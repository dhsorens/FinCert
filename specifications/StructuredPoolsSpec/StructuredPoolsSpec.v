(* an abstract structured pools contract *)

From PhD.Specifications.FA2Spec Require FA2Spec.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.
From Coq Require Import Lia.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(* =============================================================================
 * Defintions:
      We begin with some type and auxiliary definitions which we use for the 
      contract specification.
 * ============================================================================= *)

Section Definitions.
Context {Base : ChainBase}.

(* ConCert specific types *)
Definition error : Type := N.

    Section ErrorCodes. 

    Definition error_PERMISSIONS_DENIED : error := 1.
    Definition error_CONTRACT_NOT_FOUND : error := 2.
    Definition error_TOKEN_NOT_FOUND : error := 3.
    Definition error_INSUFFICIENT_BALANCE : error := 4.
    Definition error_CALL_VIEW_FAILED : error := 5.
    Definition error_FAILED_ASSERTION : error := 6.
    Definition error_FAILED_DIVISION : error := 7.
    Definition error_FAILED_TO_INITIALIZE : error := 8.

    End ErrorCodes.

Definition token : Type := FA2Spec.token. (* token_address and token_id fields *)
Definition exchange_rate := N. (* always divided by 1_000_000n in the code  *)

Definition token_eq_dec (t1 t2 : token) : { t1 = t2 } + { t1 <> t2 }.
Proof.
    decide equality.
    - apply N.eq_dec.
    - apply address_eqdec.
Defined.

Definition transfer_to := FA2Spec.transfer_to.
Definition transfer_data := FA2Spec.transfer_data.

Definition mint_data := FA2Spec.mint_data.
Definition mint := FA2Spec.mint.

Record pool_data := {
    token_pooled : token ;
    qty_pooled : N ; (* the qty of tokens to be pooled *)
}.

Record unpool_data := {
    token_unpooled : token ;
    qty_unpooled : N ; (* the qty of pool tokens being turned in *)
}.

Record trade_data := {
    token_in_trade : token ; 
    token_out_trade : token ; 
    qty_trade : N ; (* the qty of token_in going in *)
}.

Inductive entrypoint := 
(* pooling and trading *)
| pool : pool_data -> entrypoint 
| unpool : unpool_data -> entrypoint 
| trade : trade_data -> entrypoint.

Definition calc_delta_y (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N) : N := 
    (* calculate ell *)
    let l := N.sqrt (k * (1_000_000 * 1_000_000) / (rate_in * rate_out)) in 
    (* calculate the exchange rate *)
    l * rate_in / 1_000_000 - k / ((l * rate_out) / 1_000_000 + qty_trade).

Definition calc_rate_in (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N) : N :=
    let delta_y := calc_delta_y rate_in rate_out qty_trade k x in 
    (rate_in * x / 1_000_000 + rate_out * delta_y / 1_000_000) / (x + qty_trade).

(* a function to get a balance from an FMap *)
Definition get_bal (t : token) (tokens_held : FMap token N) := 
    match FMap.find t tokens_held with | Some b => b | None => 0 end.

(* the same function, but named differently for the sake of clarity *)
Definition get_rate (t : token) (rates : FMap token N) : N :=
    match FMap.find t rates with | Some r => r | None => 0 end.

End Definitions.


(* the abstract specification *)
Section AbstractSpecification.
Context {Base : ChainBase}

(* =============================================================================
 * The Contract Specification `is_structured_pool` :
      We detail a list of propositions of a contract's behavior which can be 
      proven true of a given contract.
 * ============================================================================= *)

    { Setup State Error : Type }
    `{Serializable Setup}  `{Serializable State} `{Serializable Error}.

Definition Msg : Type := entrypoint.
Context `{Serializable Msg}.


(* Specification of the Msg type:
  - A Pool entrypoint, whose interface is defined by the pool_data type
  - An Unpool entrypoint, whose interface is defined by the unpool_data type
  - A Trade entrypoint, whose interface is defined by the trade_data type

Class Msg_Spec (T : Type) := 
  build_msg_spec {
    pool : pool_data -> T ;
    unpool : unpool_data -> T ;
    trade : trade_data -> T ;
}.*)

(* specification of the State type:
  - keeps track of:
    - the exchange rates
    - tokens held
    - pool token address
    - number of outstanding pool tokens
*)
Class State_Spec (T : Type) := 
  build_state_spec {
    stor_rates : T -> FMap token exchange_rate ;
    stor_tokens_held : T -> FMap token N ;
    stor_pool_token : T -> token ; 
    stor_outstanding_tokens : T -> N ;
}.

(* specification of the Setup type 
  to initialize the contract, we need:
    - the initial rates
    - the pool token
*)
Class Setup_Spec (T : Type) := 
  build_setup_spec {
    init_rates : T -> FMap token exchange_rate ;
    init_pool_token : T -> token ; 
}.

(* specification of the Error type *)
Class Error_Spec (T : Type) := 
  build_error_type {
    error_to_Error : error -> T ;
}.

(* we assume that our contract types satisfy the type specifications *)
Context `{Msg_Spec Msg}  `{Setup_Spec Setup}  `{State_Spec State} `{Error_Spec Error}.

(* First, we assume that all successful calls require a message *)
Definition none_fails (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx,
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    exists err : Error, 
    receive contract chain ctx cstate None = Err err.

(* Specification of the POOL entrypoint *)
(* When the POOL entrypoint is called, the contract call fails if 
    the token to be pooled is not in the family of semi-fungible tokens. *)
Definition pool_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* forall calls to the Pool entrypoint *)
    msg = pool (msg_payload) -> 
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    FMap.find msg_payload.(token_pooled) (stor_rates cstate) = None -> 
    receive contract chain ctx cstate (Some msg) = 
      Err(error_to_Error error_TOKEN_NOT_FOUND).


Definition pool_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate cstate' chain ctx msg msg_payload acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* forall calls to the Pool entrypoint *)
    msg = pool (msg_payload) -> 
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    exists r_x, 
    FMap.find msg_payload.(token_pooled) (stor_rates cstate) = Some r_x.


(* When the POOL entrypoint is successfully called, it emits a TRANSFER call to the 
    token in storage, with q tokens in the payload of the call *)
Definition pool_emits_transfer (contract : Contract Setup Msg State Error) : Prop := 
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to POOL was successful *)
    msg = pool (msg_payload) -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the acts list there is a transfer call with q tokens as the payload *)
    exists transfer_to transfer_data transfer_payload,
    (* there is a transfer call *)
    In 
    (act_call 
        (msg_payload.(token_pooled).(FA2Spec.token_address)) (* call to the token address *)
        0 (* with amount = 0 *)
        (serialize (FA2Spec.Transfer transfer_payload)))
    acts /\ 
    (* with a transfer in it *)
    In transfer_data transfer_payload /\ 
    (* which itself has transfer data *)
    In transfer_to transfer_data.(FA2Spec.txs) /\
    (* whose quantity is the quantity pooled *)
    transfer_to.(FA2Spec.amount) = msg_payload.(qty_pooled).


(* When the POOL entrypoint is successfully called, it emits a MINT call to the 
    pool_token, with q * r_x / 1_000_000 in the payload *)
Definition pool_emits_mint (contract : Contract Setup Msg State Error) : Prop := 
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to POOL was successful *)
    msg = pool msg_payload -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the acts list there is a MINT call with q * r_x / 1_000_000 in the payload *)
    exists mint_data mint_payload,
    (* there is a mint call in acts *)
    In 
    (act_call
        (stor_pool_token cstate).(FA2Spec.token_address) (* calls the pool token address *)
        0 (* with amount 0 *)
        (serialize (FA2Spec.Mint mint_payload)))
    acts /\ 
    (* with has mint_data in the payload *)
    In mint_data mint_payload /\
    (* and the mint data has these properties: *)
    let r_x := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    mint_data.(FA2Spec.qty) = msg_payload.(qty_pooled) * r_x / 1_000_000 /\
    (* TODO perhaps also specify that the minted tokens go to pooler *)
    mint_data.(FA2Spec.mint_owner) = ctx.(ctx_from).

(* When the POOL entrypoint is successfully called, the TRANSFER and MINT transactions
    are the only transactions emitted by the contract *)
Definition pool_atomic (contract : Contract Setup Msg State Error) : Prop := 
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts, 
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to POOL was successful *)
    msg = pool msg_payload -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* we have a MINT call in acts and a TRANSFER call *)
    length acts = 2%nat.


(* When the POOL entrypoint is successfully called, tokens_held goes up appropriately *)
Definition pool_increases_tokens_held (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let token := msg_payload.(token_pooled) in
    let qty := msg_payload.(qty_pooled) in
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := get_bal token (stor_tokens_held cstate') in 
    new_bal = old_bal + qty.


Definition pool_rates_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

Definition pool_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    let rate_in := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    let qty := msg_payload.(qty_pooled) in 
    stor_outstanding_tokens cstate' = 
    stor_outstanding_tokens cstate + rate_in / 1000000 * qty.

(* Specification of the UNPOOL entrypoint *)
(* When the UNPOOL entrypoint is called, the contract call fails if 
    the token to be pooled is not in the family of semi-fungible tokens. *)
Definition unpool_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* forall calls to the Pool entrypoint *)
    msg = unpool (msg_payload) -> 
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    FMap.find msg_payload.(token_unpooled) (stor_rates cstate) = None -> 
    receive contract chain ctx cstate (Some msg) = 
      Err(error_to_Error error_TOKEN_NOT_FOUND).


Definition unpool_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate cstate' chain ctx msg msg_payload acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* forall calls to the Pool entrypoint *)
    msg = unpool (msg_payload) -> 
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    exists r_x,
    FMap.find msg_payload.(token_unpooled) (stor_rates cstate) = Some r_x.


(* When the UNPOOL entrypoint is successfully called, it emits a BURN call to the 
    pool_token, with q in the payload *)
Definition unpool_emits_burn (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to UNPOOL was successful *)
    msg = unpool msg_payload -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the acts list there is a BURN call with q in the payload *)
    exists burn_data burn_payload,
    (* there is a mint call in acts *)
    In 
    (act_call
        (stor_pool_token cstate).(FA2Spec.token_address) (* calls the pool token address *)
        0 (* with amount 0 *)
        (serialize (FA2Spec.Retire burn_payload)))
    acts /\ 
    (* with has burn_data in the payload *)
    In burn_data burn_payload /\
    (* and burn_data has these properties: *)
    burn_data.(FA2Spec.retire_amount) = msg_payload.(qty_unpooled) /\
    (* the burned tokens go from the unpooler *)
    burn_data.(FA2Spec.retiring_party) = ctx.(ctx_from).


(* When the UNPOOL entrypoint is successfully called, it emits a TRANSFER call to the 
    token in storage, with q * 1_000_000 / r_x tokens in the payload of the call *)
Definition unpool_emits_transfer (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to UNPOOL was successful *)
    msg = unpool (msg_payload) -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the acts list there is a transfer call with q tokens as the payload *)
    exists transfer_to transfer_data transfer_payload,
    (* there is a transfer call *)
    In 
    (act_call 
        (msg_payload.(token_unpooled).(FA2Spec.token_address)) (* call to the token address *)
        0 (* with amount = 0 *)
        (serialize (FA2Spec.Transfer transfer_payload)))
    acts /\ 
    (* with a transfer in it *)
    In transfer_data transfer_payload /\ 
    (* which itself has transfer data *)
    In transfer_to transfer_data.(FA2Spec.txs) /\
    (* whose quantity is the quantity pooled *)
    let r_x := get_rate msg_payload.(token_unpooled) (stor_rates cstate) in 
    transfer_to.(FA2Spec.amount) = msg_payload.(qty_unpooled) * 1_000_000 / r_x.


(* When the UNPOOL entrypoint is successfully called, tokens_held goes down appropriately *)
Definition unpool_decreases_tokens_held (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let token := msg_payload.(token_unpooled) in
    let qty := msg_payload.(qty_unpooled) in
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := get_bal token (stor_tokens_held cstate') in 
    new_bal = old_bal - qty.

(* When the UNPOOL entrypoint is successfully called, tokens_held goes down appropriately *)
Definition unpool_rates_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

Definition unpool_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    let rate_in := get_rate msg_payload.(token_unpooled) (stor_rates cstate) in 
    let qty := msg_payload.(qty_unpooled) in 
    stor_outstanding_tokens cstate' = 
    stor_outstanding_tokens cstate - 1000000 / rate_in * qty.

(* If the TRADE entrypoint is called, token_in_trade and token_out_trade must both be 
    part of the semi-fungible family for the trade to succeed. *)
Definition trade_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* forall calls to the Pool entrypoint *)
    msg = trade (msg_payload) -> 
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    ((FMap.find msg_payload.(token_in_trade) (stor_rates cstate) = None) \/
    (FMap.find msg_payload.(token_out_trade) (stor_rates cstate) = None)) ->
    receive contract chain ctx cstate (Some msg) = 
      Err(error_to_Error error_TOKEN_NOT_FOUND).


Definition trade_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    exists x r_x r_y,
    ((FMap.find msg_payload.(token_in_trade) (stor_tokens_held cstate) = Some x) /\
    (FMap.find msg_payload.(token_in_trade) (stor_rates cstate) = Some r_x) /\
    (FMap.find msg_payload.(token_out_trade) (stor_rates cstate) = Some r_y)).


(* Specification of the TRADE entrypoint *)
(* When TRADE is successfully called, the trade is priced using the correct formula 
    given by calculate_trade. The updated rate is also priced using the formula from
    calculate_trade. *)
Definition trade_pricing_formula (contract : Contract Setup Msg State Error) : Prop := 
    forall bstate caddr cstate chain ctx msg msg_payload t_x t_y q cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the TRADE entrypoint was called succesfully *)
    msg = trade msg_payload -> 
    t_x = msg_payload.(token_in_trade) -> 
    t_y = msg_payload.(token_out_trade) -> 
    t_x <> t_y -> 
    q = msg_payload.(qty_trade) ->
    receive contract chain ctx cstate (Some msg) = 
      Ok(cstate', acts) -> 
    (* calculate the diffs delta_x and delta_y *)
    let delta_x := 
        (get_bal t_x (stor_tokens_held cstate')) - (get_bal t_x (stor_tokens_held cstate)) in 
    let delta_y := 
        (get_bal t_y (stor_tokens_held cstate)) - (get_bal t_y (stor_tokens_held cstate')) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    (* the diff delta_x and delta_y are correct *)
    delta_x = q /\
    delta_y = calc_delta_y rate_in rate_out q k x.


Definition trade_update_rates_formula (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the TRADE entrypoint was called succesfully *)
    receive contract chain ctx cstate (Some (trade msg_payload)) = 
      Ok(cstate', acts) -> 
    let t_x := msg_payload.(token_in_trade) in
    let t_y := msg_payload.(token_out_trade) in
    t_x <> t_y /\
    (* calculate the diffs delta_x and delta_y *)
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let q := msg_payload.(qty_trade) in
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    (* the new rate of t_x is correct *)
    let r_x' := calc_rate_in rate_in rate_out q k x in 
    FMap.find t_x (stor_rates cstate') = Some r_x' /\ 
    (forall t, t <> t_x -> 
        FMap.find t (stor_rates cstate') = 
        FMap.find t (stor_rates cstate)).


(* When TRADE is successfully called, it emits a TRANSFER action of t_x in quantity q *)
Definition trade_emits_transfer_tx (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate cstate' chain ctx msg msg_payload acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to TRADE was successful *)
    msg = trade (msg_payload) -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the acts list there is a transfer call with q tokens as the payload *)
    exists transfer_to transfer_data transfer_payload,
    (* there is a transfer call *)
    In 
    (act_call 
        (msg_payload.(token_in_trade).(FA2Spec.token_address)) (* call to the correct token address *)
        0 (* with amount = 0 *)
        (serialize (FA2Spec.Transfer transfer_payload)))
    acts /\ 
    (* with a transfer in it *)
    In transfer_data transfer_payload /\ 
    (* which itself has transfer data *)
    In transfer_to transfer_data.(FA2Spec.txs) /\
    (* whose quantity is the quantity traded, transferred to the contract *)
    transfer_to.(FA2Spec.amount) = msg_payload.(qty_trade) /\
    transfer_to.(FA2Spec.to_) = ctx.(ctx_contract_address).


(* transfers with delta_y given by calculate_trade function *)
Definition trade_emits_transfer_ty (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to TRADE was successful *)
    msg = trade (msg_payload) -> 
    receive contract chain ctx cstate (Some msg) = 
      Ok(cstate', acts) -> 
    (* in the acts list there is a transfer call with q tokens as the payload *)
    exists transfer_to transfer_data transfer_payload,
    (* there is a transfer call *)
    In 
    (act_call 
        (msg_payload.(token_out_trade).(FA2Spec.token_address)) (* call to the correct token address *)
        0 (* with amount = 0 *)
        (serialize (FA2Spec.Transfer transfer_payload)))
    acts /\ 
    (* with a transfer in it *)
    In transfer_data transfer_payload /\ 
    (* which itself has transfer data *)
    In transfer_to transfer_data.(FA2Spec.txs) /\
    (* whose quantity is the quantity traded, transferred to the contract *)
    let t_x := msg_payload.(token_in_trade) in 
    let t_y := msg_payload.(token_out_trade) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let q := msg_payload.(qty_trade) in 
    transfer_to.(FA2Spec.amount) = calc_delta_y rate_in rate_out q k x  /\
    transfer_to.(FA2Spec.to_) = ctx.(ctx_from).

Definition trade_tokens_held_update (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to TRADE was successful *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* in the new state *)
    let t_x := msg_payload.(token_in_trade) in 
    let t_y := msg_payload.(token_out_trade) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let delta_x := msg_payload.(qty_trade) in 
    let delta_y := calc_delta_y rate_in rate_out delta_x k x in 
    let prev_bal_y := get_bal t_y (stor_tokens_held cstate) in 
    let prev_bal_x := get_bal t_x (stor_tokens_held cstate) in 
    get_bal t_y (stor_tokens_held cstate') = (prev_bal_y - delta_y) /\
    get_bal t_x (stor_tokens_held cstate') = (prev_bal_x + delta_x) /\
    forall t_z, 
        t_z <> t_x -> 
        t_z <> t_y -> 
        get_bal t_z (stor_tokens_held cstate') = 
        get_bal t_z (stor_tokens_held cstate).

Definition trade_outstanding_update (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to TRADE was successful *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* in the new state *)
    let t_x := msg_payload.(token_in_trade) in 
    let t_y := msg_payload.(token_out_trade) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let delta_x := msg_payload.(qty_trade) in 
    let delta_y := calc_delta_y rate_in rate_out delta_x k x in 
    (stor_outstanding_tokens cstate') = 
    (stor_outstanding_tokens cstate) + delta_x - delta_y.

Definition trade_in_deposit (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to TRADE was successful *)
    msg = trade (msg_payload) -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the new state *)
    (* TODO COVER THE CASE THAT t_in = t_out *)
    FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate') =
    Some (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate) + (qty_trade msg_payload)).

(*
Definition stor_outstanding_tokens (contract : Contract Setup Msg State Error) : Prop :=
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to TRADE was successful *)
    msg = trade (msg_payload) -> 
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in the new state *)
    (stor_outstanding_tokens cstate') = 
    (stor_outstanding_tokens cstate) - 
*)

(* 
    (!!!) TODO A SAFETY PROPERTY THAT THE OUTSTANDING TOKENS IS ALWAYS CORRECT
    (!!!) TODO A SAFETY PROPERTY FOR ALL STORAGE BITS!
*)

(* Initialization specification *)
Definition initialized_with_nonzero_rates (contract : Contract Setup Msg State Error) : Prop := 
    forall chain ctx setup cstate,
    (* we call init successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then all rates are nonzero *)
    forall t r,
    FMap.find t (stor_rates cstate) = Some r -> 
    r > 0.

Definition initialized_with_zero_balance (contract : Contract Setup Msg State Error) : Prop := 
    forall chain ctx setup cstate,
    (* we call init successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then all rates are nonzero *)
    forall t,
    get_bal t (stor_tokens_held cstate) = 0.

Definition initialized_with_zero_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall chain ctx setup cstate,
    (* we call init successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then all rates are nonzero *)
    stor_outstanding_tokens cstate = 0.

(* we amalgamate each proposition in the specification into a single proposition *)
Definition is_structured_pool
    (C : Contract Setup Msg State Error) : Prop := 
    none_fails C /\
    pool_entrypoint_check C /\
    pool_entrypoint_check_2 C /\
    pool_emits_transfer C /\
    pool_emits_mint C /\
    pool_atomic C /\
    pool_increases_tokens_held C /\
    pool_rates_unchanged C /\
    pool_outstanding C /\
    unpool_entrypoint_check C /\
    unpool_entrypoint_check_2 C /\
    unpool_emits_burn C /\
    unpool_emits_transfer C /\
    unpool_decreases_tokens_held C /\
    unpool_rates_unchanged C /\
    unpool_outstanding C /\
    trade_entrypoint_check C /\
    trade_entrypoint_check_2 C /\
    trade_pricing_formula C /\
    trade_update_rates_formula C /\
    trade_emits_transfer_tx C /\
    trade_emits_transfer_ty C /\
    trade_tokens_held_update C /\
    trade_outstanding_update C /\
    trade_in_deposit C /\
    initialized_with_nonzero_rates C /\
    initialized_with_zero_balance C /\
    initialized_with_zero_outstanding C.

(* A tactic to destruct is_sp if it's in the context of a proof *)
Tactic Notation "is_sp_destruct" := 
    match goal with 
    | is_sp : is_structured_pool _ |- _ => 
        unfold is_structured_pool in is_sp;
        destruct is_sp  as [none_fails_pf is_sp'];
        destruct is_sp'  as [pool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [pool_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [pool_emits_transfer_pf is_sp'];
        destruct is_sp' as [pool_emits_mint_pf is_sp'];
        destruct is_sp' as [pool_atomic_pf is_sp'];
        destruct is_sp' as [pool_increases_tokens_held_pf is_sp'];
        destruct is_sp' as [pool_rates_unchanged_pf is_sp'];
        destruct is_sp' as [pool_outstanding_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [unpool_emits_burn_pf is_sp'];
        destruct is_sp' as [unpool_emits_transfer_pf is_sp'];
        destruct is_sp' as [unpool_decreases_tokens_held_pf is_sp'];
        destruct is_sp' as [unpool_rates_unchanged_pf is_sp'];
        destruct is_sp' as [unpool_outstanding_pf is_sp'];
        destruct is_sp' as [trade_entrypoint_check_pf is_sp'];
        destruct is_sp' as [trade_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [trade_pricing_formula_pf is_sp'];
        destruct is_sp' as [trade_update_rates_formula_pf is_sp'];
        destruct is_sp' as [trade_emits_transfer_tx_pf is_sp'];
        destruct is_sp' as [trade_emits_transfer_ty_pf is_sp'];
        destruct is_sp' as [trade_tokens_held_update_pf is_sp']; 
        destruct is_sp' as [trade_outstanding_update_pf is_sp'];
        destruct is_sp' as [trade_in_deposit_pf is_sp'];
        destruct is_sp' as [initialized_with_nonzero_rates_pf is_sp']; 
        destruct is_sp' as [initialized_with_zero_balance_pf initialized_with_zero_outstanding_pf]
end.


(* =============================================================================
 * The contract Metaspecification:
      We reason about a contract which satisfies the properties of the specification 
      given here, showing that a contract which satisfies the specification also satisfies
      the properties here.
 * ============================================================================= *)

Context {contract : Contract Setup Msg State Error}
        { is_sp : is_structured_pool contract }
        (* some common assumptions in the metaspecification *)
        { bstate : ChainState } { caddr : Address } { cstate : State }
        (* reachable state *)
        { reachable_st : reachable bstate } { trace : ChainTrace empty_state bstate}
        (* with contract at caddr *)
        { contract_at_caddr : env_contracts bstate caddr = Some (contract : WeakContract) }
        (* with contract state cstate *)
        { state_is_cstate : contract_state bstate caddr = Some cstate }.

(* Some assumptions (should probably prove some of these) *)
(* update_rate function returns positive number  *)
Axiom update_rate_returns_positive : forall r_x r_y delta_x k x, 
    let r_x' := calc_rate_in r_x r_y delta_x k x in
    let delta_y := calc_delta_y r_x r_y delta_x k x in  
    (r_x * x / 1_000_000 + r_y * delta_y / 1_000_000) > 0 -> 
    (x + delta_x) > 0 -> 
    r_x' > 0.

Axiom update_rate_stays_positive : forall r_x r_y delta_x k x, 
    let r_x' := calc_rate_in r_x r_y delta_x k x in
    r_x > 0 ->
    r_x' > 0.

(* calculate_trade function returns a positive number if k, r_x, r_y, delta_x > 0 *)
Axiom calc_trade_returns_positive : forall r_x r_y delta_x k x, 
    k > 0 -> 
    r_x > 0 -> 
    r_y > 0 -> 
    delta_x > 0 -> 
    calc_delta_y r_x r_y delta_x k x > 0.

(* r_x' < r_x *)
Axiom rate_decrease : forall r_x r_y delta_x k x, 
    let r_x' := calc_rate_in r_x r_y delta_x k x in 
    r_x' < r_x.

(* delta_y < ( r_y / r_x ) * delta_x *)
Axiom trade_upper_bound : forall r_x r_y delta_x k x, 
    let delta_y := calc_delta_y r_x r_y delta_x k x in 
    delta_y < ( r_y / r_x ) * delta_x.

(* just simplified from ^^ *)
Axiom trade_upper_bound_2 : forall r_x r_y delta_x k x, 
    let delta_y := calc_delta_y r_x r_y delta_x k x in 
    r_x * delta_y < r_y * delta_x.

(* Demand Sensitivity :
    A trade for a given token increases its price relative to other constituent tokens, 
    so that higher relative demand corresponds to a higher relative price. 
    Likewise, trading one token in for another decreases the first's relative price in 
    the pool, corresponding to slackened demand. This enforces the classical notion of 
    supply and demand 

    We prove that r_x' > r_x and forall t_z, r_z' = r_z.
*)

(* x decreases relative to z as x => x', z => z' :
    z - x < z' - x' *)
Definition rel_decr (x z x' z' : N) := 
    ((Z.of_N z) - (Z.of_N x) < (Z.of_N z') - (Z.of_N x'))%Z.

Lemma rel_decr_lem : forall x x' z : N, 
    x' < x -> 
    rel_decr x z x' z.
Proof.
    intros * x_leq.
    unfold rel_decr.
    (* z - x < z - x' <-> -x < -x' *)
    rewrite <- (Z.add_opp_r (Z.of_N z) (Z.of_N x)).
    rewrite <- (Z.add_opp_r (Z.of_N z) (Z.of_N x')).
    rewrite (Z.add_comm (Z.of_N z) (- Z.of_N x)).
    rewrite (Z.add_comm (Z.of_N z) (- Z.of_N x')).
    apply (Z.add_lt_mono_r (- Z.of_N x) (- Z.of_N x') (Z.of_N z)).
    (* <-> x' < x, as desired *)
    apply (Z.opp_lt_mono (Z.of_N x') (Z.of_N x)).
    apply (N2Z.inj_lt x' x) in x_leq.
    exact x_leq.
Qed.

(* y increases relative to x as y => y', x => x' : 
    y - x < y' - x' *)
Definition rel_incr (y x y' x' : N) := 
    ((Z.of_N y) - (Z.of_N x) < (Z.of_N y') - (Z.of_N x'))%Z.

Lemma rel_incr_lem : forall x x' y : N, 
    x' < x -> 
    rel_incr y x y x'.
Proof.
    intros * x_leq.
    unfold rel_incr.
    (* y - x < y - x' <-> -x < -x' *)
    rewrite <- (Z.add_opp_r (Z.of_N y) (Z.of_N x)).
    rewrite <- (Z.add_opp_r (Z.of_N y) (Z.of_N x')).
    rewrite (Z.add_comm (Z.of_N y) (- Z.of_N x)).
    rewrite (Z.add_comm (Z.of_N y) (- Z.of_N x')).
    apply (Z.add_lt_mono_r (- Z.of_N x) (- Z.of_N x') (Z.of_N y)).
    (* <-> x' < x, as desired *)
    apply (Z.opp_lt_mono (Z.of_N x') (Z.of_N x)).
    apply (N2Z.inj_lt x' x) in x_leq.
    exact x_leq.
Qed.

Theorem demand_sensitivity :
    (* For all tokens t_x t_y, rates r_x r_y, and quantities x and y, where *)
    forall t_x r_x x t_y r_y y,
    (* t_x is a token with nonzero pooled liquidity and with rate r_x > 0, and *)
    FMap.find t_x (stor_tokens_held cstate) = Some x /\ x > 0 /\
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 ->
    (* t_y is a token with nonzero pooled liquidity and with rate r_y > 0 *)
    FMap.find t_y (stor_tokens_held cstate) = Some y /\ y > 0 /\
    FMap.find t_y (stor_rates cstate) = Some r_y /\ r_y > 0 ->
    (* In a trade t_x to t_y ... *)
    forall chain ctx msg msg_payload acts cstate',
        (* i.e.: a successful call to the contract *)
        receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) ->
        (* which is a trade *)
        msg = trade msg_payload ->
        (* from t_x to t_y *)
        msg_payload.(token_in_trade) = t_x ->
        msg_payload.(token_out_trade) = t_y ->
        (* with t_x <> t_y *)
        t_x <> t_y -> 
    (* ... as r_x is updated to r_x': ... *)
    let r_x' := get_rate t_x (stor_rates cstate') in 
    (* (1) r_x decreases relative to all rates r_z, for t_z <> t_x, and *)
    (forall t_z, 
        t_z <> t_x -> 
        let r_z  := get_rate t_z (stor_rates cstate) in 
        let r_z' := get_rate t_z (stor_rates cstate') in 
        rel_decr r_x r_z r_x' r_z') /\
    (* (2) r_y strictly increases relative to r_x *)
    let t_y := msg_payload.(token_out_trade) in 
    let r_y  := get_rate t_y (stor_rates cstate) in 
    let r_y' := get_rate t_y (stor_rates cstate') in 
    rel_incr r_y r_x r_y' r_x'.
Proof.
    intros ? ? ? ? ? ? t_x_data t_y_data ? ? ? ? ? ? successful_txn msg_is_trade 
        token_in_tx token_out_ty tx_neq_ty r_x'.
    destruct t_x_data as [stor_tx t_x_data].
    destruct t_x_data as [x_geq0 t_x_data].
    destruct t_x_data as [rate_rx rx_geq_0].
    (* first, prove that r_x' < r_x while r_z = r_z' for all other rates *)
    assert (r_x' < r_x /\
        forall t,
        t <> t_x ->
        get_rate t (stor_rates cstate') = get_rate t (stor_rates cstate))
    as change_lemma.
    {   intros.
        is_sp_destruct.
        rewrite msg_is_trade in successful_txn.
        pose proof (trade_entrypoint_check_2_pf cstate chain ctx msg_payload
                cstate' acts successful_txn)
        as token_in_qty.
        do 3 destruct token_in_qty as [* token_in_qty].
        destruct token_in_qty as [token_in_qty rates_exist].
        destruct rates_exist as [rate_in_exists rate_out_exists].
        (* get the new rates *)  
        rewrite <- token_out_ty in tx_neq_ty.
        rewrite <- msg_is_trade in successful_txn.
        rewrite msg_is_trade in successful_txn.
        pose proof (trade_update_rates_formula_pf cstate chain ctx msg_payload cstate' acts successful_txn) as updating_rates. 
        destruct updating_rates as [_ updating_rates].
        destruct updating_rates as [calc_new_rate_x other_rates_equal].
        (* split into cases *)
        split.
        -   unfold r_x'. unfold get_rate.
            rewrite token_in_tx in calc_new_rate_x.
            replace (FMap.find t_x (stor_rates cstate')) 
            with (Some
                (calc_rate_in 
                    (get_rate t_x (stor_rates cstate))
                    (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                    (qty_trade msg_payload)
                    (stor_outstanding_tokens cstate) 
                    (get_bal t_x (stor_tokens_held cstate)))).
            assert (r_x = (get_rate t_x (stor_rates cstate))) as r_x_is_r_x.
            +   unfold get_rate. 
                replace (FMap.find t_x (stor_rates cstate)) 
                with (Some r_x).
                reflexivity.
            +   rewrite r_x_is_r_x.
                exact (rate_decrease 
                    (get_rate t_x (stor_rates cstate)) 
                    (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                    (qty_trade msg_payload)
                    (stor_outstanding_tokens cstate) 
                    (get_bal t_x (stor_tokens_held cstate))).
        -   intros t t_neq_tx. 
            unfold get_rate.
            replace (FMap.find t (stor_rates cstate')) with (FMap.find t (stor_rates cstate)).
            2:{ rewrite <- token_in_tx in t_neq_tx.
                exact (eq_sym (other_rates_equal t t_neq_tx)). }
            auto. }
    (* now use change_lemma to prove the result *)
    destruct change_lemma as [rx_change tz_change].
    split.
    (* prove: r_x decreases relative to all rates r_z, for t_z <> t_x *)
    -   intros t_z z_neq_x. 
        pose proof (tz_change t_z z_neq_x) as tz_change'. 
        clear tz_change.
        rewrite tz_change'.
        apply rel_decr_lem.
        exact rx_change.
    (* prove: r_y strictly increases relative to r_x *)
    -   unfold rel_incr.
        rewrite <- token_out_ty in tx_neq_ty.
        pose proof (tz_change (token_out_trade msg_payload) (not_eq_sym tx_neq_ty)) as tz_change'.
        clear tz_change.
        rewrite tz_change'.
        apply rel_incr_lem.
        exact rx_change.
Qed.

(* Nonpathological prices 
    As relative prices shift over time, a price that starts out nonzero never goes to 
    zero or to a negative value. 

    This is to avoid pathological behavior of zero or negative prices. 

    Note, however, that prices can still get arbitrarily close to zero, like in the case 
    of CPMMs.
*)

Theorem nonpathological_prices : 
    exists (cstate : State),
    contract_state bstate caddr = Some cstate /\
    (* For a token t_x in T and rate r_x, *)
    forall t_x r_x,
    (* such that in the contract state cstate the rate of t_x is r_x and r_x > 0, *)
    FMap.find t_x (stor_rates cstate) = Some r_x -> r_x > 0.
Proof.
    contract_induction; intros.
    (* Please reestablish the invariant after addition of a block *)
    -   exact (IH t_x r_x H6).
    (* Please establish the invariant after deployment of the contract *)
    -   is_sp_destruct. clear is_sp.
        pose proof (initialized_with_nonzero_rates_pf chain ctx setup result init_some) as init_rates.
        exact (init_rates t_x r_x H6).
    (* Please reestablish the invariant after an outgoing action *)
    -   exact (IH t_x r_x H6).
    (* Please reestablish the invariant after a nonrecursive call *)
    -   destruct msg.
        (* msg = Some m *)
        +   destruct m.
            (* m = pool p : by the specification, pooling does not change exchange rates *)
            *   is_sp_destruct. clear is_sp.
                pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts receive_some t_x).
                replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H6.
                exact (IH t_x r_x H6).
            (* m = unpool p : by the specification, pooling does not change exchange rates *)
            *   is_sp_destruct. clear is_sp.
                pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts receive_some t_x).
                replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H6.
                exact (IH t_x r_x H6).
            (* m = trade p *)
            *   is_sp_destruct. clear is_sp.
                (* We split into cases (token_in_trade t) = t_x and (token_in_trade t) <> t_x *)
                destruct (token_eq_dec (token_in_trade t) t_x).
                (* first we treat unequality, which is the simpler case *)
                2:{ (* first use the spec to prove that the updated r_x is equal to the old r_x *)
                    pose proof (trade_update_rates_formula_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as rx_update.
                    simpl in rx_update.
                    destruct rx_update as [_ rates_update].
                    simpl in rates_update.
                    destruct rates_update as [_ tz_update].
                    pose proof (tz_update t_x (not_eq_sym n)).
                    replace (FMap.find t_x (stor_rates new_state)) 
                    with (FMap.find t_x (stor_rates prev_state))
                    in H6.
                    (* by induction ... *)
                    exact (IH t_x r_x H6). }
                (* now we have (token_in_trade t) = t_x *)
                (* we need to get r_x from prev_state *)
                assert (exists prev_rx, FMap.find t_x (stor_rates prev_state) = Some prev_rx)
                as exists_prevrx.
                {   pose proof (trade_entrypoint_check_2_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as prev_rate_lem.
                    do 3 destruct prev_rate_lem as [* prev_rate_lem].
                    destruct prev_rate_lem as [_ prev_rate_lem].
                    destruct prev_rate_lem as [in_lem _].
                    rewrite e in in_lem.
                    exists x0.
                    exact in_lem. }
                destruct exists_prevrx as [prev_rx *].
                (* by IH prev_rx is positive *)
                pose proof (IH t_x prev_rx H7) as prev_pos.
                (* assert that there is some rate r_y of the  *)
                assert (exists r_y, r_x = calc_rate_in prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as rx_update.
                {   pose proof (trade_update_rates_formula_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as rx_update.
                    destruct rx_update as [_ rates_update].
                    simpl in rates_update.
                    destruct rates_update as [tx_update _].
                    rewrite <- e in *.
                    rewrite H6 in tx_update.
                    inversion tx_update.
                    exists (get_rate (token_out_trade t) (stor_rates prev_state)).
                    f_equal.
                    unfold get_rate.
                    replace (FMap.find (token_in_trade t) (stor_rates prev_state))
                    with (Some prev_rx).
                    auto. }
                destruct rx_update as [r_y rx_update].
                (* we call on the result prev_rx > 0 => r_x > 0 *)
                pose proof (update_rate_stays_positive prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as pos_new_rate.
                rewrite <- rx_update in pos_new_rate.
                cbn in pos_new_rate.
                exact (pos_new_rate prev_pos).
        (* msg = None *)
        +   is_sp_destruct. clear is_sp.
            pose proof (none_fails_pf prev_state chain ctx) as none_fail.
            destruct none_fail as [err none_fail].
            rewrite none_fail in receive_some.
            inversion receive_some.
    (* Please reestablish the invariant after a recursive call *)
    -   destruct msg.
        (* msg = Some m *)
        +   destruct m.
            (* m = pool p : by the specification, pooling does not change exchange rates *)
            *   is_sp_destruct. clear is_sp.
                pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts receive_some t_x).
                replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H6.
                exact (IH t_x r_x H6).
            (* m = unpool p : by the specification, pooling does not change exchange rates *)
            *   is_sp_destruct. clear is_sp.
                pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts receive_some t_x).
                replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H6.
                exact (IH t_x r_x H6).
            (* m = trade p *)
            *   is_sp_destruct. clear is_sp.
                (* We split into cases (token_in_trade t) = t_x and (token_in_trade t) <> t_x *)
                destruct (token_eq_dec (token_in_trade t) t_x).
                (* first we treat unequality, which is the simpler case *)
                2:{ (* first use the spec to prove that the updated r_x is equal to the old r_x *)
                    pose proof (trade_update_rates_formula_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as rx_update.
                    simpl in rx_update.
                    destruct rx_update as [_ rates_update].
                    simpl in rates_update.
                    destruct rates_update as [_ tz_update].
                    pose proof (tz_update t_x (not_eq_sym n)).
                    replace (FMap.find t_x (stor_rates new_state)) 
                    with (FMap.find t_x (stor_rates prev_state))
                    in H6.
                    (* by induction ... *)
                    exact (IH t_x r_x H6). }
                (* now we have (token_in_trade t) = t_x *)
                (* we need to get r_x from prev_state *)
                assert (exists prev_rx, FMap.find t_x (stor_rates prev_state) = Some prev_rx)
                as exists_prevrx.
                {   pose proof (trade_entrypoint_check_2_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as prev_rate_lem.
                    do 3 destruct prev_rate_lem as [* prev_rate_lem].
                    destruct prev_rate_lem as [_ prev_rate_lem].
                    destruct prev_rate_lem as [in_lem _].
                    rewrite e in in_lem.
                    exists x0.
                    exact in_lem. }
                destruct exists_prevrx as [prev_rx *].
                (* by IH prev_rx is positive *)
                pose proof (IH t_x prev_rx H7) as prev_pos.
                (* assert that there is some rate r_y of the  *)
                assert (exists r_y, r_x = calc_rate_in prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as rx_update.
                {   pose proof (trade_update_rates_formula_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as rx_update.
                    destruct rx_update as [_ rates_update].
                    simpl in rates_update.
                    destruct rates_update as [tx_update _].
                    rewrite <- e in *.
                    rewrite H6 in tx_update.
                    inversion tx_update.
                    exists (get_rate (token_out_trade t) (stor_rates prev_state)).
                    f_equal.
                    unfold get_rate.
                    replace (FMap.find (token_in_trade t) (stor_rates prev_state))
                    with (Some prev_rx).
                    auto. }
                destruct rx_update as [r_y rx_update].
                (* we call on the result prev_rx > 0 => r_x > 0 *)
                pose proof (update_rate_stays_positive prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as pos_new_rate.
                rewrite <- rx_update in pos_new_rate.
                cbn in pos_new_rate.
                exact (pos_new_rate prev_pos).
        (* msg = None *)
        +   is_sp_destruct. clear is_sp.
            pose proof (none_fails_pf prev_state chain ctx) as none_fail.
            destruct none_fail as [err none_fail].
            rewrite none_fail in receive_some.
            inversion receive_some.
    (* Please reestablish the invariant after permutation of the action queue *)
    -   exact (IH t_x r_x H6).
    -   solve_facts.
Qed.

(* from paper: just need to show that r_x' < r_x always, since TRADE is the only
    entrypoint that changes r_x *)
Theorem nonpathological_prices_old : 
    (* For a token t_x in T and rate r_x, *)
    forall t_x r_x,
    (* such that in the contract state cstate the rate of t_x is r_x and r_x > 0, *)
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 -> 
    (* in any future reachable state bstate' with contract state cstate', *)
    forall bstate' (cstate' : State) r_x',
    reachable_through bstate bstate' -> 
    contract_state bstate' caddr = Some cstate' ->
    (* t_x still has an exchange rate greater than zero in the new state cstate' *)
    FMap.find t_x (stor_rates cstate') = Some r_x' /\ r_x' > 0.
Proof.
    contract_induction.
    (* Please reestablish the invariant after addition of a block *)
    -   intros. exact IH.
    (* Please establish the invariant after deployment of the contract *)
    -   intros.
        admit.
    (* Please reestablish the invariant after an outgoing action *)
    -   intros. exact IH.
    (* Please reestablish the invariant after a nonrecursive call *)
    -   intros. exact IH.
    (* Please reestablish the invariant after a recursive call *)
    -   intros. exact IH.
    (* Please reestablish the invariant after permutation of the action queue *)
    -   intros. exact IH.
    (* Please prove your facts *)
    -   intros. solve_facts.
Admitted.


(* Swap rate consistency : 
    For tokens tau_x, tau_y and tau_z, the exchange rate from tau_x to tau_y, and then to 
    tau_z, must not be greater than the exchange rate from tau_x to token tau_z. 

    As we will see, structured pools always price trades consistently, but because of how 
    prices update over time it is nontrivial to show that this is true in practice.
    
    In particular, price consistency means that it is never profitable to trade in a loop, 
    e.g. tau_x to tau_y, and back to tau_x, which is important so that there are no 
    arbitrage oportunities internal to the pool.
*)

(* first a type to describe successive trades *)
Record trade_sequence_type := build_trade_sequence_type {
    seq_chain : ChainState ; 
    seq_ctx : ContractCallContext ; 
    seq_cstate : State ; 
    seq_trade_data : trade_data ;
    seq_res_acts : list ActionBody ;
}.

(* a proposition that indicates a list of trades are successive, successful trades *)
Fixpoint are_successive_trades (trade_sequence : list trade_sequence_type) : Prop := 
    match trade_sequence with 
    | [] => True
    | [ t ] =>
        (* if the list has one element, it just has to succeed *)
        exists cstate' acts,
        receive contract 
            (seq_chain t)
            (seq_ctx t)
            (seq_cstate t) 
            (Some (trade (seq_trade_data t))) 
        = Ok(cstate', acts)
    | t1 :: t2 :: l => 
        (* the trade t1 goes through, connecting t1 and t2 *)
        receive contract 
            (seq_chain t1) 
            (seq_ctx t1) 
            (seq_cstate t1) 
            (Some (trade (seq_trade_data t1))) 
        = Ok(seq_cstate t2, seq_res_acts t2) /\ 
        (are_successive_trades l)
    end.

(* a function to calculate the the trade output of the final trade, delta_x' *)
Definition calc_final_delta (t : trade_sequence_type) := 
    let cstate := seq_cstate t in 
    let token_in := token_in_trade (seq_trade_data t) in 
    let token_out := token_out_trade (seq_trade_data t) in 
    let rate_in := get_rate token_in (stor_rates cstate) in 
    let rate_out := get_rate token_out (stor_rates cstate) in 
    let delta_x := qty_trade (seq_trade_data t) in 
    let k := stor_outstanding_tokens cstate in 
    let x := get_bal token_in (stor_tokens_held cstate) in 
    (* the calculation *)
    calc_delta_y rate_in rate_out delta_x k x.

Definition swap_rate_lemma : 
    forall t_x r_x x t_y r_y y, 
    (* t_x is a token with nonzero pooled liquidity and with rate r_x > 0, and *)
    FMap.find t_x (stor_tokens_held cstate) = Some x /\ x > 0 /\
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 ->
    (* t_y is a token with nonzero pooled liquidity and with rate r_y > 0 *)
    FMap.find t_y (stor_tokens_held cstate) = Some y /\ y > 0 /\
    FMap.find t_y (stor_rates cstate) = Some r_y /\ r_y > 0 ->
    (* In a trade t_x to t_y ... *)
    forall chain ctx msg msg_payload acts cstate',
        (* i.e.: a successful call to the contract *)
        receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) ->
        (* which is a trade *)
        msg = trade msg_payload ->
        (* from t_x to t_y *)
        msg_payload.(token_in_trade) = t_x ->
        msg_payload.(token_out_trade) = t_y ->
        (* with t_x <> t_y *)
        t_x <> t_y -> 
    (* ... as r_x is updated to r_x': ... *)
    let delta_x := msg_payload.(qty_trade) in 
    let delta_y := calc_delta_y r_x r_y delta_x (stor_outstanding_tokens cstate) x in 
    let r_x' := get_rate t_x (stor_rates cstate') in 
    r_y * delta_y <= r_x' * delta_x.
Proof.
    intros * lqty_x lqty_y * trade_success msg_is_trade from_tx to_ty tx_neq_ty *.
    is_sp_destruct. clear is_sp.
    rewrite msg_is_trade in trade_success.
    pose proof (trade_update_rates_formula_pf cstate chain ctx msg_payload cstate' acts
        trade_success)
    as rx_update.
    simpl in rx_update.
    destruct rx_update as [_ rates_update].
    simpl in rates_update.
    destruct rates_update as [tx_update tz_update].
    assert (r_x' = calc_rate_in r_x r_y (qty_trade msg_payload) (stor_outstanding_tokens cstate) x) as r_x'_calc.
    { admit. }
    rewrite r_x'_calc.
    unfold calc_rate_in.
    assert (forall x1 x2 y z : N, z <= x1 / y * x2 <-> z * y <= x1 * x2) as div_alg. 
    { admit. }
    rewrite (div_alg 
        (r_x * x / 1000000 + r_y * calc_delta_y r_x r_y (qty_trade msg_payload) (stor_outstanding_tokens cstate) x / 1000000)
        delta_x
        (x + qty_trade msg_payload)
        (r_y * delta_y)).
Admitted.


Theorem swap_rate_consistency : 
    (* Let t_x be a token with nonzero pooled liquidity and rate r_x > 0 *)
    forall t_x r_x x,
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 /\ 
    FMap.find t_x (stor_tokens_held cstate) = Some x /\ x > 0 ->
    (* then for any delta_x > 0 and any sequence of trades, beginning and ending with t_x *)
    forall delta_x (trade_sequence : list trade_sequence_type) t_fst t_last,
    delta_x > 0 -> 
    (* trade_sequence is a list of successive trades *)
    are_successive_trades trade_sequence -> 
    (* with a first and last trade, t_fst and t_last respectively, *)
    (hd_error trade_sequence) = Some t_fst ->
    (hd_error (rev trade_sequence)) = Some t_last ->
    (* starting from our current bstate and cstate *)
    seq_chain t_fst = bstate ->
    seq_cstate t_fst = cstate ->
    (* the first trade is from t_x *)
    token_in_trade (seq_trade_data t_fst) = t_x ->
    (* the last trade is to t_x *)
    token_out_trade (seq_trade_data t_last) = t_x -> 
    (* delta_x', the output of the last trade, is never larger than delta_x. *)
    let delta_x' := calc_final_delta t_last in 
    delta_x' <= delta_x.
Proof.
    (* from paper: 
        - first prove ry dy \leq rx' dx as a lemma.
        - then consider sequences of trades of length:
            - 1: tx -> tx 
            - 2: tx -> ty -> tx 
            - 3: tx -> ty -> tz -> tx
        - it always follows from the lemma.
    *)
    intros * H_lr * dx_geq_0 trades_successive fst_txn lst_txn start_bstate start_cstate from_tx to_tx *.
    (* induct on the length of the sequence of trades, trade_sequence *)
    set (length trade_sequence) as num_trades.
    induction num_trades eqn:NumTrades.
    (* there can't be zero trades, proof by contradiction *)
    -   pose proof (length_zero_iff_nil trade_sequence) as nil_list.
        apply nil_list in NumTrades.
        rewrite NumTrades in fst_txn.
        inversion fst_txn.
    (* now for the case that there is at least one trade *)
    -   admit.
    (* TODO a function that gives this for any n. Define the function recursively. *)
Admitted.

(* Zero-Impact Liquidity Change :
    The quoted price of trades is unaffected by calling DEPOSIT and WITHDRAW 
*)
Theorem zero_impact_liquidity_change_deposit :
    (* Consider the quoted price of a trade t_x to t_y at cstate, *)
    forall t_x t_y r_x r_y,
    FMap.find t_x (stor_rates cstate) = Some r_x ->
    FMap.find t_y (stor_rates cstate) = Some r_y ->
    let quoted_price := r_x / r_y in 
    (* and a successful DEPOSIT or WITHDRAW action. *)
    forall chain ctx msg payload_pool payload_unpool acts cstate' r_x' r_y',
        receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) ->
        msg = pool payload_pool \/
        msg = unpool payload_unpool ->
    (* Then take the (new) quoted price of a trade t_x to t_y at cstate'. *)
    FMap.find t_x (stor_rates cstate') = Some r_x' ->
    FMap.find t_y (stor_rates cstate') = Some r_y' ->
    let quoted_price' := r_x' / r_y' in 
    (* The quoted price is unchanged. *)
    quoted_price = quoted_price'.
Proof.
    intros * rx_rate ry_rate * successful_txn msg_pool_or_unpool new_rx_rate new_ry_rate *.
    destruct msg_pool_or_unpool as [msg_pool | msg_unpool].
    (* the successful transaction was a deposit *)
    -   is_sp_destruct.
        assert (FMap.find t_x (stor_rates cstate') = FMap.find t_x (stor_rates cstate)) 
        as rate_unchanged_x.
        {   rewrite msg_pool in successful_txn.
            exact (eq_sym (pool_rates_unchanged_pf cstate cstate' chain ctx payload_pool acts 
            successful_txn t_x)). }
        assert (FMap.find t_y (stor_rates cstate') = FMap.find t_y (stor_rates cstate)) 
        as rate_unchanged_y.
        {   rewrite msg_pool in successful_txn.
            exact (eq_sym (pool_rates_unchanged_pf cstate cstate' chain ctx payload_pool acts   
                successful_txn t_y)). }
        replace (FMap.find t_x (stor_rates cstate')) 
        with (FMap.find t_x (stor_rates cstate))
        in new_rx_rate.
        replace (FMap.find t_y (stor_rates cstate')) 
        with (FMap.find t_y (stor_rates cstate))
        in new_ry_rate.
        replace (FMap.find t_x (stor_rates cstate)) 
        with (Some r_x')
        in rx_rate.
        replace (FMap.find t_y (stor_rates cstate)) 
        with (Some r_y')
        in ry_rate.
        injection rx_rate as rx_eq.
        injection ry_rate as ry_eq.
        unfold quoted_price, quoted_price'.
        rewrite rx_eq, ry_eq.
        reflexivity.
    (* the successful transaction was a withdraw *)
    -   is_sp_destruct.
        assert (FMap.find t_x (stor_rates cstate') = FMap.find t_x (stor_rates cstate)) 
        as rate_unchanged_x.
        {   rewrite msg_unpool in successful_txn.
            exact (eq_sym (unpool_rates_unchanged_pf cstate cstate' chain ctx payload_unpool acts 
            successful_txn t_x)). }
        assert (FMap.find t_y (stor_rates cstate') = FMap.find t_y (stor_rates cstate)) 
        as rate_unchanged_y.
        {   rewrite msg_unpool in successful_txn.
            exact (eq_sym (unpool_rates_unchanged_pf cstate cstate' chain ctx payload_unpool acts   
                successful_txn t_y)). }
        replace (FMap.find t_x (stor_rates cstate')) 
        with (FMap.find t_x (stor_rates cstate))
        in new_rx_rate.
        replace (FMap.find t_y (stor_rates cstate')) 
        with (FMap.find t_y (stor_rates cstate))
        in new_ry_rate.
        replace (FMap.find t_x (stor_rates cstate)) 
        with (Some r_x')
        in rx_rate.
        replace (FMap.find t_y (stor_rates cstate)) 
        with (Some r_y')
        in ry_rate.
        injection rx_rate as rx_eq.
        injection ry_rate as ry_eq.
        unfold quoted_price, quoted_price'.
        rewrite rx_eq, ry_eq.
        reflexivity.
Qed.

(* Arbitrage sensitivity :
    If an opportunity for arbitrage exists due to some external market pricing a 
    constituent token differently from the structured pool, the arbitrage loop can be 
    closed with one sufficiently large transaction.

    In our case, this happens because prices adapt through trades due to demand 
    sensitivity or the pool depletes in that particular token.
*)
Theorem arbitrage_sensitivity : 
    forall t_x r_x x,
    (* t_x is a token with nonzero pooled liquidity *)
    FMap.find t_x (stor_rates cstate) = Some r_x /\ 
    r_x > 0 /\ 
    FMap.find t_x (stor_tokens_held cstate) = Some x 
    /\ x > 0 ->
    (* we consider some external price *)    
    forall external_price,
    exists trade_qty, 
    (* and a trade of trade_qty succeeds *)
    forall chain ctx msg msg_payload cstate' acts,
    receive contract chain ctx cstate msg = Ok(cstate', acts) ->
    msg = Some(trade msg_payload) ->
    msg_payload.(qty_trade) = trade_qty ->
    (* the arbitrage opportunity is resolved *)
    let r_x' := get_rate t_x (stor_rates cstate') in
    (* first the case that the external price was lower *)
    (external_price < r_x -> r_x' >= external_price) /\
    (* second the case that the external price is higher *)
    (external_price > r_x -> r_x' <= external_price \/
     FMap.find t_x (stor_tokens_held cstate') = None).
Proof.
    intros * liquidity *.
    (* construct the trade quantity *)
    assert N as trade_qty. admit.
    exists trade_qty.
    intros * successful_trade msg_is_trade qty_traded_is_trade_qty.
    (* show that the trade has equalized arbitrage *)
    split.
    -   intro ext_leq_rx. admit.
    -   intro ext_gt_rx. admit.   
Admitted.


(* Pooled consistency 
    The sum of all the constituent, pooled tokens, multiplied by their value in terms of 
    pooled tokens, always equals the total number of outstanding pool tokens. That is, 
    pool tokens are never under- or over-collateralized. 
*)
Definition fold_fn (rates : FMap token exchange_rate) (tokens_held : FMap token N)
    (n : N) (k : token) : N := 
    let rate := 
        match FMap.find k rates with 
        | Some r => r 
        | None => 0
        end in 
    let qty_held := 
        match FMap.find k tokens_held with 
        | Some r => r 
        | None => 0 
        end in 
    rate * qty_held / 1_000_000.

Definition sum_over_tokens 
    (rates : FMap token exchange_rate) (tokens_held : FMap token N) : N := 
    (* get the list of keys *)
    let token_family := (FMap.keys rates) in 
    (* fold over the list *)
    List.fold_left
        (fold_fn rates tokens_held)
        token_family 
        0.

Theorem pooled_consistency : 
    exists (cstate : State),
    contract_state bstate caddr = Some cstate /\
    (* The sum of all the constituent, pooled tokens, multiplied by their value in terms 
    of pooled tokens, always equals the total number of outstanding pool tokens. *)
    sum_over_tokens (stor_rates cstate) (stor_tokens_held cstate) = 
        (stor_outstanding_tokens cstate).
Proof.
    contract_induction; intros; try exact IH.
    is_sp_destruct. clear is_sp.
    (* Please establish the invariant after deployment of the contract *)
    -   (* we use the fact that balances initialize at zero *)
        pose proof (initialized_with_zero_balance_pf chain ctx setup result init_some)
        as zero_bal.
        pose proof (initialized_with_zero_outstanding_pf chain ctx setup result init_some)
        as zero_outstanding.
        rewrite zero_outstanding. clear zero_outstanding.
        unfold sum_over_tokens.
        unfold fold_fn.
        assert (forall k, match FMap.find k (stor_tokens_held result) with
        | Some r => r
        | None => 0
        end = 0)
        as no_tokens_held.
        {   intro. 
            unfold get_bal in zero_bal.
            pose proof (zero_bal k) as e.
            destruct (FMap.find k (stor_tokens_held result)).
            exact e. 
            reflexivity. }
        assert ((fun (_ : N) (k : token) =>
        match FMap.find k (stor_rates result) with
        | Some r => r
        | None => 0
        end * match FMap.find k (stor_tokens_held result) with
              | Some r => r
              | None => 0
              end / 1000000) = (fun (_ : N) (k : token) => 0))
        as fold_fn_0.
        {   apply functional_extensionality. 
            intro n.
            apply functional_extensionality. 
            intro t.
            rewrite (no_tokens_held t).
            rewrite (N.mul_0_r (match FMap.find t (stor_rates result) with
            | Some r => r
            | None => 0
            end)).
            assert (1000000 <> 0) as neq_n. { auto. }
            exact (N.div_0_l 1000000 neq_n). }
        rewrite fold_fn_0.
        unfold fold_left.
        induction (FMap.keys (stor_rates result)); auto.
    (* Please reestablish the invariant after a nonrecursive call *)
    -   destruct msg.
        (* msg = Some m *)
        +   destruct m.
            (* m = pool *)
            *   is_sp_destruct. clear is_sp.
                (* understand how tokens_held has changed *)
                pose proof (pool_increases_tokens_held_pf prev_state chain ctx p new_state new_acts
                    receive_some) as bal_update.
                simpl in bal_update.
                (* show all rates are the same *)
                pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts
                    receive_some) as rates_update.
                (* show how the outstanding tokens update *)
                pose proof (pool_outstanding_pf prev_state new_state chain ctx p new_acts 
                    receive_some) as out_update.
                simpl in out_update.
                assert (sum_over_tokens (stor_rates new_state) (stor_tokens_held new_state) = 
                    sum_over_tokens (stor_rates prev_state) (stor_tokens_held new_state))
                as rates_unchanged.
                { admit. }
                rewrite rates_unchanged. clear rates_unchanged.
                assert (sum_over_tokens (stor_rates prev_state) (stor_tokens_held new_state) = 
                    sum_over_tokens (stor_rates prev_state) (stor_tokens_held prev_state) + 
                    get_rate (token_pooled p) (stor_rates prev_state) / 1000000 * qty_pooled p)
                as separate_sum.
                { admit. }
                rewrite separate_sum. clear separate_sum.
                rewrite out_update.
                rewrite IH.
                reflexivity.
            (* m = unpool *)
            *   is_sp_destruct. clear is_sp.
                (* understand how tokens_held has changed *)
                pose proof (unpool_decreases_tokens_held_pf prev_state chain ctx u new_state new_acts
                    receive_some) as bal_update.
                simpl in bal_update.
                (* show all rates are the same *)
                pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts
                    receive_some) as rates_update.
                (* show how the outstanding tokens update *)
                pose proof (unpool_outstanding_pf prev_state new_state chain ctx u new_acts 
                    receive_some) as out_update.
                simpl in out_update.
                assert (sum_over_tokens (stor_rates new_state) (stor_tokens_held new_state) = 
                    sum_over_tokens (stor_rates prev_state) (stor_tokens_held new_state))
                as rates_unchanged.
                { admit. }
                rewrite rates_unchanged. clear rates_unchanged.
                assert (sum_over_tokens (stor_rates prev_state) (stor_tokens_held new_state) = 
                    sum_over_tokens (stor_rates prev_state) (stor_tokens_held prev_state) - 
                    1000000 / get_rate (token_unpooled u) (stor_rates prev_state) * qty_unpooled u)
                as separate_sum.
                { admit. }
                rewrite separate_sum. clear separate_sum.
                rewrite out_update.
                rewrite IH.
                reflexivity.
            (* m = trade *)
            *   is_sp_destruct. clear is_sp.
                (* understand how tokens_held has changed *)
                pose proof (trade_tokens_held_update_pf prev_state chain ctx t new_state new_acts 
                    receive_some) as tokens_held_update.
                destruct tokens_held_update as [tokens_held_update_ty tokens_held_update].
                destruct tokens_held_update as [tokens_held_update_tx tokens_held_update_tz].
                (* how calling trade updates rates *)
                pose proof (trade_update_rates_formula_pf prev_state chain ctx t new_state new_acts
                    receive_some) as rates_changed_and_unchanged.
                destruct rates_changed_and_unchanged as [tx_neq_ty rates_changed_and_unchanged].
                destruct rates_changed_and_unchanged as [rx_change rz_unchanged].
                (* how outstanding_tokens has changed by calling trade *)
                pose proof (trade_outstanding_update_pf prev_state chain ctx t new_state new_acts 
                    receive_some) as out_update.
                (* LHS equals sum over tokens except for tx and ty, plus r_x' * etc , minus r_y * delta_y *)
                admit.
        (* msg = None *)
        +   is_sp_destruct. clear is_sp.
            pose proof (none_fails_pf prev_state chain ctx) as failed.
            destruct failed as [err failed].
            rewrite receive_some in failed.
            inversion failed.
    (* Please reestablish the invariant after a recursive call *)
    -   admit. (* probably the same proof *)
    (* solve remaining facts *)
    -   solve_facts.
Admitted.

End AbstractSpecification.