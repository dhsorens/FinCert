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
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.

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
| Pool : pool_data -> entrypoint 
| Unpool : unpool_data -> entrypoint 
| Trade : trade_data -> entrypoint.

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
 * The Contract Specification:
      We detail a list of propositions of a contract's behavior which can be 
      proven true of a given contract.
 * ============================================================================= *)

    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}.

(* Specification of the Msg type:
  - A Pool entrypoint, whose interface is defined by the pool_data type
  - An Unpool entrypoint, whose interface is defined by the unpool_data type
  - A Trade entrypoint, whose interface is defined by the trade_data type
*)
Class Msg_Spec (T : Type) := 
  build_msg_spec {
    pool : pool_data -> T ;
    unpool : unpool_data -> T ;
    trade : trade_data -> T ;
}.

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
    forall bstate caddr cstate chain ctx msg msg_payload qty token cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to POOL was successful *)
    msg = pool msg_payload -> 
    qty = msg_payload.(qty_pooled) -> 
    token = msg_payload.(token_pooled) ->
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := get_bal token (stor_tokens_held cstate') in 
    new_bal = old_bal + qty.


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
    forall bstate caddr cstate chain ctx msg msg_payload qty token cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the call to UNPOOL was successful *)
    msg = unpool msg_payload -> 
    qty = msg_payload.(qty_unpooled) -> 
    token = msg_payload.(token_unpooled) ->
    receive contract chain ctx cstate (Some msg) = 
      Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := get_bal token (stor_tokens_held cstate') in 
    new_bal = old_bal - qty.


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
    forall bstate caddr cstate chain ctx msg msg_payload cstate' acts,
    (* reachable bstate *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* forall calls to the Pool entrypoint *)
    msg = trade (msg_payload) -> 
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
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
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
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


(* Initialization specification *)
(* TODO HOW IS THE CONTRACT INITIALIZED *)
Definition initialized_with_nonzero_rates (contract : Contract Setup Msg State Error) : Prop := 
    forall chain bstate ctx setup cstate,
    (* bstate is reachable *)
    reachable bstate -> 
    (* we call init successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then all rates are nonzero *)
    forall t r,
    FMap.find t (stor_rates cstate) = Some r -> 
    r > 0.

(* we amalgamate each proposition in the specification into a single proposition *)
Definition is_structured_pool
    (C : Contract Setup Msg State Error) : Prop := 
    pool_entrypoint_check C /\
    pool_entrypoint_check_2 C /\
    pool_emits_transfer C /\
    pool_emits_mint C /\
    pool_atomic C /\
    pool_increases_tokens_held C /\
    unpool_entrypoint_check C /\
    unpool_entrypoint_check_2 C /\
    unpool_emits_burn C /\
    unpool_emits_transfer C /\
    unpool_decreases_tokens_held C /\
    trade_entrypoint_check C /\
    trade_entrypoint_check_2 C /\
    trade_pricing_formula C /\
    trade_update_rates_formula C /\
    trade_emits_transfer_tx C /\
    trade_emits_transfer_ty C /\
    initialized_with_nonzero_rates C.

(* A tactic to destruct is_sp if it's in the context of a proof *)
Tactic Notation "is_sp_destruct" := 
match goal with 
    | is_sp : is_structured_pool _ |- _ => 
        unfold is_structured_pool in is_sp;
        destruct is_sp  as [pool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [pool_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [pool_emits_transfer_pf is_sp'];
        destruct is_sp' as [pool_emits_mint_pf is_sp'];
        destruct is_sp' as [pool_atomic_pf is_sp'];
        destruct is_sp' as [pool_increases_tokens_held_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [unpool_emits_burn_pf is_sp'];
        destruct is_sp' as [unpool_emits_transfer_pf is_sp'];
        destruct is_sp' as [unpool_decreases_tokens_held_pf is_sp'];
        destruct is_sp' as [trade_entrypoint_check_pf is_sp'];
        destruct is_sp' as [trade_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [trade_pricing_formula_pf is_sp'];
        destruct is_sp' as [trade_update_rates_formula_pf is_sp'];
        destruct is_sp' as [trade_emits_transfer_tx_pf is_sp'];
        destruct is_sp' as [trade_emits_transfer_ty_pf initialized_with_nonzero_rates_pf]
end.


(* =============================================================================
 * The contract Metaspecification:
      We reason about a contract which satisfies the properties of the specification 
      given here, showing that a contract which satisfies the specification also satisfies
      the properties here.
 * ============================================================================= *)

 Context {contract : Contract Setup Msg State Error}
 { is_sp : is_structured_pool contract }.


(* Demand Sensitivity :
    A trade for a given token increases its price relative to other constituent tokens, 
    so that higher relative demand corresponds to a higher relative price. 
    Likewise, trading one token in for another decreases the first's relative price in 
    the pool, corresponding to slackened demand. This enforces the classical notion of 
    supply and demand 

    We prove that r_x' > r_x and forall t_z, r_z' = r_z.
*)
Lemma rate_decrease : forall r_x r_y delta_x k x, 
    calc_rate_in r_x r_y delta_x k x < r_x.
Proof. Admitted.

Theorem demand_sensitivity :
    forall bstate caddr cstate t_x r_x,
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* r_x is the rate of token t_x *)
    0 < r_x ->
    (FMap.find t_x (stor_rates cstate)) = Some r_x -> 
    (* a trade of t_x for some t_y happens *)
    forall chain ctx msg msg_payload acts cstate',
        receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) ->
        msg = trade msg_payload ->
        msg_payload.(token_in_trade) = t_x ->
        t_x <> msg_payload.(token_out_trade) ->
    (* new cstate induced by *)
    let r_x' := get_rate t_x (stor_rates cstate') in 
    (* r_x' goes down while all other rates stay constant *)
    r_x' < r_x /\
    forall t,
    t <> t_x ->
    get_rate t (stor_rates cstate') = get_rate t (stor_rates cstate).
Proof.
    intros. 
    is_sp_destruct.
    pose proof (trade_entrypoint_check_2_pf bstate caddr cstate chain ctx msg msg_payload
            cstate' acts H7 H8 H9 H13 H12).
    do 4 destruct H16. destruct H17.
    (* get the new rates *)  
    pose proof (trade_update_rates_formula_pf bstate caddr cstate chain ctx msg msg_payload t_x (msg_payload.(token_out_trade)) (msg_payload.(qty_trade)) cstate' acts H7 H8 H9 H13 (eq_sym H14) (reflexivity (token_out_trade msg_payload)) H15 (reflexivity (qty_trade msg_payload)) H12). 
    destruct H19.
    (*  *)
    split.
    -   unfold r_x'. unfold get_rate.
        replace (FMap.find t_x (stor_rates cstate')) 
        with (Some
            (calc_rate_in 
                (get_rate t_x (stor_rates cstate))
                (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                (qty_trade msg_payload)
                (stor_outstanding_tokens cstate) 
                (get_bal t_x (stor_tokens_held cstate)))).
        assert (r_x = (get_rate t_x (stor_rates cstate))).
        +   unfold get_rate. 
            replace (FMap.find t_x (stor_rates cstate)) 
            with (Some r_x).
            reflexivity.
        +   rewrite H21.
            exact (rate_decrease 
                (get_rate t_x (stor_rates cstate)) 
                (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                (qty_trade msg_payload)
                (stor_outstanding_tokens cstate) 
                (get_bal t_x (stor_tokens_held cstate))).
    -   intros. unfold get_rate.
        replace (FMap.find t (stor_rates cstate')) with (FMap.find t (stor_rates cstate));
        try exact (eq_sym (H20 t H21)).
        auto.
Qed.


(* Nonpathological prices 
    As relative prices shift over time, a price that starts out nonzero never goes to 
    zero or to a negative value. 

    This is to avoid pathological behavior of zero or negative prices. 

    Note, however, that prices can still get arbitrarily close to zero, like in the case 
    of CPMMs.
*) (*
Theorem nonpathological_prices : 
    forall bstate caddr cstate n,
    (* the state is reachable *)
    reachable bstate -> 
    (* get the address *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* the statement *)
    forall t,
    (* token in the ledger => rate neq zero *)
    FMap.find t (stor_rates cstate) = Some n /\ n > 0 -> 
    (* any state reachable through cstate has the same property *)
    forall bstate' cstate',
    reachable_through bstate bstate' -> 
    contract_state bstate' caddr = Some cstate' ->
    (* the token still has an exchange rate greater than zero in the new state cstate' *)
    exists n', 
    FMap.find t (stor_rates cstate) = Some n' /\ n' > 0.
Proof.
    intros.
    (* contract induction over the trace *)

*)

(* Functional non-depletion :
    No trade can empty the entire pool of tokens. This mimics properties of CPMMs 
    currently, for which no trade can deplete any constituent token of any pool. The 
    difference here is that we are willing to let individual, constituent tokens deplete, 
    but do not allow the entire pool to deplete. 

    This is because tokenized carbon credits can be consumed by being retired as offsets, 
    so while we don't want the entire class of carbon credits to deplete from the pool by 
    trading, we should enable individual credits to deplete.
*)
Theorem functional_non_depletion :
    forall bstate caddr cstate,
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* there is liquidity *)
    (stor_outstanding_tokens cstate) > 0 -> 
    (* a trade occurs *)
    forall chain ctx msg msg_payload acts cstate',
        receive contract chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
        msg = trade msg_payload ->
    (* there is liquidity *)
    (stor_outstanding_tokens cstate') > 0.
Proof. (* 
    intros.
    pose proof (trade_entrypoint_check_2_pf bstate caddr cstate chain ctx msg msg_payload
            cstate' acts H7 H8 H9 H12 H11).
    do 4 destruct H13. destruct H14.
    rewrite H12 in H11. *)
    (* open up the receive function 
    cbn in H7.
    destruct 
        (FMap.find (token_in_trade msg_payload) (tokens_held cstate)),
        (FMap.find (token_in_trade msg_payload) (rates cstate)),
        (FMap.find (token_out_trade msg_payload) (rates cstate)) in H7; 
    cbn in H7; inversion H7. 
    destruct (RPMM.get_bal (token_out_trade msg_payload) (tokens_held cstate) <?
           calc_delta_y e n0 (qty_trade msg_payload) (outstanding_tokens cstate) n)%N in H7;
    cbn in H7; inversion H7.
    clear H7 H13 H15.*)
    (*  *)
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
Theorem swap_rate_consistency : 
    forall bstate caddr cstate,
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* a trade from t_x to t_z *)
    forall t_x t_z qty_trade
        chain ctx msg_xz msg_payload_xz acts_xz cstate_xz,
        receive contract chain ctx cstate msg_xz = Ok (cstate_xz, acts_xz) ->
        msg_xz = Some (trade msg_payload_xz) -> 
        msg_payload_xz = Build_trade_data t_x t_z qty_trade ->
    (* a trade from t_x to t_y *)
    forall t_y msg_xy msg_payload_xy acts_xy cstate_xy,
        receive contract chain ctx cstate msg_xy = Ok (cstate_xy, acts_xy) ->
        msg_xy = Some (trade msg_payload_xy) -> 
        msg_payload_xy = Build_trade_data t_x t_y qty_trade ->
    (* which yields delta_y tokens in t_y *)
    let delta_y := 
        (get_bal t_y (stor_tokens_held cstate)) - 
        (get_bal t_y (stor_tokens_held cstate_xy)) in 
    (* followed by a trade of delta_y from t_y to t_z *)
    forall msg_yz msg_payload_yz acts_yz cstate_yz chain' ctx',
        receive contract chain' ctx' cstate_xy msg_yz = Ok (cstate_yz, acts_yz) ->
        msg_yz = Some (trade msg_payload_yz) -> 
        msg_payload_yz = Build_trade_data t_y t_z delta_y ->
    (* the output delta_z *)
    let delta_z_direct := 
        (get_bal t_z (stor_tokens_held cstate)) - 
        (get_bal t_z (stor_tokens_held cstate_xz)) in 
    let delta_z_indirect := 
        (get_bal t_z (stor_tokens_held cstate)) - 
        (get_bal t_z (stor_tokens_held cstate_yz)) in     
    (* the direct trade yielded more t_z than the indirect trade *)
    delta_z_direct > delta_z_indirect.
Proof. Admitted.


(* Arbitrage sensitivity :
    If an opportunity for arbitrage exists due to some external market pricing a 
    constituent token differently from the structured pool, the arbitrage loop can be 
    closed with one sufficiently large transaction.

    In our case, this happens because prices adapt through trades due to demand 
    sensitivity or the pool depletes in that particular token.
*)
Theorem arbitrage_sensitivity : 
    forall bstate caddr cstate t_x, 
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (*  *)
    forall external_price 
    chain ctx msg msg_payload cstate' acts,
    receive contract chain ctx cstate msg = Ok(cstate', acts) -> 
    msg = Some(trade msg_payload) -> 
    exists trade_qty, 
    msg_payload.(qty_trade) = trade_qty -> 
    (* price stabilizes or liquidity depletes *)
    FMap.find t_x (stor_rates cstate') = Some(external_price) \/
    FMap.find t_x (stor_tokens_held cstate') = None.
Proof. Admitted.


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
    forall bstate caddr cstate,
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr *)
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    (* the contract state is cstate *)
    contract_state bstate caddr = Some cstate -> 
    (* The sum of all the constituent, pooled tokens, multiplied by their value in terms 
    of pooled tokens, always equals the total number of outstanding pool tokens. *)
    sum_over_tokens (stor_rates cstate) (stor_tokens_held cstate) = 
        (stor_outstanding_tokens cstate).
Proof. Admitted.


End AbstractSpecification.