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
From Coq Require Import Permutation.
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
      (* the exchange rates *)
      stor_rates : T -> FMap token exchange_rate ;
      (* token balances *)
      stor_tokens_held : T -> FMap token N ;
      (* pool token data *)
      stor_pool_token : T -> token ; 
      (* number of outstanding pool tokens *)
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
(* A call to the DEPOSIT entrypoint fails if the token to be pooled is not in the 
    rates map held in the storage (=> is not in T) *)
Definition pool_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload,
    (* If there is no entry in the rates map for the token to be pooled, *)
    FMap.find msg_payload.(token_pooled) (stor_rates cstate) = None -> 
    (* the transaction fails. *)
    receive contract chain ctx cstate (Some (pool (msg_payload))) = 
      Err(error_to_Error error_TOKEN_NOT_FOUND).

(* A successful call to DEPOSIT means that token_pooled has an exchange rate (=> is in T) *)
Definition pool_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (pool (msg_payload))) = Ok(cstate', acts) -> 
    (* an exchange rate exists *)
    exists r_x, 
    FMap.find msg_payload.(token_pooled) (stor_rates cstate) = Some r_x.

(* When the DEPOSIT entrypoint is successfully called, it emits a TRANSFER call to the 
    token in storage, with q tokens in the payload of the call *)
Definition pool_emits_txns (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (pool (msg_payload))) = Ok(cstate', acts) -> 
    (* in the acts list there is a transfer call with q tokens as the payload *)
    exists transfer_to transfer_data transfer_payload mint_data mint_payload,
    (* there is a transfer call *)
    let transfer_call := (act_call 
        (* calls the pooled token address *)
        (msg_payload.(token_pooled).(FA2Spec.token_address)) 
        (* with amount 0 *)
        0
        (* and payload transfer_payload *)
        (serialize (FA2Spec.Transfer transfer_payload))) in 
    (* with a transfer in it *)
    In transfer_data transfer_payload /\ 
    (* which itself has transfer data *)
    In transfer_to transfer_data.(FA2Spec.txs) /\
    (* whose quantity is the quantity pooled *)
    transfer_to.(FA2Spec.amount) = msg_payload.(qty_pooled) /\
    (* there is a mint call in acts *)
    let mint_call := (act_call 
        (* calls the pool token contract *)
        (stor_pool_token cstate).(FA2Spec.token_address) 
        (* with amount 0 *)
        0 
        (* and payload mint_payload *)
        (serialize (FA2Spec.Mint mint_payload))) in 
    (* with has mint_data in the payload *)
    In mint_data mint_payload /\
    (* and the mint data has these properties: *)
    let r_x := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    mint_data.(FA2Spec.qty) = msg_payload.(qty_pooled) * r_x / 1_000_000 /\
    mint_data.(FA2Spec.mint_owner) = ctx.(ctx_from) /\ 
    (* these are the only emitted transactions *)
    (acts = [ transfer_call ; mint_call ] \/
    acts = [ mint_call ; transfer_call ]).

(* When the DEPOSIT entrypoint is successfully called, tokens_held goes up appropriately *)
Definition pool_increases_tokens_held (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let token := msg_payload.(token_pooled) in
    let qty := msg_payload.(qty_pooled) in
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := get_bal token (stor_tokens_held cstate') in 
    new_bal = old_bal + qty /\ 
    forall t,
    t <> token -> 
    get_bal t (stor_tokens_held cstate) = 
    get_bal t (stor_tokens_held cstate').

(* And the rates don't change *)
Definition pool_rates_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

(* The outstanding tokens change appropriately *)
Definition pool_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    let rate_in := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    let qty := msg_payload.(qty_pooled) in 
    stor_outstanding_tokens cstate' = 
    stor_outstanding_tokens cstate + rate_in / 1000000 * qty.

(* Specification of the UNPOOL entrypoint *)

(* A call to the WITHDRAW entrypoint fails if the token to be unpooled is not in the 
    rates map held in the storage (=> is not in T) *)
Definition unpool_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload,
    (* If there is no entry in the rates map for the token to be unpooled, *)
    FMap.find msg_payload.(token_unpooled) (stor_rates cstate) = None -> 
    (* the transaction fails. *)
    receive contract chain ctx cstate (Some (unpool (msg_payload))) = 
      Err(error_to_Error error_TOKEN_NOT_FOUND).


(* A successful call to WITHDRAW means that token_pooled has an exchange rate (=> is in T) *)
Definition unpool_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (unpool (msg_payload))) = Ok(cstate', acts) -> 
    (* an exchange rate exists *)
    exists r_x,
    FMap.find msg_payload.(token_unpooled) (stor_rates cstate) = Some r_x.

Definition unpool_entrypoint_check_3 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (unpool (msg_payload))) = Ok(cstate', acts) -> 
    (* an exchange rate exists *)
    qty_unpooled msg_payload <=
    get_rate (token_unpooled msg_payload) (stor_rates cstate) * get_bal (token_unpooled msg_payload) (stor_tokens_held cstate) / 1_000_000.

(* When the WITHDRAW entrypoint is successfully called, it emits a BURN call to the 
    pool_token, with q in the payload *)
Definition unpool_emits_txns (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to WITHDRAW was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* in the acts list there are burn and transfer transactions *)
    exists burn_data burn_payload transfer_to transfer_data transfer_payload,
    (* there is a burn call in acts *)
    let burn_call := (act_call
        (* calls the pool token address *)
        (stor_pool_token cstate).(FA2Spec.token_address)
        (* with amount 0 *)
        0
        (* with payload burn_payload *)
        (serialize (FA2Spec.Retire burn_payload))) in 
    (* with has burn_data in the payload *)
    In burn_data burn_payload /\
    (* and burn_data has these properties: *)
    burn_data.(FA2Spec.retire_amount) = msg_payload.(qty_unpooled) /\
    (* the burned tokens go from the unpooler *)
    burn_data.(FA2Spec.retiring_party) = ctx.(ctx_from) /\
    (* there is a transfer call *)
    let transfer_call := (act_call 
        (* call to the token address *)
        (msg_payload.(token_unpooled).(FA2Spec.token_address))
        (* with amount = 0 *)
        0 
        (* with payload transfer_payload *)
        (serialize (FA2Spec.Transfer transfer_payload))) in 
    (* with a transfer in it *)
    In transfer_data transfer_payload /\ 
    (* which itself has transfer data *)
    In transfer_to transfer_data.(FA2Spec.txs) /\
    (* whose quantity is the quantity pooled *)
    let r_x := get_rate msg_payload.(token_unpooled) (stor_rates cstate) in 
    transfer_to.(FA2Spec.amount) = msg_payload.(qty_unpooled) * 1_000_000 / r_x /\
    (* and these are the only emitted transactions *)
    (acts = [ burn_call ; transfer_call ] \/
     acts = [ transfer_call ; burn_call ]).


(* When the UNPOOL entrypoint is successfully called, tokens_held goes down appropriately *)
Definition unpool_decreases_tokens_held (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let token := msg_payload.(token_unpooled) in
    let r_x := get_rate token (stor_rates cstate) in 
    let qty := msg_payload.(qty_unpooled) * 1_000_000 / r_x in
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := get_bal token (stor_tokens_held cstate') in 
    new_bal = old_bal - qty /\ 
    forall t,
    t <> token -> 
    get_bal t (stor_tokens_held cstate) = 
    get_bal t (stor_tokens_held cstate').

(* When the UNPOOL entrypoint is successfully called, tokens_held goes down appropriately *)
Definition unpool_rates_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

Definition unpool_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to DEPOSIT was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    let rate_in := get_rate msg_payload.(token_unpooled) (stor_rates cstate) in 
    let qty := msg_payload.(qty_unpooled) in 
    stor_outstanding_tokens cstate' = 
    stor_outstanding_tokens cstate - qty.

(* A call to the TRADE entrypoint fails if either the token to be traded in or the token 
    to be traded out is not in the rates map held in the storage (=> is not in T) *)
Definition trade_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload,
    (* If there is no entry in the rates map for either token in the trade, *)
    ((FMap.find msg_payload.(token_in_trade) (stor_rates cstate) = None) \/
     (FMap.find msg_payload.(token_out_trade) (stor_rates cstate) = None)) ->
    (* the transaction fails. *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = 
      Err(error_to_Error error_TOKEN_NOT_FOUND).

(* A successful call to TRADE means that token_in_trade and token_out_trade have exchange 
    rates (=> are in T) *)
Definition trade_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* exchange rates exist *)
    exists x r_x r_y,
    ((FMap.find msg_payload.(token_in_trade) (stor_tokens_held cstate) = Some x) /\
    (FMap.find msg_payload.(token_in_trade) (stor_rates cstate) = Some r_x) /\
    (FMap.find msg_payload.(token_out_trade) (stor_rates cstate) = Some r_y)).


(* Specification of the TRADE entrypoint *)
(* When TRADE is successfully called, the trade is priced using the correct formula 
    given by calculate_trade. The updated rate is also priced using the formula from
    calculate_trade. *)
Definition trade_pricing_formula (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload t_x t_y q cstate' acts,
    (* the TRADE entrypoint was called succesfully *)
    t_x = msg_payload.(token_in_trade) -> 
    t_y = msg_payload.(token_out_trade) -> 
    t_x <> t_y -> 
    q = msg_payload.(qty_trade) ->
    receive contract chain ctx cstate (Some (trade msg_payload)) = 
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


Definition trade_update_rates (contract : Contract Setup Msg State Error) : Prop := 
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
    (stor_rates cstate') = 
    (FMap.add (token_in_trade msg_payload)
        (calc_rate_in (get_rate (token_in_trade msg_payload) (stor_rates cstate))
        (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
        (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)))
        (stor_rates cstate)).


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


(* When TRADE is successfully called, it emits two TRANSFER actions *)
Definition trade_emits_transfers (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to TRADE was successful *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* the acts list consists of two transfer actions, specified as follows: *)
    exists transfer_to_x transfer_data_x transfer_payload_x
           transfer_to_y transfer_data_y transfer_payload_y,
    (* there is a transfer call for t_x *)
    let transfer_tx := (act_call 
        (* call to the correct token address *)
        (msg_payload.(token_in_trade).(FA2Spec.token_address))
        (* with amount = 0 *)
        0
        (* and payload transfer_payload_x *)
        (serialize (FA2Spec.Transfer transfer_payload_x))) in 
    (* with a transfer in it *)
    In transfer_data_x transfer_payload_x /\ 
    (* which itself has transfer data *)
    In transfer_to_x transfer_data_x.(FA2Spec.txs) /\
    (* whose quantity is the quantity traded, transferred to the contract *)
    transfer_to_x.(FA2Spec.amount) = msg_payload.(qty_trade) /\
    transfer_to_x.(FA2Spec.to_) = ctx.(ctx_contract_address) /\ 
    (* there is a transfer call for t_y *)
    let transfer_ty := (act_call 
        (* call to the correct token address *)
        (msg_payload.(token_out_trade).(FA2Spec.token_address))
        (* with amount = 0 *)
        0 
        (* and payload transfer_payload_y *)
        (serialize (FA2Spec.Transfer transfer_payload_y))) in 
    (* with a transfer in it *)
    In transfer_data_y transfer_payload_y /\ 
    (* which itself has transfer data *)
    In transfer_to_y transfer_data_y.(FA2Spec.txs) /\
    (* whose quantity is the quantity traded, transferred to the contract *)
    let t_x := msg_payload.(token_in_trade) in 
    let t_y := msg_payload.(token_out_trade) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let q := msg_payload.(qty_trade) in 
    transfer_to_y.(FA2Spec.amount) = calc_delta_y rate_in rate_out q k x  /\
    transfer_to_y.(FA2Spec.to_) = ctx.(ctx_from) /\ 
    (* acts is only these two transfers *)
    (acts = [ transfer_tx ; transfer_ty ] \/
     acts = [ transfer_ty ; transfer_tx ]).


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
    (* balances update appropriately *)
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
    (stor_outstanding_tokens cstate') = (stor_outstanding_tokens cstate).

Definition trade_pricing (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to TRADE was successful *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* balances for t_x change appropriately *)
    FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate') =
    Some (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate) + (qty_trade msg_payload)) /\ 
    (* balances for t_y change appropriately *)
    let t_x := token_in_trade msg_payload in 
    let t_y := token_out_trade msg_payload in 
    let delta_x := qty_trade msg_payload in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in
    (* in the new state *)
    FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate') =
    Some (get_bal (token_out_trade msg_payload) (stor_tokens_held cstate) 
        - (calc_delta_y rate_in rate_out delta_x k x)).


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
Definition initialized_with_positive_rates (contract : Contract Setup Msg State Error) := 
    forall chain ctx setup cstate,
    (* If the contract initializes successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then all rates are nonzero *)
    forall t r,
    FMap.find t (stor_rates cstate) = Some r -> 
    r > 0.

Definition initialized_with_zero_balance (contract : Contract Setup Msg State Error) := 
    forall chain ctx setup cstate,
    (* If the contract initializes successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then all token balances initialize to zero *)
    forall t,
    get_bal t (stor_tokens_held cstate) = 0.

Definition initialized_with_zero_outstanding (contract : Contract Setup Msg State Error) := 
    forall chain ctx setup cstate,
    (* If the contract initializes successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then there are no outstanding tokens *)
    stor_outstanding_tokens cstate = 0.

Definition initialized_with_init_rates (contract : Contract Setup Msg State Error) := 
    forall chain ctx setup cstate,
    (* If the contract initializes successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then the init rates map is the same as given in the setup *)
    (stor_rates cstate) = (init_rates setup).

Definition initialized_with_pool_token (contract : Contract Setup Msg State Error) := 
    forall chain ctx setup cstate,
    (* If the contract initializes successfully *)
    init contract chain ctx setup = Ok cstate -> 
    (* then the pool token is the same as given in the setup *)
    (stor_pool_token cstate) = (init_pool_token setup).

(* we amalgamate each proposition in the specification into a single proposition *)
Definition is_structured_pool
    (C : Contract Setup Msg State Error) : Prop := 
    none_fails C /\
    (* pool entrypoint specification *)
    pool_entrypoint_check C /\
    pool_entrypoint_check_2 C /\
    pool_emits_txns C /\
    pool_increases_tokens_held C /\
    pool_rates_unchanged C /\
    pool_outstanding C /\
    (* unpool entrypoint specification *)
    unpool_entrypoint_check C /\
    unpool_entrypoint_check_2 C /\
    unpool_entrypoint_check_3 C /\
    unpool_emits_txns C /\
    unpool_decreases_tokens_held C /\
    unpool_rates_unchanged C /\
    unpool_outstanding C /\
    (* trade entrypoint specification *)
    trade_entrypoint_check C /\
    trade_entrypoint_check_2 C /\
    trade_pricing_formula C /\
    trade_update_rates C /\
    trade_update_rates_formula C /\
    trade_emits_transfers C /\
    trade_tokens_held_update C /\
    trade_outstanding_update C /\
    trade_pricing C /\ 
    (* initialization specification *)
    initialized_with_positive_rates C /\
    initialized_with_zero_balance C /\
    initialized_with_zero_outstanding C /\ 
    initialized_with_init_rates C /\ 
    initialized_with_pool_token C.

(* A tactic to destruct is_sp if it's in the context of a proof *)
Tactic Notation "is_sp_destruct" := 
    match goal with 
    | is_sp : is_structured_pool _ |- _ => 
        unfold is_structured_pool in is_sp;
        destruct is_sp  as [none_fails_pf is_sp'];
        (* isolate the pool entrypoint specification *)
        destruct is_sp'  as [pool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [pool_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [pool_emits_txns_pf is_sp'];
        destruct is_sp' as [pool_increases_tokens_held_pf is_sp'];
        destruct is_sp' as [pool_rates_unchanged_pf is_sp'];
        destruct is_sp' as [pool_outstanding_pf is_sp'];
        (* isolate the unpool entrypoint specification *)
        destruct is_sp' as [unpool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_3_pf is_sp'];
        destruct is_sp' as [unpool_emits_txns_pf is_sp'];
        destruct is_sp' as [unpool_decreases_tokens_held_pf is_sp'];
        destruct is_sp' as [unpool_rates_unchanged_pf is_sp'];
        destruct is_sp' as [unpool_outstanding_pf is_sp'];
        (* isolate the trade entrypoint specification *)
        destruct is_sp' as [trade_entrypoint_check_pf is_sp'];
        destruct is_sp' as [trade_entrypoint_check_2_pf is_sp'];
        destruct is_sp' as [trade_pricing_formula_pf is_sp'];
        destruct is_sp' as [trade_update_rates_pf is_sp'];
        destruct is_sp' as [trade_update_rates_formula_pf is_sp'];
        destruct is_sp' as [trade_emits_transfers is_sp'];
        destruct is_sp' as [trade_tokens_held_update_pf is_sp']; 
        destruct is_sp' as [trade_outstanding_update_pf is_sp'];
        destruct is_sp' as [trade_pricing is_sp'];
        (* isolate the initialization specification *)
        destruct is_sp' as [initialized_with_positive_rates_pf is_sp']; 
        destruct is_sp' as [initialized_with_zero_balance_pf is_sp']; 
        destruct is_sp' as [initialized_with_zero_outstanding_pf is_sp'];
        destruct is_sp' as [initialized_with_init_rates_pf initialized_with_pool_token_pf]
end.


(* =============================================================================
 * The contract Metaspecification:
      We reason about a contract which satisfies the properties of the specification 
      given here, showing that a contract which satisfies the specification also satisfies
      the properties here.
 * ============================================================================= *)

Context {contract : Contract Setup Msg State Error}
        { is_sp : is_structured_pool contract }.
        (* some common assumptions in the metaspecification 
        { bstate : ChainState } { caddr : Address } { cstate : State }
        (* reachable state *)
        { reachable_st : reachable bstate } { trace : ChainTrace empty_state bstate}
        (* with contract at caddr *)
        { contract_at_caddr : env_contracts bstate caddr = Some (contract : WeakContract) }
        (* with contract state cstate *)
        { state_is_cstate : contract_state bstate caddr = Some cstate }.*)

(* Some assumptions (should probably prove some of these) *)
(* update_rate function returns positive number if the num, denom are positive *)
Lemma update_rate_returns_positive : forall r_x r_y delta_x k x, 
    let r_x' := calc_rate_in r_x r_y delta_x k x in
    let delta_y := calc_delta_y r_x r_y delta_x k x in  
    (r_x * x / 1_000_000 + r_y * delta_y / 1_000_000) > 0 -> 
    (x + delta_x) > 0 -> 
    r_x' > 0.
Admitted.

(* TODO Lemma-tize *)
Axiom update_rate_stays_positive : forall r_x r_y delta_x k x, 
    let r_x' := calc_rate_in r_x r_y delta_x k x in
    r_x > 0 ->
    r_x' > 0.

(* calculate_trade function returns a positive number if k, r_x, r_y, delta_x > 0 *)
Lemma calc_trade_returns_positive : forall r_x r_y delta_x k x, 
    k > 0 -> 
    r_x > 0 -> 
    r_y > 0 -> 
    delta_x > 0 -> 
    calc_delta_y r_x r_y delta_x k x > 0.
Admitted.

(* r_x' < r_x *)
Lemma rate_decrease : forall r_x r_y delta_x k x, 
    let r_x' := calc_rate_in r_x r_y delta_x k x in 
    r_x' < r_x.
Admitted.

(* Assumed: delta_y < ( r_y / r_x ) * delta_x *)
Axiom trade_upper_bound : forall r_x r_y delta_x k x, 
    let delta_y := calc_delta_y r_x r_y delta_x k x in 
    delta_y < ( r_y / r_x ) * delta_x.

(* just simplified from ^^ *)
Axiom trade_upper_bound_2 : forall r_x r_y delta_x k x, 
    let delta_y := calc_delta_y r_x r_y delta_x k x in 
    r_x * delta_y < r_y * delta_x.

(* TODO add in > 0 for each of these (fix arb proof); distill the right assumption to make
    about the xy = k curve *)
Lemma arbitrage_lemma_lt :
    forall rate_x rate_y ext k x,
    ext < rate_x -> 
    exists delta_x,
    calc_rate_in rate_x rate_y delta_x k x <= ext.
Admitted.

(* TODO THIS IS FALSE, the one you have to choose is the actual balance that you have, then it depletes. *)
Lemma arbitrage_lemma_gt : 
    forall rate_x rate_y ext k x,
    ext > rate_x -> 
    exists delta_x,
    calc_rate_in rate_x rate_y delta_x k x >= ext.
Admitted.



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

Theorem demand_sensitivity cstate :
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

Theorem nonpathological_prices bstate caddr :
    (* reachable state with contract at caddr *)
    reachable bstate -> 
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    (* the statement *)
    exists (cstate : State),
    contract_state bstate caddr = Some cstate /\
    (* For a token t_x in T and rate r_x, *)
    forall t_x r_x,
    (* if r_x is the exchange rate of t_x, then r_x > 0 *)
    FMap.find t_x (stor_rates cstate) = Some r_x -> r_x > 0.
Proof.
    intros reachable_st contract_at_caddr.
    contract_induction; intros.
    (* Please reestablish the invariant after addition of a block *)
    -   exact (IH t_x r_x H6).
    (* Please establish the invariant after deployment of the contract *)
    -   is_sp_destruct. clear is_sp.
        pose proof (initialized_with_positive_rates_pf chain ctx setup result init_some) as init_rates.
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
Definition trade_to_delta_y (t : trade_sequence_type) := 
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

Fixpoint leq_list (l : list N) : Prop := 
    match l with 
    | [] => True 
    | h :: tl => 
        match tl with 
        | [] => True 
        | h' :: tl' => (h <= h') /\ leq_list tl 
        end 
    end.

Definition trade_to_ry_delta_y (t : trade_sequence_type) := 
    let delta_y := trade_to_delta_y t in 
    let rate_y := get_rate (token_out_trade (seq_trade_data t)) (stor_rates (seq_cstate t)) in 
    rate_y * delta_y.

Lemma swap_rate_lemma (trade_sequence : list trade_sequence_type) : 
    (* if this is a list of successive trades *)
    are_successive_trades trade_sequence -> 
    (* then  *)
    leq_list (map trade_to_ry_delta_y trade_sequence).
Admitted. 


Theorem swap_rate_consistency bstate cstate : 
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
    let delta_x' := trade_to_delta_y t_last in 
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
Theorem zero_impact_liquidity_change :
    (* Consider the quoted price of a trade t_x to t_y at cstate, *)
    forall cstate t_x t_y r_x r_y,
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
    forall cstate t_x r_x x,
    (* t_x is a token with nonzero pooled liquidity *)
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 /\ 
    FMap.find t_x (stor_tokens_held cstate) = Some x /\ x > 0 ->
    (* we consider some external price *)    
    forall external_price,
    (* and a trade of trade_qty succeeds *)
    forall chain ctx msg msg_payload cstate' acts,
    receive contract chain ctx cstate msg = Ok(cstate', acts) ->
    msg = Some(trade msg_payload) ->
    t_x = (token_in_trade msg_payload) ->
    (* the arbitrage opportunity is resolved *)
    let r_x' := get_rate t_x (stor_rates cstate') in
    (* first the case that the external price was lower *)
    (external_price < r_x -> 
        exists trade_qty,
        msg_payload.(qty_trade) = trade_qty ->
        external_price >= r_x') /\
    (* second the case that the external price is higher *)
    (external_price > r_x -> 
    exists trade_qty,
        msg_payload.(qty_trade) = trade_qty ->
        external_price <= r_x' \/
     FMap.find t_x (stor_tokens_held cstate') = None).
Proof.
    intros * liquidity * successful_trade msg_is_trade tx_trade_in.
    (* show that the trade has equalized arbitrage *)
    split.
    (* the external market prices lower than the contract *)
    -   is_sp_destruct.
        intro ext_lt_rx.
        (* the strategy is to buy low (externally), sell high (internally) *)
        pose proof arbitrage_lemma_lt r_x (get_rate (token_out_trade msg_payload) (stor_rates cstate)) external_price (stor_outstanding_tokens cstate) (get_bal t_x 
            (stor_tokens_held cstate)) ext_lt_rx
        as arb_lemma_lt.
        destruct arb_lemma_lt as [trade_qty new_rate_lt].
        exists trade_qty.
        (* use the spec to get r_x' *)
        intro traded_qty.
        rewrite msg_is_trade in successful_trade.
        pose proof trade_update_rates_formula_pf cstate chain ctx msg_payload cstate' acts
            successful_trade as new_rate_calc.
        destruct new_rate_calc as [_ rates].
        destruct rates as [new_rx _].
        unfold get_rate.
        rewrite tx_trade_in.
        replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate'))
        with (Some
        (calc_rate_in (get_rate (token_in_trade msg_payload) (stor_rates cstate))
           (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
           (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)))).
        assert (r_x = (get_rate (token_in_trade msg_payload) (stor_rates cstate)))
        as rx_got_rate.
        {   unfold get_rate.
            destruct liquidity as [rx_l _].
            rewrite tx_trade_in in rx_l.
            replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
            with (Some r_x).
            reflexivity. }
        rewrite rx_got_rate in new_rate_lt.
        rewrite <- traded_qty in new_rate_lt.
        rewrite tx_trade_in in new_rate_lt.
        apply (N.le_ge (calc_rate_in (get_rate (token_in_trade msg_payload) (stor_rates cstate))
        (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
        (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate))) external_price) in new_rate_lt.
        exact new_rate_lt.
    (* the external market prices higher than the contract *)
    -   is_sp_destruct.
        intro ext_gt_rx.
        (* the strategy is to buy low (internally), sell high (externally) *)
        pose proof arbitrage_lemma_gt r_x (get_rate (token_out_trade msg_payload) (stor_rates cstate)) external_price (stor_outstanding_tokens cstate) (get_bal t_x 
            (stor_tokens_held cstate)) ext_gt_rx
        as arb_lemma_gt.
        destruct arb_lemma_gt as [trade_qty new_rate_gt].
        exists trade_qty.
        (* use the spec to get r_x' *)
        intro traded_qty.
        rewrite msg_is_trade in successful_trade.
        pose proof trade_update_rates_formula_pf cstate chain ctx msg_payload cstate' acts
            successful_trade as new_rate_calc.
        destruct new_rate_calc as [_ rates].
        destruct rates as [new_rx _].
        unfold get_rate.
        rewrite tx_trade_in.
        replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate'))
        with (Some
        (calc_rate_in (get_rate (token_in_trade msg_payload) (stor_rates cstate))
           (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
           (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)))).
        assert (r_x = (get_rate (token_in_trade msg_payload) (stor_rates cstate)))
        as rx_got_rate.
        {   unfold get_rate.
            destruct liquidity as [rx_l _].
            rewrite tx_trade_in in rx_l.
            replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
            with (Some r_x).
            reflexivity. }
        rewrite rx_got_rate in new_rate_gt.
        rewrite <- traded_qty in new_rate_gt.
        rewrite tx_trade_in in new_rate_gt.
        apply (N.ge_le (calc_rate_in (get_rate (token_in_trade msg_payload) (stor_rates cstate))
        (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
        (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate))) external_price) in new_rate_gt.
        left.
        exact new_rate_gt.
Qed.


(* Pooled consistency 
    The sum of all the constituent, pooled tokens, multiplied by their value in terms of 
    pooled tokens, always equals the total number of outstanding pool tokens. That is, 
    pool tokens are never under- or over-collateralized. 
*)

(* map over the keys *)
Definition tokens_to_values (rates : FMap token exchange_rate) (tokens_held : FMap token N) : list N := 
    List.map
        (fun k => 
            let rate := get_rate k rates in 
            let qty_held := get_bal k tokens_held in 
            rate * qty_held / 1_000_000)
        (FMap.keys rates).

(* some lemmas *)
Lemma token_keys_invariant_pool : forall p new_state new_acts prev_state ctx chain,
    receive contract chain ctx prev_state (Some (pool p)) =
        Ok (new_state, new_acts) -> 
    (FMap.keys (stor_rates new_state)) = 
    (FMap.keys (stor_rates prev_state)).
Proof.
    intros * receive_some.
    is_sp_destruct.
    (* pool p *)
    pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts receive_some) as rates_unchanged.
        assert ((stor_rates prev_state) = (stor_rates new_state)) as rates_eq.
        {   apply FMap.ext_eq.
            auto. }
        rewrite <- rates_eq.
    reflexivity.
Qed.

Lemma token_keys_invariant_unpool : forall u new_state new_acts prev_state ctx chain,
    receive contract chain ctx prev_state (Some (unpool u)) =
        Ok (new_state, new_acts) -> 
    (FMap.keys (stor_rates new_state)) = 
    (FMap.keys (stor_rates prev_state)).
Proof.
    intros * receive_some.
    is_sp_destruct.
    (* unpool u *)
    pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts receive_some) as unrates_unchanged.
        assert ((stor_rates prev_state) = (stor_rates new_state)) as rates_eq.
        {   apply FMap.ext_eq.
            auto. }
        rewrite <- rates_eq.
    reflexivity.
Qed.

Lemma token_keys_invariant_trade : forall t new_state new_acts prev_state ctx chain,
    receive contract chain ctx prev_state (Some (trade t)) =
        Ok (new_state, new_acts) -> 
    Permutation 
    (FMap.keys (stor_rates new_state))
    (FMap.keys (stor_rates prev_state)).
Proof.
    intros * receive_some.
    is_sp_destruct.
    (* trade t *)
    pose proof (trade_update_rates_formula_pf prev_state chain ctx t new_state new_acts receive_some) 
    as update_rates_formula.
    destruct update_rates_formula as [tokens_neq update_rates_formula].
    destruct update_rates_formula as [old_rate_in other_rates_unchanged].
    (* ... *)
    pose proof (trade_entrypoint_check_2_pf prev_state
    chain ctx t new_state new_acts receive_some) 
    as trade_check.
    do 3 destruct trade_check as [* trade_check].
    destruct trade_check as [_ trade_check]. 
    destruct trade_check as [trade_check _].
    clear x1 x.
    pose proof (FMap.keys_already 
        (token_in_trade t) x0 
        (calc_rate_in
            (get_rate (token_in_trade t)
                (stor_rates prev_state))
            (get_rate (token_out_trade t)
                (stor_rates prev_state)) 
            (qty_trade t)
            (stor_outstanding_tokens prev_state)
            (get_bal (token_in_trade t)
                (stor_tokens_held prev_state)))
        (stor_rates prev_state) trade_check)
    as keys_permuted.
    pose proof (trade_update_rates_pf prev_state chain ctx t new_state new_acts receive_some)
    as update_rates.
    destruct update_rates as [_ update_rates].
    simpl in update_rates.
    (* rewrite <- update_rates in H6 *)
    replace (FMap.add (token_in_trade t)
        (calc_rate_in (get_rate (token_in_trade t) (stor_rates prev_state))
        (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t)
        (stor_outstanding_tokens prev_state) (get_bal (token_in_trade t) (stor_tokens_held prev_state)))
        (stor_rates prev_state))
    with (stor_rates new_state)
    in keys_permuted.
    exact keys_permuted.
Qed.

Definition suml l := fold_right N.add 0 l.

(* and suml commutes with the permutation *)
Lemma map_extract { A B : Type } : forall (a : A) (l : list A) (f : A -> B),
    map f (a :: l) = 
    (f a) :: map f l.
Proof. auto. Qed.

Lemma suml_extract : forall a l,
    suml (a :: l) = 
    a + (suml l).
Proof. auto. Qed.

Lemma in_map : forall { A B : Type } (f : A -> B) l a,
    In a l -> In (f a) (map f l).
Proof.
    intros * H_in.
    induction l as [|x l IH]; auto.
    simpl. simpl in H_in. destruct H_in.
    + left. subst. reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma nodup_permute : forall { A : Type } a (l : list A)
    (eq_dec : forall a b, { a = b } + { a <> b }),
    NoDup l -> 
    In a l -> 
    Permutation l (a :: remove eq_dec a l).
Proof.
    intros A a l eq_dec NoDup_l In_a_l.
    induction NoDup_l as [| b l H_not_in_b_l NoDup_l IH].
    - simpl in In_a_l. contradiction.
    - simpl in In_a_l. destruct In_a_l as [a_eq_b | a_in_l].
        + subst b. simpl. destruct (eq_dec a a).
            * (* apply Permutation_refl. *) admit.
            * contradiction.
        + simpl. destruct (eq_dec a b).
            * subst b. contradiction.
            * apply Permutation_trans with (b :: a :: remove eq_dec a l).
                { (* apply perm_swap. *) admit. }
                { (* apply perm_skip. apply IH. assumption. *) admit. }
Admitted.

Lemma mapped_eq : forall (A B : Type) (f f' : A -> B) (l : list A),
    (forall a, In a l -> f a = f' a) -> 
    map f l = map f' l.
Proof.
    intros * H_in.
    induction l; auto.
    repeat rewrite map_extract.
    rewrite (H_in a (in_eq a l)).
    assert (forall a : A, In a l -> f a = f' a) as H_in_ind.
    {   intros * in_a0.
        exact (H_in a0 (in_cons a a0 l in_a0)). }
    rewrite (IHl H_in_ind).
    reflexivity.
Qed.

Lemma suml_permute_commutes : forall l l',
    Permutation l l' -> suml l = suml l'.
Proof.
    intros. induction H6; auto.
    -   repeat rewrite (suml_extract x).
        rewrite IHPermutation.
        reflexivity.
    -   rewrite (suml_extract y). rewrite (suml_extract x).
        rewrite (suml_extract x). rewrite (suml_extract y).
        repeat rewrite N.add_assoc.
        rewrite (N.add_comm x y).
        reflexivity.
    -   rewrite IHPermutation1.  
        rewrite IHPermutation2.
        reflexivity.
Qed.

Theorem pooled_consistency bstate caddr :
    reachable bstate -> 
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    exists (cstate : State),
    contract_state bstate caddr = Some cstate /\
    (* The sum of all the constituent, pooled tokens, multiplied by their value in terms 
    of pooled tokens, always equals the total number of outstanding pool tokens. *)
    suml (tokens_to_values (stor_rates cstate) (stor_tokens_held cstate)) = 
        (stor_outstanding_tokens cstate).
Proof.
    contract_induction; intros; try exact IH.
    is_sp_destruct.
    (* Please establish the invariant after deployment of the contract *)
    -   (* we use the fact that balances initialize at zero *)
        pose proof (initialized_with_zero_balance_pf chain ctx setup result init_some)
        as zero_bal.
        pose proof (initialized_with_zero_outstanding_pf chain ctx setup result init_some)
        as zero_outstanding.
        rewrite zero_outstanding. clear zero_outstanding.
        unfold tokens_to_values.
        induction (FMap.keys (stor_rates result)); auto.
        rewrite map_cons.
        rewrite zero_bal.
        rewrite N.mul_0_r. 
        auto.
    (* Please reestablish the invariant after a nonrecursive call *)
    -   destruct msg.
        (* first, msg = None *)
        2:{ is_sp_destruct.
            pose proof (none_fails_pf prev_state chain ctx) as failed.
            destruct failed as [err failed].
            rewrite receive_some in failed.
            inversion failed. }
        (* msg = Some m *)
        destruct m.
        (* m = pool *)
        +   is_sp_destruct.
            (* understand how tokens_held has changed *)
            pose proof (pool_increases_tokens_held_pf prev_state chain ctx p new_state new_acts
                receive_some) as bal_update.
            destruct bal_update as [bal_update bals_unchanged].
            (* show all rates are the same *)
            pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts
                receive_some) as rates_update.
            (* show how the outstanding tokens update *)
            pose proof (pool_outstanding_pf prev_state new_state chain ctx p new_acts 
                receive_some) as out_update.
            simpl in out_update.
            (* because the rates are unchanged, summing over them is unchanged *)
            assert (tokens_to_values (stor_rates new_state)  (stor_tokens_held new_state) = 
                    tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state))
            as rates_unchanged.
            {   unfold tokens_to_values.
                rewrite (token_keys_invariant_pool p new_state new_acts prev_state ctx chain receive_some).
                apply map_ext.
                intro t.
                unfold get_rate. rewrite rates_update.
                auto.  }
            rewrite rates_unchanged. clear rates_unchanged.
            (* now separate the sum *)
            assert (suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state)) = 
                    suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held prev_state)) + 
                        get_rate (token_pooled p) (stor_rates prev_state) / 1000000 * qty_pooled p)
            as separate_sum.
            {   unfold tokens_to_values.
                (* some simplifying notation *)
                set (keys_minus_p := (remove token_eq_dec (token_pooled p) (FMap.keys (stor_rates prev_state)))).
                set (tokens_to_values_new := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held new_state) / 1000000).
                set (tokens_to_values_prev := fun (k : token) => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state) / 1000000).
                (* 1. show there's a Permutation with (token_pooled p) at the front *)
                assert (Permutation
                    (FMap.keys (stor_rates prev_state)) 
                    ((token_pooled p) :: keys_minus_p))
                as keys_permuted.
                {   unfold keys_minus_p.
                    (* In (token_pooled p) (FMap.keys (stor_rates prev_state)) *)
                    pose proof (pool_entrypoint_check_2_pf prev_state new_state chain ctx p new_acts receive_some) as rate_exists.
                    destruct rate_exists as [r_x rate_exists_el].
                    apply FMap.In_elements in rate_exists_el.
                    pose proof (in_map fst
                        (FMap.elements (stor_rates prev_state))
                        (token_pooled p, r_x)
                        rate_exists_el)
                    as rate_exists_key. clear rate_exists_el.
                    simpl in rate_exists_key.
                    (* recall NoDup keys *)
                    pose proof (FMap.NoDup_keys (stor_rates prev_state))
                    as nodup_keys.
                    (* since NoDup keys, you can permute *)
                    exact (nodup_permute 
                        (token_pooled p) 
                        (FMap.keys (stor_rates prev_state))
                        token_eq_dec
                        nodup_keys 
                        rate_exists_key). }
                (* Use the permutation to rewrite the LHS first, extracting (token_pooled p) *)
                pose proof 
                    (Permutation_map tokens_to_values_new)
                        (* list 1 *)
                        (FMap.keys (stor_rates prev_state))
                        (* list 2 *)
                        ((token_pooled p) :: keys_minus_p) 
                        (* the previous permutation *)
                        keys_permuted
                as lhs_permute_map.
                (* now that we have that permutation, rewrite in the suml *)
                rewrite (suml_permute_commutes 
                    (map tokens_to_values_new (FMap.keys (stor_rates prev_state)))
                    (map tokens_to_values_new (token_pooled p :: keys_minus_p))
                    lhs_permute_map).
                (* now extract (token_pooled p) *)
                rewrite (map_extract
                    (token_pooled p)
                    keys_minus_p
                    tokens_to_values_new).
                rewrite (suml_extract (tokens_to_values_new (token_pooled p))).
                (* Now separate the sum on the RHS *)
                pose proof 
                    (Permutation_map tokens_to_values_prev)
                        (* list 1 *)
                        (FMap.keys (stor_rates prev_state))
                        (* list 2 *)
                        ((token_pooled p) :: keys_minus_p)
                        (* the previous permutation *)
                        keys_permuted
                as rhs_permute_map.
                (* now that we have that permutation, rewrite in the suml *)
                rewrite (suml_permute_commutes 
                    (map tokens_to_values_prev (FMap.keys (stor_rates prev_state)))
                    (map tokens_to_values_prev (token_pooled p :: keys_minus_p))
                    rhs_permute_map).
                (* now extract (token_pooled p) *)
                rewrite (map_extract
                    (token_pooled p)
                    keys_minus_p
                    tokens_to_values_prev).
                rewrite (suml_extract (tokens_to_values_prev (token_pooled p))).

                (* Now proceed in two parts *)
                (* first the sum of all the unchanged keys *)
                assert 
                    (suml (map tokens_to_values_new keys_minus_p) = 
                     suml (map tokens_to_values_prev keys_minus_p))
                as old_keys_eq.
                {   assert (forall t, In t keys_minus_p -> t <> (token_pooled p))
                    as t_neq.
                    {   intros * H_in.
                        unfold keys_minus_p in H_in.
                        apply in_remove in H_in.
                        destruct H_in as [_ res].
                        exact res. }
                    assert (forall t, In t keys_minus_p -> 
                        tokens_to_values_new t = tokens_to_values_prev t)
                    as tokens_to_vals_eq.
                    {   intros * H_in.
                        apply t_neq in H_in.
                        apply bals_unchanged in H_in.
                        unfold tokens_to_values_new, tokens_to_values_prev.
                        rewrite H_in.
                        reflexivity. }
                    rewrite (mapped_eq
                        token N
                        tokens_to_values_new
                        tokens_to_values_prev
                        keys_minus_p
                        tokens_to_vals_eq).
                    reflexivity. }

                (* then to the key that did change *)
                assert
                    (tokens_to_values_new (token_pooled p) = 
                    tokens_to_values_prev (token_pooled p) + 
                    get_rate (token_pooled p) (stor_rates prev_state) / 1000000 * qty_pooled p)
                as new_key_eq.
                {   unfold tokens_to_values_new, tokens_to_values_prev.
                    (* get the calculation from the specification *)
                    rewrite bal_update.
                    (* rewrite some terms to simplify *)
                    set (t := (token_pooled p)).
                    set (rates := (stor_rates prev_state)).
                    set (t_bal := get_bal t (stor_tokens_held prev_state)).
                    set (q_pooled := qty_pooled p).
                    set (rate_t := get_rate t rates).
                    (* some simple algebraic manipulation *)
                    rewrite (N.mul_add_distr_l).
                    (* !!! TODO this is an inherent problem with the function definitions *)
                        (* TODO this should be abstracted to the specification *)
                        assert ((rate_t * t_bal + rate_t * q_pooled) / 1000000 = (rate_t * t_bal / 1000000 + rate_t * q_pooled / 1000000)) as div_distr. admit.
                        rewrite div_distr. clear div_distr.
                        (* TODO THIS TOO *)
                        assert (rate_t / 1000000 * q_pooled = rate_t * q_pooled / 1000000) as div_comm. admit.
                        rewrite div_comm. clear div_comm.
                    (* END problem with function definitions *)
                    reflexivity. }
                rewrite old_keys_eq. rewrite new_key_eq.
                rewrite <- N.add_assoc.
                rewrite (N.add_comm
                    (get_rate (token_pooled p) (stor_rates prev_state) / 1000000 * qty_pooled p)
                    (suml (map tokens_to_values_prev keys_minus_p))).
                rewrite N.add_assoc.
                reflexivity. }
            rewrite separate_sum. clear separate_sum.
            rewrite out_update.
            rewrite IH.
            reflexivity.
        (* m = unpool *)
        +   is_sp_destruct.
            (* understand how tokens_held has changed *)
            pose proof (unpool_decreases_tokens_held_pf prev_state chain ctx u new_state new_acts
                receive_some) as bal_update.
            destruct bal_update as [bal_update bals_unchanged].
            (* show all rates are the same *)
            pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts
                receive_some) as rates_update.
            (* show how the outstanding tokens update *)
            pose proof (unpool_outstanding_pf prev_state new_state chain ctx u new_acts 
                receive_some) as out_update.
            simpl in out_update.
            rewrite out_update. clear out_update.
            (* because the rates are unchanged, summing over them is unchanged *)
            assert (tokens_to_values (stor_rates new_state)  (stor_tokens_held new_state) = 
                    tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state))
            as rates_unchanged.
            {   unfold tokens_to_values.
                rewrite (token_keys_invariant_unpool u new_state new_acts prev_state ctx chain receive_some).
                apply map_ext.
                intro t.
                unfold get_rate. rewrite rates_update.
                auto.  }
            rewrite rates_unchanged. clear rates_unchanged.
            (* now separate the sum *)
            assert (suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state)) = 
                    suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held prev_state)) - 
                        qty_unpooled u)
            as separate_sum.
            {   unfold tokens_to_values.
                (* some simplifying notation *)
                set (keys_minus_u := (remove token_eq_dec (token_unpooled u) (FMap.keys (stor_rates prev_state)))).
                set (tokens_to_values_new := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held new_state) / 1000000).
                set (tokens_to_values_prev := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state) / 1000000).
                (* 1. show there's a Permutation with (token_pooled p) at the front *)
                assert (Permutation
                    (FMap.keys (stor_rates prev_state)) 
                    ((token_unpooled u) :: keys_minus_u))
                as keys_permuted.
                {   unfold keys_minus_u.
                    (* In (token_pooled p) (FMap.keys (stor_rates prev_state)) *)
                    pose proof (unpool_entrypoint_check_2_pf prev_state new_state chain ctx u new_acts receive_some) as rate_exists.
                    destruct rate_exists as [r_x rate_exists_el].
                    apply FMap.In_elements in rate_exists_el.
                    pose proof (in_map fst
                        (FMap.elements (stor_rates prev_state))
                        (token_unpooled u, r_x)
                        rate_exists_el)
                    as rate_exists_key. clear rate_exists_el.
                    simpl in rate_exists_key.
                    (* recall NoDup keys *)
                    pose proof (FMap.NoDup_keys (stor_rates prev_state))
                    as nodup_keys.
                    (* since NoDup keys, you can permute *)
                    exact (nodup_permute 
                        (token_unpooled u) 
                        (FMap.keys (stor_rates prev_state))
                        token_eq_dec
                        nodup_keys 
                        rate_exists_key). }
                (* Use the permutation to rewrite the LHS first, extracting (token_pooled p) *)
                pose proof 
                    (Permutation_map tokens_to_values_new)
                        (* list 1 *)
                        (FMap.keys (stor_rates prev_state))
                        (* list 2 *)
                        ((token_unpooled u) :: keys_minus_u) 
                        (* the previous permutation *)
                        keys_permuted
                as lhs_permute_map.
                (* now that we have that permutation, rewrite in the suml *)
                rewrite (suml_permute_commutes 
                    (map tokens_to_values_new (FMap.keys (stor_rates prev_state)))
                    (map tokens_to_values_new (token_unpooled u :: keys_minus_u))
                    lhs_permute_map).
                (* now extract (token_pooled p) *)
                rewrite (map_extract
                    (token_unpooled u)
                    keys_minus_u
                    tokens_to_values_new).
                rewrite (suml_extract (tokens_to_values_new (token_unpooled u))).
                (* Now separate the sum on the RHS *)
                pose proof 
                    (Permutation_map tokens_to_values_prev)
                        (* list 1 *)
                        (FMap.keys (stor_rates prev_state))
                        (* list 2 *)
                        ((token_unpooled u) :: keys_minus_u)
                        (* the previous permutation *)
                        keys_permuted
                as rhs_permute_map.
                (* now that we have that permutation, rewrite in the suml *)
                rewrite (suml_permute_commutes 
                    (map tokens_to_values_prev (FMap.keys (stor_rates prev_state)))
                    (map tokens_to_values_prev (token_unpooled u :: keys_minus_u))
                    rhs_permute_map).
                (* now extract (token_pooled p) *)
                rewrite (map_extract
                    (token_unpooled u)
                    keys_minus_u
                    tokens_to_values_prev).
                rewrite (suml_extract (tokens_to_values_prev (token_unpooled u))).

                (* Now proceed in two parts *)
                (* first the sum of all the unchanged keys *)
                assert 
                    (suml (map tokens_to_values_new keys_minus_u) = 
                     suml (map tokens_to_values_prev keys_minus_u))
                as old_keys_eq.
                {   assert (forall t, In t keys_minus_u -> t <> (token_unpooled u))
                    as t_neq.
                    {   intros * H_in.
                        unfold keys_minus_u in H_in.
                        apply in_remove in H_in.
                        destruct H_in as [_ res].
                        exact res. }
                    assert (forall t, In t keys_minus_u -> 
                        tokens_to_values_new t = tokens_to_values_prev t)
                    as tokens_to_vals_eq.
                    {   intros * H_in.
                        apply t_neq in H_in.
                        apply bals_unchanged in H_in.
                        unfold tokens_to_values_new, tokens_to_values_prev.
                        rewrite H_in.
                        reflexivity. }
                    rewrite (mapped_eq
                        token N
                        tokens_to_values_new
                        tokens_to_values_prev
                        keys_minus_u
                        tokens_to_vals_eq).
                    reflexivity. }
                rewrite old_keys_eq. clear old_keys_eq.

                (* then to the key that did change *)
                assert
                    (tokens_to_values_new (token_unpooled u) = 
                    tokens_to_values_prev (token_unpooled u) - qty_unpooled u)
                as new_key_eq.
                {   unfold tokens_to_values_new, tokens_to_values_prev.
                    (* get the calculation from the specification *)
                    rewrite bal_update.
                    (* rewrite some terms to simplify *)
                    set (t := (token_unpooled u)).
                    set (rates := (stor_rates prev_state)).
                    set (t_bal_old := get_bal t (stor_tokens_held prev_state)).
                    set (q_unpooled := qty_unpooled u).
                    set (rate_t := get_rate t rates).
                    (* some simple algebraic manipulation *)
                    rewrite (N.mul_sub_distr_l t_bal_old (q_unpooled * 1_000_000 / rate_t) rate_t).
                    assert ((rate_t * t_bal_old - rate_t * (q_unpooled * 1000000 / rate_t)) / 1000000 = 
                    rate_t * t_bal_old / 1000000 - rate_t * (q_unpooled * 1000000 / rate_t) / 1000000)
                    as div_distr. { admit. }
                    rewrite div_distr. clear div_distr.
                    assert (rate_t * (q_unpooled * 1000000 / rate_t) / 1000000 = q_unpooled) 
                    as div_cancelled. { admit. } 
                    rewrite div_cancelled. clear div_cancelled.
                    reflexivity. }
                rewrite new_key_eq.
                
                (* this is an additional condition required here so that commutativity applies *)
                assert (qty_unpooled u <= tokens_to_values_prev (token_unpooled u))
                as unpooled_leq. {
                    unfold tokens_to_values_prev.
                    exact (unpool_entrypoint_check_3_pf prev_state new_state chain ctx u new_acts receive_some). }
                rewrite (N.add_sub_swap 
                    (tokens_to_values_prev (token_unpooled u))
                    (suml (map tokens_to_values_prev keys_minus_u))
                    (qty_unpooled u)
                    unpooled_leq).
                reflexivity. }
            rewrite separate_sum. clear separate_sum.
            rewrite IH.
            reflexivity.
        (* m = trade *)
        +   is_sp_destruct. clear is_sp.
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
            rewrite out_update. clear out_update.
            (* LHS equals sum over tokens except for tx and ty, plus r_x' * etc , minus r_y * delta_y *)

            (* LHS *)
            (* permute FMap.keys (stor_tokens_held new_state) to have tx :: ty :: keys' *)
                (* for these, rates and balances are all the same as before *)
            
            (* separate LHS into ^^, plus new rate * t_x, minus rate * t_y *)

            (* permute FMap.keys for the OLD suml to MANIPULATE the inductive hypothesis IH *)

            (* then assert NEW decomposed suml = OLD decomposed suml
                <=> new_rate * t_x - rate * t_y = old_rate * t_x - rate * t_y (something like that) *)
                (* ** will require additional assumptions on rate, etc. ** *)

            (* rewrite that assertion; prove by IH *)

            admit. (* TODO algebra *)
    (* Please reestablish the invariant after a recursive call *)
    -   admit. (* TODO probably the same proof *)
    (* solve remaining facts *)
    -   solve_facts.
Admitted.

End AbstractSpecification.