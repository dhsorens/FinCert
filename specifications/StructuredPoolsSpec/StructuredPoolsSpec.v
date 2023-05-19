(**
   This file contains the Specification and Metaspecification of a Structured Pools Contract.
   
   It is organized as follows:

   1. Definitions: 
        - We begin with some auxiliary definitions.

   2. AbstractSpecification: 
        - We define various propositions which must be true of a contract in order for 
            it to be a structured pool
        - We define a predicate `is_structured_pool` on contracts which contains the 
            propositions constituting the specification.

   3. MetaSpecification:
        - We define and prove six properties which are true of any contract satisfying 
          the specification. These include:
            - Demand Sensitivity
            - Nonpathological prices
            - Swap Rate Consistency
            - Zero-Impact Liquidity Change 
            - Arbitrage Sensitivity
            - Pooled Consistency
        - These are designed to justify the correctness and strength of the specification,
          hence the name 'metaspecification'

    The specification is designed so that it can be imported into a Coq module, e.g. to 
    verify a contract correct with respect to this specification, or to reason about 
    structured pools abstractly, possibly in conjunction with other DeFi contracts.
*)

From stdpp Require Import decidable.
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
      We begin with some type and auxiliary type and function definitions which we 
      use for the contract specification.

      The key artefacts here are:
      - the token type 
      - the get_bal function
      - the get_rate function

 * ============================================================================= *)

Section Definitions.
  Context {Base : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

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

Record token := {
    token_address : Address;
    token_id : N
  }.

    (* begin hide *)
    Section STDPPInstances.
    Global Instance token_eq_dec : base.EqDecision token.
    Proof.
        unfold EqDecision, Decision.
        decide equality.
        - apply N.eq_dec.
        - apply address_eqdec.
    Defined.
    Global Program Instance token_countable : countable.Countable token :=
        countable.inj_countable' (fun t => (token_address t, token_id t)) 
            (fun x => let (a, i) := x in Build_token a i) _.
    
    Declare Scope token_scope.
    Notation "x =? y" := (if token_eq_dec x y then true else false)
          (at level 70) : token_scope.
  End STDPPInstances.
  (* end hide *)


Definition exchange_rate := N.

Record transfer_to := {
    to_ : Address;
    transfer_token_id : N;
    amount : N
}.

Record transfer_data := {
    from_ : Address;
    txs : list transfer_to
}.

Record mint_data := {
    mint_owner : Address;
    mint_token_id : N;
    qty : N
  }.
Definition mint : Type := list mint_data.

  (* begin hide *)
  Section Serialization.
    Global Instance transfer_to_serializable : Serializable transfer_to :=
      Derive Serializable transfer_to_rect <Build_transfer_to>.

    Global Instance transfer_data_serializable : Serializable transfer_data :=
      Derive Serializable transfer_data_rect <Build_transfer_data>.

    Global Instance mint_data_serializable : Serializable mint_data :=
      Derive Serializable mint_data_rect <Build_mint_data>.
  End Serialization.
  (* end hide *)
    
(* a function to get a balance from an FMap *)
Definition get_bal (t : token) (tokens_held : FMap token N) := 
    match FMap.find t tokens_held with | Some b => b | None => 0 end.

(* the same function, but named differently for the sake of clarity *)
Definition get_rate (t : token) (rates : FMap token N) : N :=
    match FMap.find t rates with | Some r => r | None => 0 end.

End Definitions.

Section AbstractSpecification.
Context {Base : ChainBase}

(* =============================================================================
 * The Contract Specification `is_structured_pool` :
      We detail a list of propositions of a contract's behavior which must be 
      proven true of a given contract for it to be a correct structured pool contract.
 * ============================================================================= *)

    { Setup Msg State Error : Type }
    { other_entrypoint : Type }
    `{Serializable Setup}  `{Serializable Msg}  `{Serializable State} `{Serializable Error}.

(** Specification of the Msg type:
  - A Pool entrypoint, whose interface is defined by the pool_data type
  - An Unpool entrypoint, whose interface is defined by the unpool_data type
  - A Trade entrypoint, whose interface is defined by the trade_data type
  - Possibly other types
*)

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

(* The Msg typeclass *)
Class Msg_Spec (T : Type) := 
  build_msg_spec {
    pool : pool_data -> T ;
    unpool : unpool_data -> T ;
    trade : trade_data -> T ;
    (* any other potential entrypoints *)
    other : other_entrypoint -> option T ;
}.

(** Specification of the State type:
  The contract state keeps track of:
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

(** Specification of the Setup type:
  To initialize the contract, we need:
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

(* We also specify that the Msg type is fully characterized by its typeclass *)
Definition msg_destruct (contract : Contract Setup Msg State Error) : Prop :=
    forall (m : Msg),
    (exists p, m = pool p) \/
    (exists u, m = unpool u) \/
    (exists t, m = trade t) \/
    (exists o, Some m = other o).


(** Specification of the POOL entrypoint *)

(* A successful call to POOL means that token_pooled has an exchange rate (=> is in T) *)
Definition pool_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (pool (msg_payload))) = Ok(cstate', acts) -> 
    (* an exchange rate exists *)
    exists r_x, 
    FMap.find msg_payload.(token_pooled) (stor_rates cstate) = Some r_x.

(* When the POOL entrypoint is successfully called, it emits a TRANSFER call to the 
    token in storage, with q tokens in the payload of the call *)
Definition pool_emits_txns (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (pool (msg_payload))) = Ok(cstate', acts) -> 
    (* in the acts list there is a transfer call with q tokens as the payload *)
    exists transfer_to transfer_data transfer_payload mint_data mint_payload,
    (* there is a transfer call *)
    let transfer_call := (act_call 
        (* calls the pooled token address *)
        (msg_payload.(token_pooled).(token_address)) 
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
        (stor_pool_token cstate).(token_address) 
        (* with amount 0 *)
        0 
        (* and payload mint_payload *)
        (serialize (FA2Spec.Mint mint_payload))) in 
    (* with has mint_data in the payload *)
    In mint_data mint_payload /\
    (* and the mint data has these properties: *)
    let r_x := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    mint_data.(FA2Spec.qty) = msg_payload.(qty_pooled) * r_x /\
    mint_data.(FA2Spec.mint_owner) = ctx.(ctx_from) /\ 
    (* these are the only emitted transactions *)
    (acts = [ transfer_call ; mint_call ] \/
    acts = [ mint_call ; transfer_call ]).

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
    new_bal = old_bal + qty /\ 
    forall t,
    t <> token -> 
    get_bal t (stor_tokens_held cstate) = 
    get_bal t (stor_tokens_held cstate').

(* And the rates don't change *)
Definition pool_rates_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

(* The outstanding tokens change appropriately *)
Definition pool_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (pool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    let rate_in := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    let qty := msg_payload.(qty_pooled) in 
    stor_outstanding_tokens cstate' = 
    stor_outstanding_tokens cstate + rate_in * qty.


(** Specification of the UNPOOL entrypoint *)

(* We assume an inverse rate function *)
Context { calc_rx_inv : forall (r_x : N) (q : N), N }.

(* A successful call to UNPOOL means that token_pooled has an exchange rate (=> is in T) *)
Definition unpool_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (unpool (msg_payload))) = Ok(cstate', acts) -> 
    (* an exchange rate exists *)
    exists r_x,
    FMap.find msg_payload.(token_unpooled) (stor_rates cstate) = Some r_x.

Definition unpool_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate cstate' chain ctx msg_payload acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (unpool (msg_payload))) = Ok(cstate', acts) -> 
    (* we don't unpool more than we have in reserves *)
    qty_unpooled msg_payload <=
    get_rate (token_unpooled msg_payload) (stor_rates cstate) * get_bal (token_unpooled msg_payload) (stor_tokens_held cstate).

(* When the UNPOOL entrypoint is successfully called, it emits a BURN call to the 
    pool_token, with q in the payload *)
Definition unpool_emits_txns (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to UNPOOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* in the acts list there are burn and transfer transactions *)
    exists burn_data burn_payload transfer_to transfer_data transfer_payload,
    (* there is a burn call in acts *)
    let burn_call := (act_call
        (* calls the pool token address *)
        (stor_pool_token cstate).(token_address)
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
        (msg_payload.(token_unpooled).(token_address))
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
    transfer_to.(FA2Spec.amount) = msg_payload.(qty_unpooled) / r_x /\
    (* and these are the only emitted transactions *)
    (acts = [ burn_call ; transfer_call ] \/
     acts = [ transfer_call ; burn_call ]).


(* When the UNPOOL entrypoint is successfully called, tokens_held goes down appropriately *)
Definition unpool_decreases_tokens_held (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* in cstate', tokens_held has increased at token *)
    let token := msg_payload.(token_unpooled) in
    let r_x := get_rate token (stor_rates cstate) in 
    let qty := calc_rx_inv r_x msg_payload.(qty_unpooled) in
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
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

(* Defines how the UNPOOL entrypoint updates outstanding tokens *)
Definition unpool_outstanding (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx msg_payload acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (Some (unpool msg_payload)) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    let rate_in := get_rate msg_payload.(token_unpooled) (stor_rates cstate) in 
    let qty := msg_payload.(qty_unpooled) in 
    stor_outstanding_tokens cstate' = 
    stor_outstanding_tokens cstate - qty.

(* A successful call to TRADE means that token_in_trade and token_out_trade have exchange 
    rates (=> are in T) *)
Definition trade_entrypoint_check (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* exchange rates exist *)
    exists y r_x r_y,
    ((FMap.find msg_payload.(token_out_trade) (stor_tokens_held cstate) = Some y) /\
    (FMap.find msg_payload.(token_in_trade) (stor_rates cstate) = Some r_x) /\
    (FMap.find msg_payload.(token_out_trade) (stor_rates cstate) = Some r_y)).

(* A successful call to TRADE means that the inputs to the trade calculation are 
    all positive *)
Definition trade_entrypoint_check_2 (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* a successful call *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* exchange rates exist *)
    exists x r_x r_y k,
    ((FMap.find msg_payload.(token_in_trade) (stor_tokens_held cstate) = Some x) /\
    (FMap.find msg_payload.(token_in_trade) (stor_rates cstate) = Some r_x) /\
    (FMap.find msg_payload.(token_out_trade) (stor_rates cstate) = Some r_y) /\
    (stor_outstanding_tokens cstate = k) /\ 
    r_x > 0 /\ r_y > 0 /\ x > 0 /\ k > 0).

(* Specification of the TRADE entrypoint *)
(* We assume the existence of two functions *)
Context { calc_delta_y : forall (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N), N }
        { calc_rx' : forall (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N), N }.

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
    let r_x' := calc_rx' rate_in rate_out q k x in 
    (stor_rates cstate') = 
    (FMap.add (token_in_trade msg_payload)
        (calc_rx' (get_rate (token_in_trade msg_payload) (stor_rates cstate))
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
    let r_x' := calc_rx' rate_in rate_out q k x in 
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
        (msg_payload.(token_in_trade).(token_address))
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
        (msg_payload.(token_out_trade).(token_address))
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

Definition trade_amounts_nonnegative (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the call to TRADE was successful *)
    receive contract chain ctx cstate (Some (trade (msg_payload))) = Ok(cstate', acts) -> 
    (* delta_x and delta_y are nonnegative *)
    let t_x := msg_payload.(token_in_trade) in 
    let t_y := msg_payload.(token_out_trade) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let delta_x := msg_payload.(qty_trade) in 
    let delta_y := calc_delta_y rate_in rate_out delta_x k x in 
    0 <= delta_x /\ 
    0 <= delta_y.

(* Specification of all other entrypoints *)
Definition other_rates_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx o acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (other o) = Ok(cstate', acts) -> 
    (* rates all stay the same *)
    forall t,
    FMap.find t (stor_rates cstate) = FMap.find t (stor_rates cstate').

Definition other_balances_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx o acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (other o) = Ok(cstate', acts) -> 
    (* balances all stay the same *)
    forall t, 
    FMap.find t (stor_tokens_held cstate) = FMap.find t (stor_tokens_held cstate').

Definition other_outstanding_unchanged (contract : Contract Setup Msg State Error) : Prop := 
    forall cstate cstate' chain ctx o acts,
    (* the call to POOL was successful *)
    receive contract chain ctx cstate (other o) = Ok(cstate', acts) -> 
    (* balances all stay the same *)
    (stor_outstanding_tokens cstate) = (stor_outstanding_tokens cstate').

(** Specification of the functions calc_rx' and calc_delta_y *)

(* update_rate function returns positive number if the num, denom are positive *)
Definition update_rate_stays_positive := 
    forall r_x r_y delta_x k x, 
    let r_x' := calc_rx' r_x r_y delta_x k x in
    r_x > 0 ->
    r_x' > 0.

(* r_x' <= r_x *)
Definition rate_decrease := 
    forall r_x r_y delta_x k x, 
    let r_x' := calc_rx' r_x r_y delta_x k x in 
    r_x' <= r_x.

(* the inverse rate function is a right inverse of r_x *)
Definition rates_balance := 
    forall q t rates prev_state, 
    let r_x := get_rate t rates in 
    let x := get_bal t (stor_tokens_held prev_state) in 
    r_x * calc_rx_inv r_x q = q.

Definition rates_balance_2 := 
    forall t prev_state,
    let r_x' := calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
          (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
          (get_bal (token_in_trade t) (stor_tokens_held prev_state)) in 
    let delta_y := calc_delta_y (get_rate (token_in_trade t) (stor_rates prev_state))
             (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
             (get_bal (token_in_trade t) (stor_tokens_held prev_state)) in
    let r_x := get_rate (token_in_trade t) (stor_rates prev_state) in
    let x := get_bal (token_in_trade t) (stor_tokens_held prev_state) in
    let y := get_bal (token_out_trade t) (stor_tokens_held prev_state) in 
    let r_y:= get_rate (token_out_trade t) (stor_rates prev_state) in 
    r_x' * (x + qty_trade t) + r_y * (y - delta_y) = 
    r_x * x + r_y * y.

(* the trade always does slightly worse than predicted *)
Definition trade_slippage := 
    forall r_x r_y delta_x k x, 
    let delta_y := calc_delta_y r_x r_y delta_x k x in 
    r_y * delta_y <= r_x * delta_x.

Definition trade_slippage_2 := 
    forall r_x r_y delta_x k x, 
    let delta_y := calc_delta_y r_x r_y delta_x k x in 
    let r_x' := calc_rx' r_x r_y delta_x k x in 
    r_y * delta_y <= r_x' * delta_x.

(* rates have no positive lower bound *)
Definition arbitrage_lt :=
    forall rate_x rate_y ext k x,
    0 < ext -> 
    ext < rate_x -> 
    exists delta_x,
    calc_rx' rate_x rate_y delta_x k x <= ext.

(* calc_delta_y has no positive upper bound *)
Definition arbitrage_gt :=
    forall rate_x rate_y ext_goal k x,
    rate_x > 0 /\ 
    rate_y > 0 /\ 
    x > 0 /\
    k > 0 ->
    exists delta_x,
    ext_goal <= calc_delta_y rate_x rate_y delta_x k x.


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


(** We amalgamate each proposition in the specification into a single proposition,
    to form the structured pools predicate on contracts *)
Definition is_structured_pool
    (C : Contract Setup Msg State Error) : Prop := 
    none_fails C /\
    msg_destruct C /\
    (* pool entrypoint specification *)
    pool_entrypoint_check C /\
    pool_emits_txns C /\
    pool_increases_tokens_held C /\
    pool_rates_unchanged C /\
    pool_outstanding C /\
    (* unpool entrypoint specification *)
    unpool_entrypoint_check C /\
    unpool_entrypoint_check_2 C /\
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
    trade_amounts_nonnegative C /\
    (* specification of all other entrypoints *)
    other_rates_unchanged C /\
    other_balances_unchanged C /\
    other_outstanding_unchanged C /\
    (* specification of calc_rx' and calc_delta_y *)
    update_rate_stays_positive /\
    rate_decrease /\
    rates_balance /\
    rates_balance_2 /\
    trade_slippage /\
    trade_slippage_2 /\
    arbitrage_lt /\
    arbitrage_gt /\
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
        destruct is_sp' as [msg_destruct_pf is_sp'];
        (* isolate the pool entrypoint specification *)
        destruct is_sp' as [pool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [pool_emits_txns_pf is_sp'];
        destruct is_sp' as [pool_increases_tokens_held_pf is_sp'];
        destruct is_sp' as [pool_rates_unchanged_pf is_sp'];
        destruct is_sp' as [pool_outstanding_pf is_sp'];
        (* isolate the unpool entrypoint specification *)
        destruct is_sp' as [unpool_entrypoint_check_pf is_sp'];
        destruct is_sp' as [unpool_entrypoint_check_2_pf is_sp'];
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
        destruct is_sp' as [trade_emits_transfers_pf is_sp'];
        destruct is_sp' as [trade_tokens_held_update_pf is_sp']; 
        destruct is_sp' as [trade_outstanding_update_pf is_sp'];
        destruct is_sp' as [trade_pricing_pf is_sp'];
        destruct is_sp' as [trade_amounts_nonnegative_pf is_sp'];
        (* isolate the specification of all other entrypoints *)
        destruct is_sp' as [other_rates_unchanged_pf is_sp'];
        destruct is_sp' as [other_balances_unchanged_pf is_sp'];
        destruct is_sp' as [other_outstanding_unchanged_pf is_sp'];
        (* isolate the specification of calc_rx' and calc_delta_y *)
        destruct is_sp' as [update_rate_stays_positive_pf is_sp'];
        destruct is_sp' as [rate_decrease_pf is_sp'];
        destruct is_sp' as [rates_balance_pf is_sp'];
        destruct is_sp' as [rates_balance_2_pf is_sp'];
        destruct is_sp' as [trade_slippage_pf is_sp'];
        destruct is_sp' as [trade_slippage_2_pf is_sp'];
        destruct is_sp' as [arbitrage_lt_pf is_sp'];
        destruct is_sp' as [arbitrage_gt_pf is_sp'];
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


(** Demand Sensitivity :

    A trade for a given token increases its price relative to other constituent tokens, 
    so that higher relative demand corresponds to a higher relative price. 
    Likewise, trading one token in for another decreases the first's relative price in 
    the pool, corresponding to slackened demand. This enforces the classical notion of 
    supply and demand 

    We prove that r_x' > r_x and forall t_z, r_z' = r_z.
*)

(* x decreases relative to z as x => x', z => z' :
    z - x <= z' - x' *)
Definition rel_decr (x z x' z' : N) := 
    ((Z.of_N z) - (Z.of_N x) <= (Z.of_N z') - (Z.of_N x'))%Z.

Lemma rel_decr_lem : forall x x' z : N, 
    x' <= x -> 
    rel_decr x z x' z.
Proof.
    intros * x_leq.
    unfold rel_decr.
    lia.
Qed.

(* y increases relative to x as y => y', x => x' : 
    y - x <= y' - x' *)
Definition rel_incr (y x y' x' : N) := 
    ((Z.of_N y) - (Z.of_N x) <= (Z.of_N y') - (Z.of_N x'))%Z.

Lemma rel_incr_lem : forall x x' y : N, 
    x' <= x -> 
    rel_incr y x y x'.
Proof.
    intros * x_leq.
    unfold rel_incr.
    lia.
Qed.

(** Theorem (Demand Sensitivity):
    Let t_x and t_y, t_x \neq t_y, be tokens in our family with nonzero pooled liquidity and exchange rates r_x, r_y > 0.
    In a trade t_x to t_y, as r_x is updated to r_x', it decereases relative to r_z for all t_z \neq t_x, and r_y strictly increases relative to r_x.
*)

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
    assert (r_x' <= r_x /\
        forall t,
        t <> t_x ->
        get_rate t (stor_rates cstate') = get_rate t (stor_rates cstate))
    as change_lemma.
    {   intros.
        is_sp_destruct.
        rewrite msg_is_trade in successful_txn.
        pose proof (trade_entrypoint_check_pf cstate chain ctx msg_payload
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
                (calc_rx' 
                    (get_rate t_x (stor_rates cstate))
                    (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                    (qty_trade msg_payload)
                    (stor_outstanding_tokens cstate) 
                    (get_bal t_x (stor_tokens_held cstate)))).
            assert (r_x = (get_rate t_x (stor_rates cstate))) as r_x_is_r_x.
            {   unfold get_rate. 
                now replace (FMap.find t_x (stor_rates cstate)) 
                with (Some r_x). }
            now rewrite r_x_is_r_x.
        -   intros t t_neq_tx. 
            unfold get_rate.
            replace (FMap.find t (stor_rates cstate')) with (FMap.find t (stor_rates cstate)).
            2:{ rewrite <- token_in_tx in t_neq_tx.
                apply (eq_sym (other_rates_equal t t_neq_tx)). }
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

(** Nonpathological prices 
    
    As relative prices shift in response to trading activity, a price that starts out nonzero 
    never goes to zero or to a negative value. 

    This is to avoid pathological behavior of zero or negative prices.

    Note, however, that prices can still get arbitrarily close to zero, like in the case 
    of CPMMs.
*)

(** Theorem (Nonpathological Prices):
    For a token t_x in T, if there is a contract state such that r_x > 0, 
    then r_x > 0 holds for all future states of the contract.
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
    -   now apply (IH t_x r_x).
    (* Please establish the invariant after deployment of the contract *)
    -   is_sp_destruct.
        pose proof (initialized_with_positive_rates_pf chain ctx setup result init_some) as init_rates.
        now apply (init_rates t_x r_x).
    (* Please reestablish the invariant after an outgoing action *)
    -   now apply (IH t_x r_x).
    (* Please reestablish the invariant after a nonrecursive call *)
    -   destruct msg.
        (* msg = Some m *)
        +   is_sp_destruct.
            pose proof (msg_destruct_pf m) as msg_destruct.
            destruct msg_destruct as [pool | [unpool | [trade | other]]].
            (* m = pool p : by the specification, pooling does not change exchange rates *)
            *   destruct pool as [p msg_pool].
                rewrite msg_pool in receive_some.
                pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts receive_some t_x) as rates_unchanged.
                now replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H7.
            (* m = unpool p : by the specification, pooling does not change exchange rates *)
            *   destruct unpool as [u msg_unpool].
                rewrite msg_unpool in receive_some.
                pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts receive_some t_x) as rates_unchanged.
                now replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H7.
            (* m = trade p *)
            *   destruct trade as [t msg_trade].
                rewrite msg_trade in receive_some.
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
                    now replace (FMap.find t_x (stor_rates new_state)) 
                    with (FMap.find t_x (stor_rates prev_state))
                    in H7. }
                (* now we have (token_in_trade t) = t_x *)
                (* we need to get r_x from prev_state *)
                assert (exists prev_rx, FMap.find t_x (stor_rates prev_state) = Some prev_rx)
                as exists_prevrx.
                {   pose proof (trade_entrypoint_check_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as prev_rate_lem.
                    do 3 destruct prev_rate_lem as [* prev_rate_lem].
                    destruct prev_rate_lem as [_ prev_rate_lem].
                    destruct prev_rate_lem as [in_lem _].
                    rewrite e in in_lem.
                    exists x0.
                    apply in_lem. }
                destruct exists_prevrx as [prev_rx *].
                (* by IH prev_rx is positive *)
                pose proof (IH t_x prev_rx H8) as prev_pos.
                (* assert that there is some rate r_y of the  *)
                assert (exists r_y, r_x = calc_rx' prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as rx_update.
                {   pose proof (trade_update_rates_formula_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as rx_update.
                    destruct rx_update as [_ rates_update].
                    simpl in rates_update.
                    destruct rates_update as [tx_update _].
                    rewrite <- e in *.
                    rewrite H7 in tx_update.
                    inversion tx_update.
                    exists (get_rate (token_out_trade t) (stor_rates prev_state)).
                    f_equal.
                    unfold get_rate.
                    now replace (FMap.find (token_in_trade t) (stor_rates prev_state))
                    with (Some prev_rx). }
                destruct rx_update as [r_y rx_update].
                (* we call on the result prev_rx > 0 => r_x > 0 *)
                pose proof (update_rate_stays_positive_pf prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as pos_new_rate.
                rewrite <- rx_update in pos_new_rate.
                cbn in pos_new_rate.
                apply (pos_new_rate prev_pos).
            (* finally, now for any other entrypoints *)
            *   destruct other as [o msg_other_op].
                rewrite msg_other_op in receive_some.
                pose proof (other_rates_unchanged_pf prev_state new_state chain ctx o new_acts receive_some t_x) as rates_unchanged.
                now replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H7.
        (* msg = None *)
        +   is_sp_destruct. clear is_sp.
            pose proof (none_fails_pf prev_state chain ctx) as none_fail.
            destruct none_fail as [err none_fail].
            rewrite none_fail in receive_some.
            inversion receive_some.
    (* Please reestablish the invariant after a recursive call *)
    -   destruct msg.
        (* msg = Some m *)
        +   is_sp_destruct.
            pose proof (msg_destruct_pf m) as msg_destruct.
            destruct msg_destruct as [pool | [unpool | [trade | other]]].
            (* m = pool p : by the specification, pooling does not change exchange rates *)
            *   destruct pool as [p msg_pool].
                rewrite msg_pool in receive_some.
                pose proof (pool_rates_unchanged_pf prev_state new_state chain ctx p new_acts receive_some t_x) as rates_unchanged.
                now replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H7.
            (* m = unpool p : by the specification, pooling does not change exchange rates *)
            *   destruct unpool as [u msg_unpool].
                rewrite msg_unpool in receive_some.
                pose proof (unpool_rates_unchanged_pf prev_state new_state chain ctx u new_acts receive_some t_x) as rates_unchanged.
                now replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H7.
            (* m = trade p *)
            *   destruct trade as [t msg_trade].
                rewrite msg_trade in receive_some.
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
                    now replace (FMap.find t_x (stor_rates new_state)) 
                    with (FMap.find t_x (stor_rates prev_state))
                    in H7. }
                (* now we have (token_in_trade t) = t_x *)
                (* we need to get r_x from prev_state *)
                assert (exists prev_rx, FMap.find t_x (stor_rates prev_state) = Some prev_rx)
                as exists_prevrx.
                {   pose proof (trade_entrypoint_check_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as prev_rate_lem.
                    do 3 destruct prev_rate_lem as [* prev_rate_lem].
                    destruct prev_rate_lem as [_ prev_rate_lem].
                    destruct prev_rate_lem as [in_lem _].
                    rewrite e in in_lem.
                    exists x0.
                    apply in_lem. }
                destruct exists_prevrx as [prev_rx *].
                (* by IH prev_rx is positive *)
                pose proof (IH t_x prev_rx H8) as prev_pos.
                (* assert that there is some rate r_y of the  *)
                assert (exists r_y, r_x = calc_rx' prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as rx_update.
                {   pose proof (trade_update_rates_formula_pf prev_state chain ctx t 
                        new_state new_acts receive_some)
                    as rx_update.
                    destruct rx_update as [_ rates_update].
                    simpl in rates_update.
                    destruct rates_update as [tx_update _].
                    rewrite <- e in *.
                    rewrite H7 in tx_update.
                    inversion tx_update.
                    exists (get_rate (token_out_trade t) (stor_rates prev_state)).
                    f_equal.
                    unfold get_rate.
                    now replace (FMap.find (token_in_trade t) (stor_rates prev_state))
                    with (Some prev_rx). }
                destruct rx_update as [r_y rx_update].
                (* we call on the result prev_rx > 0 => r_x > 0 *)
                pose proof (update_rate_stays_positive_pf prev_rx r_y (qty_trade t) (stor_outstanding_tokens prev_state) (get_bal t_x (stor_tokens_held prev_state)))
                as pos_new_rate.
                rewrite <- rx_update in pos_new_rate.
                cbn in pos_new_rate.
                apply (pos_new_rate prev_pos).
            (* finally, now for any other entrypoints *)
            *   destruct other as [o msg_other_op].
                rewrite msg_other_op in receive_some.
                pose proof (other_rates_unchanged_pf prev_state new_state chain ctx o new_acts receive_some t_x) as rates_unchanged.
                now replace (FMap.find t_x (stor_rates new_state))
                with (FMap.find t_x (stor_rates prev_state))
                in H7.
        (* msg = None *)
        +   is_sp_destruct. clear is_sp.
            pose proof (none_fails_pf prev_state chain ctx) as none_fail.
            destruct none_fail as [err none_fail].
            rewrite none_fail in receive_some.
            inversion receive_some.
    (* Please reestablish the invariant after permutation of the action queue *)
    -   now apply (IH t_x r_x).
    -   solve_facts.
Qed.


(** Swap rate consistency : 
    For a token t_x in T and for any delta_x > 0, there is no sequence of trades, beginning and 
    ending with t_x, such that delta_x' > delta_x, where delta_x' is the output quantity of the 
    sequence of trades.
    
    Swap rate consistency means that it is never profitable to trade in a loop, e.g. t_x to t_y, 
    and back to t_x, which is important so that there are never any opportunities for arbitrage 
    internal to the pool.
*)

(* Some results on successive trades *)

(* first a type to describe successive trades *)
Record trade_sequence_type := build_trade_sequence_type {
    seq_chain : ChainState ; 
    seq_ctx : ContractCallContext ; 
    seq_cstate : State ; 
    seq_trade_data : trade_data ;
    seq_res_acts : list ActionBody ;
}.

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

Definition trade_to_rx' (t : trade_sequence_type) := 
    let cstate := seq_cstate t in 
    let token_in := token_in_trade (seq_trade_data t) in 
    let token_out := token_out_trade (seq_trade_data t) in 
    let rate_in := get_rate token_in (stor_rates cstate) in 
    let rate_out := get_rate token_out (stor_rates cstate) in 
    let delta_x := qty_trade (seq_trade_data t) in 
    let k := stor_outstanding_tokens cstate in 
    let x := get_bal token_in (stor_tokens_held cstate) in 
    (* the calculation *)
    calc_rx' rate_in rate_out delta_x k x.

(* a proposition that indicates a list of trades are successive, successful trades *)
Fixpoint are_successive_trades (trade_sequence : list trade_sequence_type) : Prop := 
    match trade_sequence with 
    | [] => True
    | t1 :: l => 
        match l with 
        | [] => 
            (* if the list has one element, it just has to succeed *)
            exists cstate' acts,
            receive contract 
                (seq_chain t1)
                (seq_ctx t1)
                (seq_cstate t1) 
                (Some (trade (seq_trade_data t1))) 
            = Ok(cstate', acts)
        | t2 :: l' => 
            (* the trade t1 goes through, connecting t1 and t2 *)
            receive contract 
                (seq_chain t1) 
                (seq_ctx t1) 
                (seq_cstate t1) 
                (Some (trade (seq_trade_data t1))) 
            = Ok(seq_cstate t2, seq_res_acts t2) /\ 
            (qty_trade (seq_trade_data t2) = trade_to_delta_y t1) /\
            (token_in_trade (seq_trade_data t2) = token_out_trade (seq_trade_data t1)) /\
            (are_successive_trades l)
        end
    end.

Fixpoint leq_list (l : list N) : Prop := 
    match l with 
    | [] => True 
    | h :: tl => 
        match tl with 
        | [] => True 
        | h' :: tl' => (h <= h') /\ leq_list tl 
        end 
    end.

Fixpoint geq_list (l : list N) : Prop := 
    match l with 
    | [] => True 
    | h :: tl => 
        match tl with 
        | [] => True 
        | h' :: tl' => (h >= h') /\ geq_list tl 
        end 
    end.

Lemma rev_injective : forall {A : Type} (l l' : list A), rev l = rev l' -> l = l'.
Proof.
  intros A l l' H_rev.
  rewrite <- (rev_involutive l).
  rewrite <- (rev_involutive l').
  apply f_equal, H_rev.
Qed.

Lemma geq_cons : forall a l,
    geq_list (a :: l) -> 
    geq_list l.
Proof.
    intros * H_geq.
    destruct l as [| a' l]; auto.
    unfold geq_list in *.
    now destruct H_geq as [geq ind_l].
Qed.

Lemma geq_app : forall l l',
    geq_list (l ++ l') -> 
    geq_list l /\ geq_list l'.
Proof.
    intros * H_geq.
    split.
    -   induction l.
        +   now unfold geq_list.
        +   rewrite <- app_comm_cons in H_geq.
            pose proof (IHl (geq_cons a (l ++ l') H_geq)) as geq_l.
            unfold geq_list.
            destruct l; auto.
            unfold geq_list in geq_l.
            split; try assumption.
            clear geq_l.
            rewrite <- app_comm_cons in H_geq.
            unfold geq_list in H_geq.
            now destruct H_geq as [g_geq_n _].
    -   induction l; auto.
        rewrite <- app_comm_cons in H_geq.
        now apply geq_cons in H_geq.
Qed.

Lemma geq_cons_remove_simpl : forall a a' l, 
    geq_list (a :: a' :: l) -> 
    geq_list (a :: l).
Proof.
    intros * H_geq.
    destruct l as [| a'' l].
    -   now unfold geq_list.
    -   unfold geq_list in *.
        destruct H_geq as [a_geq_a' [a'_geq_a'' H_geq]].
        split; auto.
        apply N.ge_le in a_geq_a', a'_geq_a''.
        apply N.le_ge.
        now apply (N.le_trans a'' a' a).
Qed.

Lemma list_decompose {A : Type} : forall (l : list A), l = [] \/ exists l' b, l = (l' ++ [b])%list.
Proof.
  intros.
  destruct (rev l) eqn:H_rev.
  - left. 
    now apply rev_injective.
  - right.
    exists (rev l0), a.
    apply rev_injective.
    rewrite H_rev.
    rewrite rev_unit.
    now rewrite rev_involutive.
Qed.

Lemma geq_transitive : forall l fst lst,
    hd_error l = Some fst -> 
    hd_error (rev l) = Some lst -> 
    geq_list l -> 
    lst <= fst.
Proof.
    intros * hd_fst tl_lst H_geq_list.
    destruct l as [| a l]; try rewrite hd_error_nil in *; try discriminate.
    pose proof (list_decompose l) as l_decompose.
    destruct l_decompose as [one_txn | l_decompose].
    -   rewrite one_txn in *.
        cbn in hd_fst. injection hd_fst. intro a_fst.
        cbn in tl_lst. injection tl_lst. intro a_lst.
        now rewrite <- a_fst, <- a_lst.
    -   destruct l_decompose as [l' [b l_decompose]].
        rewrite l_decompose in *. clear l_decompose.
        cbn in hd_fst. injection hd_fst. intro a_fst.
        assert (b = lst) as b_lst.
        {   cbn in tl_lst.
            rewrite rev_unit in tl_lst.
            rewrite <- app_comm_cons in tl_lst.
            now simpl in tl_lst. }
        (* by induction on l' *)
        induction l'.
        +   rewrite app_nil_l in *.
            unfold geq_list in H_geq_list.
            destruct H_geq_list as [qeg _].
            apply (N.ge_le a b) in qeg.
            now rewrite <- a_fst, <- b_lst.
        +   apply IHl'.
            *   cbn.
                rewrite rev_unit.
                rewrite <- app_comm_cons.
                now simpl.
            *   rewrite <- app_comm_cons in H_geq_list.
                now apply geq_cons_remove_simpl in H_geq_list.
Qed.

Definition trade_to_ry_delta_y (t : trade_sequence_type) := 
    let delta_y := trade_to_delta_y t in 
    let rate_y := get_rate (token_out_trade (seq_trade_data t)) (stor_rates (seq_cstate t)) in 
    rate_y * delta_y.

Lemma mult_strict_mono : forall x y z : N, x <> 0 -> x * y <= x * z -> y <= z.
Proof.
  intros x y z Hx Hz.
  now apply N.mul_le_mono_pos_l in Hz.
Qed.

Lemma hd_transitive { A B : Type } : forall (l : list A) (f : A -> B) fst, 
    hd_error l = Some fst -> 
    hd_error (map f l) = Some (f fst).
Proof.
    intros * fst_is_fst.
    destruct l; try rewrite hd_error_nil in *; try discriminate.
    cbn in fst_is_fst.
    cbn.
    injection fst_is_fst. 
    intro a_eq_fst.
    now rewrite a_eq_fst.
Qed.

Lemma geq_list_is_sufficient : forall trade_sequence t_x t_fst t_last cstate r_x, 
    (* more assumptions *)
    (hd_error trade_sequence) = Some t_fst ->
    (hd_error (rev trade_sequence)) = Some t_last ->
    token_in_trade (seq_trade_data t_fst) = t_x ->
    token_out_trade (seq_trade_data t_last) = t_x -> 
    seq_cstate t_fst = cstate ->
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 ->
    FMap.find t_x (stor_rates cstate) = FMap.find t_x (stor_rates (seq_cstate t_last)) ->
    (* the statement *)
    geq_list (map trade_to_ry_delta_y trade_sequence) ->
    let delta_x := qty_trade (seq_trade_data t_fst) in 
    let delta_x' := trade_to_delta_y t_last in 
    delta_x' <= delta_x.
Proof.
    intros * fst_txn lst_txn from_tx to_tx start_cstate rx_exists one_tx_txn H_geq_list *.
    is_sp_destruct.
    (* a lemma *)
    assert (forall t,
        let r_x := get_rate (token_in_trade (seq_trade_data t)) (stor_rates (seq_cstate t)) in 
        let r_y := get_rate (token_out_trade (seq_trade_data t)) (stor_rates (seq_cstate t)) in 
        let delta_x := qty_trade (seq_trade_data t) in 
        let delta_y := trade_to_delta_y t in 
        r_y * delta_y <= r_x * delta_x)
    as trade_slippage.
    {   intro.
        cbn.
        unfold trade_to_delta_y.
        apply trade_slippage_pf. }
    destruct trade_sequence; inversion fst_txn.
    destruct trade_sequence.
    (* the case that this is a trade t_x -> t_x *)
    {   (* delta_x' < r_x / r_x delta_x => delta_x' < delta_x *)
        rename H8 into tx_is_fst.
        assert (t = t_last) as tx_is_last.
        { cbn in lst_txn. injection lst_txn. auto. }
        unfold delta_x', delta_x.
        rewrite <- tx_is_fst, <- tx_is_last.
        pose proof (trade_slippage t) as trade_lt. cbn in trade_lt.
        rewrite <- from_tx in to_tx.
        rewrite <- tx_is_fst, <- tx_is_last in *.
        rewrite to_tx in trade_lt.
        rewrite <- from_tx in rx_exists.
        destruct rx_exists as [rx_exists rx_gt0].
        rewrite <- start_cstate in rx_exists.
        unfold get_rate in trade_lt.
        replace (FMap.find (token_in_trade (seq_trade_data t)) (stor_rates (seq_cstate t)))
        with (Some r_x)
        in trade_lt.
        assert (r_x <> 0) as rate_neq_0.
        {   apply N.neq_0_lt_0.
            now apply N.gt_lt. }
        eapply mult_strict_mono; now try exact rate_neq_0. }
    (* now, the case of t_x -> t_y -> [...] -> t_x *)
    (* deduce that r_x' delta_x' <= r_y delta_y *)
    set (r_x' := get_rate t_x (stor_rates (seq_cstate t_last))).
    set (t_y := token_out_trade (seq_trade_data t_fst)).
    set (r_y := get_rate t_y (stor_rates (seq_cstate t_fst))).
    set (delta_y := trade_to_delta_y t_fst).
    assert (r_x' * delta_x' <= r_y * delta_y)
    as H_y_x'.
    {   pose proof (hd_transitive (rev (t :: t0 :: trade_sequence)) trade_to_ry_delta_y t_last lst_txn) 
        as rev_map_head. 
        rewrite map_rev in rev_map_head.
        pose proof (geq_transitive 
            (map trade_to_ry_delta_y (t :: t0 :: trade_sequence))
            (trade_to_ry_delta_y t_fst) 
            (trade_to_ry_delta_y t_last)
            (hd_transitive (t :: t0 :: trade_sequence) trade_to_ry_delta_y t_fst fst_txn) 
            rev_map_head
            H_geq_list)
        as geq_trans.
        unfold trade_to_ry_delta_y in geq_trans.
        unfold r_x', delta_x', r_y, delta_y, t_y.
        now rewrite <- to_tx. }
    (* recall r_y delta_y <= r_x' delta_x *)
    assert (r_y * delta_y <= r_x' * delta_x)
    as H_x_y.
    {   destruct rx_exists as [rx_exists rx_gt0].
        replace (FMap.find t_x (stor_rates cstate))
        with (FMap.find t_x (stor_rates (seq_cstate t_last)))
        in rx_exists.
        unfold r_x', get_rate.
        replace (FMap.find t_x (stor_rates (seq_cstate t_last)))
        with (Some r_x).
        pose proof (trade_slippage t_fst) as trade_lemma.
        cbn in trade_lemma.
        unfold r_y, delta_y, delta_x.
        replace r_x 
        with (get_rate (token_in_trade (seq_trade_data t_fst)) (stor_rates (seq_cstate t_fst))).
        2:{ unfold get_rate.
            replace (seq_cstate t_fst) with cstate.
            replace (token_in_trade (seq_trade_data t_fst)) with t_x.
            replace (FMap.find t_x (stor_rates cstate)) 
            with (FMap.find t_x (stor_rates (seq_cstate t_last))).
            now replace (FMap.find t_x (stor_rates (seq_cstate t_last)))
            with (Some r_x). }
        assumption. }
    (* so r_x' delta_x' <= r_x' delta_x *)
    pose proof (N.le_trans (r_x' * delta_x') (r_y * delta_y) (r_x' * delta_x) H_y_x' H_x_y)
    as H_x'_x.
    (* giving that delta_x' <= delta_x *)
    assert (r_x' <> 0) as rate_neq_0.
    {   destruct rx_exists as [rx_exists rx_gt0].
        replace (FMap.find t_x (stor_rates cstate))
        with (FMap.find t_x (stor_rates (seq_cstate t_last)))
        in rx_exists.
        unfold r_x', get_rate.
        now replace (FMap.find t_x (stor_rates (seq_cstate t_last)))
        with (Some r_x). }
    now eapply mult_strict_mono.
Qed.

Lemma swap_rate_lemma : forall trade_sequence, 
    (* if this is a list of successive trades *)
    are_successive_trades trade_sequence -> 
    (* then  *)
    geq_list (map trade_to_ry_delta_y trade_sequence).
Proof.
    intros * trades_successive.
    induction trade_sequence as [| t1 trade_sequence IHtrade_sequence]; auto.
    assert (forall a l, are_successive_trades (a :: l) -> are_successive_trades l)
    as successive_iter.
    {   intros *.
        destruct l.
        -   intro.
            unfold are_successive_trades. 
            auto.
        -   intro outer_successive.
            unfold are_successive_trades in outer_successive.
            destruct outer_successive as [H_recv [H_qty H_iter]].
            now unfold are_successive_trades. }
    apply successive_iter in trades_successive as successive_itered.
    apply IHtrade_sequence in successive_itered.
    rewrite map_cons.
    destruct trade_sequence as [| t2 trade_sequence]; auto.
    rewrite map_cons.
    assert (forall a b l, a >= b /\ geq_list (b :: l) -> geq_list (a :: b :: l))
    as geq_conds.
    { auto. }
    apply geq_conds.
    rewrite map_cons in successive_itered.
    split; auto.
    (* some simplifying notation *)
    set (t_x := token_in_trade (seq_trade_data t1)).
    set (r_x := get_rate t_x (stor_rates (seq_cstate t1))).
    set (r_x' := trade_to_rx' t1).
    set (delta_x := qty_trade (seq_trade_data t1)).
    set (t_y := token_out_trade (seq_trade_data t1)).
    set (r_y := get_rate t_y (stor_rates (seq_cstate t1))).
    set (r_y' := trade_to_rx' t2).
    set (delta_y := trade_to_delta_y t1).
    set (t_z := token_out_trade (seq_trade_data t2)).
    set (r_z := get_rate t_z (stor_rates (seq_cstate t2))).
    set (delta_z := trade_to_delta_y t2).
    (* a lemma *)
    assert (forall t, 
        let t_x := token_in_trade (seq_trade_data t) in 
        let t_y := token_out_trade (seq_trade_data t) in 
        let r_x' := trade_to_rx' t in 
        let r_y := get_rate t_y (stor_rates (seq_cstate t)) in 
        let delta_x := qty_trade (seq_trade_data t) in 
        let delta_y := trade_to_delta_y t in 
        r_y * delta_y <= r_x' * delta_x)
    as trade_slippage_2.
    {   is_sp_destruct.
        intros.
        unfold r_y0, delta_y0, r_x'0, delta_x0, trade_to_delta_y, trade_to_rx'.
        apply trade_slippage_2_pf. }
    (* recall r_z * delta_z <= r_y' * delta_y (for t_2) *)
    assert (r_z * delta_z <= r_y' * delta_y) as le_1.
    {   pose proof (trade_slippage_2 t2) as trade_leq.
        cbn in trade_leq.
        unfold r_z, t_z, delta_z, r_y', t_y, delta_y.
        cbn in trades_successive. destruct trades_successive as [recv_some [qty_traded [in_out_eq _]]].
        now rewrite <- qty_traded. }
    (* recall r_y * delta_y <= r_x' * delta_x (for t_1) *)
    assert (r_y * delta_y <= r_x' * delta_x) as le_2.
    {   pose proof (trade_slippage_2 t1) as trade_leq.
        cbn in trade_leq.
        unfold r_y, t_y, delta_y, r_x', t_x, delta_x.
        cbn in trades_successive. destruct trades_successive as [recv_some [qty_traded [in_out_eq _]]].
        now rewrite <- qty_traded. }
    (* recall r_y' < r_y *)
    assert (r_y' <= r_y) as rates_decr.
    {   cbn in trades_successive. 
        destruct trades_successive as [recv_some [qty_traded [in_out_eq _]]].
        assert (get_rate t_y (stor_rates (seq_cstate t1)) 
                = get_rate t_y (stor_rates (seq_cstate t2)))
        as ry_unchanged_in_t1.
        {   is_sp_destruct.
            pose proof (trade_update_rates_formula_pf (seq_cstate t1) (seq_chain t1) (seq_ctx t1) (seq_trade_data t1) (seq_cstate t2)(seq_res_acts t2) recv_some)
            as rates_change.
            destruct rates_change as [token_neq [_ rates_unchange]].
            unfold t_y, get_rate.
            pose proof (rates_unchange (token_out_trade (seq_trade_data t1)) (not_eq_sym token_neq))
            as rates_unchange.
            now replace (FMap.find (token_out_trade (seq_trade_data t1)) (stor_rates (seq_cstate t2)))
            with (FMap.find (token_out_trade (seq_trade_data t1)) (stor_rates (seq_cstate t1))). }
        unfold t_y in ry_unchanged_in_t1.
        rewrite <- in_out_eq in ry_unchanged_in_t1.
        unfold r_y, r_y', t_y, trade_to_rx'.
        rewrite <- in_out_eq.
        rewrite ry_unchanged_in_t1.
        is_sp_destruct.
        apply rate_decrease_pf. }
    (* so r_z * delta_z <= r_y' * delta_y <= r_y * delta_y *)
    assert (r_y' * delta_y <= r_y * delta_y) as le_mid.
    {   apply (N.mul_le_mono_nonneg_r r_y' r_y); try assumption.
        cbn in trades_successive. 
        destruct trades_successive as [recv_some [qty_traded [in_out_eq _]]].
        is_sp_destruct.
        pose proof (trade_amounts_nonnegative_pf (seq_cstate t1) (seq_chain t1) (seq_ctx t1)
        (seq_trade_data t1) (seq_cstate t2) (seq_res_acts t2) recv_some)
        as trades_nonneg.
        destruct trades_nonneg as [_ dy_nonneg].
        now unfold delta_y, trade_to_delta_y. }
    assert (r_z * delta_z <= r_y * delta_y) as le_comp.
    {   apply (N.le_trans (r_z * delta_z) (r_y' * delta_y) (r_y * delta_y) le_1 le_mid). }
    unfold trade_to_ry_delta_y.
    unfold r_z, t_z, delta_z, r_y, t_y, delta_y in le_comp.
    now apply N.le_ge.
Qed.

(** Theorem (Swap Rate Consistency): 
    Let t_x be a token in our family with nonzero pooled liquidity and r_x > 0.
    Then for any delta_x > 0 there is no sequence of trades, beginning and ending with 
    t_x, such that delta_x' > delta_x, where delta_x' is the output quantity 
    of the sequence of trades.
*)

Theorem swap_rate_consistency bstate cstate : 
    (* Let t_x be a token with nonzero pooled liquidity and rate r_x > 0 *)
    forall t_x r_x x,
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 -> 
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
    qty_trade (seq_trade_data t_fst) = delta_x -> 
    (* the last trade is to t_x *)
    token_out_trade (seq_trade_data t_last) = t_x -> 
    FMap.find t_x (stor_rates cstate) = FMap.find t_x (stor_rates (seq_cstate t_last)) ->
    (* delta_x', the output of the last trade, is never larger than delta_x. *)
    let delta_x' := trade_to_delta_y t_last in 
    delta_x' <= delta_x.
Proof.
    intros * H_rate H_held * dx_geq_0 trades_successive fst_txn lst_txn start_bstate start_cstate from_tx trade_delta_x to_tx one_tx_txn *.
    unfold delta_x'. rewrite <- trade_delta_x.
    apply (geq_list_is_sufficient trade_sequence t_x t_fst t_last cstate r_x); auto.
    now apply swap_rate_lemma.
Qed.


(** Zero-Impact Liquidity Change :
    The quoted price of trades is unaffected by depositing or withdrawing liquidity
*)

(** Theorem (Zero-Impact Liquidity Change)
    The quoted price of trades is unaffected by calling `pool` and `unpool`.
*)
Theorem zero_impact_liquidity_change :
    (* Consider the quoted price of a trade t_x to t_y at cstate, *)
    forall cstate t_x t_y r_x r_y,
    FMap.find t_x (stor_rates cstate) = Some r_x ->
    FMap.find t_y (stor_rates cstate) = Some r_y ->
    let quoted_price := r_x / r_y in 
    (* and a successful POOL or UNPOOL action. *)
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
        now rewrite rx_eq, ry_eq.
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
        now rewrite rx_eq, ry_eq.
Qed.

(** Arbitrage Sensitivity :

    If an external, demand-sensitive market prices a constituent token differently from 
    the structured pool, a sufficiently large arbitrage transaction will equalize 
    the prices of the external market and the structured pool, or deplete the pool.

    In our case, this happens because prices adapt through trades due to demand 
    sensitivity or the pool depletes in that particular token.
*)


(** Theorem (Arbitrage Sensitivity):
    Let t_x be a token in our family with nonzero pooled liquidity and r_x > 0.
    If an external, demand-sensitive market prices t_x differently from the structured pool, 
    then assuming sufficient liquidity,  with a sufficiently large transaction either the 
    price of t_x in the structured pool converges with the external market, or the trade 
    depletes the pool of t_x.
*)
Theorem arbitrage_sensitivity :
    forall cstate t_x r_x x,
    (* t_x is a token with nonzero pooled liquidity *)
    FMap.find t_x (stor_rates cstate) = Some r_x /\ r_x > 0 /\ 
    FMap.find t_x (stor_tokens_held cstate) = Some x /\ x > 0 ->
    (* we consider some external price *)    
    forall external_price,
    0 < external_price -> 
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
    let t_y := token_out_trade msg_payload in 
    let r_y := get_rate t_y (stor_rates cstate) in 
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let y := get_bal t_y (stor_tokens_held cstate) in 
    let balances := (stor_tokens_held cstate) in 
    let k := (stor_outstanding_tokens cstate) in 
    get_bal t_y balances <= calc_delta_y r_x r_y trade_qty k x).
Proof.
    intros * liquidity * ext_pos * successful_trade msg_is_trade tx_trade_in.
    (* show that the trade has equalized arbitrage *)
    split.
    (* the external market prices lower than the contract *)
    -   is_sp_destruct.
        intro ext_lt_rx.
        (* the strategy is to buy low (externally), sell high (internally) *)
        pose proof arbitrage_lt_pf r_x (get_rate (token_out_trade msg_payload) (stor_rates cstate)) external_price  (stor_outstanding_tokens cstate) (get_bal t_x 
            (stor_tokens_held cstate)) ext_pos ext_lt_rx
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
        (calc_rx' (get_rate (token_in_trade msg_payload) (stor_rates cstate))
           (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
           (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)))).
        assert (r_x = (get_rate (token_in_trade msg_payload) (stor_rates cstate)))
        as rx_got_rate.
        {   unfold get_rate.
            destruct liquidity as [rx_l _].
            rewrite tx_trade_in in rx_l.
            now replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
            with (Some r_x). }
        rewrite rx_got_rate in new_rate_lt.
        rewrite <- traded_qty in new_rate_lt.
        rewrite tx_trade_in in new_rate_lt.
        apply (N.le_ge (calc_rx' (get_rate (token_in_trade msg_payload) (stor_rates cstate))
        (get_rate (token_out_trade msg_payload) (stor_rates cstate)) (qty_trade msg_payload)
        (stor_outstanding_tokens cstate) (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate))) external_price) in new_rate_lt.
        exact new_rate_lt.
    (* the external market prices higher than the contract *)
    -   is_sp_destruct.
        intro ext_gt_rx.
        (* the strategy is to buy low (internally), sell high (externally) *)
        set (t_y := token_out_trade msg_payload).
        rewrite msg_is_trade in successful_trade.
        destruct (trade_entrypoint_check_pf cstate chain ctx msg_payload cstate' 
        acts successful_trade) as [y [_ [r_y [bal_y [_ rate_y]]]]].
        destruct liquidity as [rate_x [rx_gt_0 [bal_x bal_gt_0]]].
        destruct (trade_entrypoint_check_2_pf cstate chain ctx msg_payload cstate' 
        acts successful_trade)
        as [x0 [rx0 [ry0 [k0 [is_x [is_rx [is_ry [is_k gt0]]]]]]]].
        replace (FMap.find (token_out_trade msg_payload) (stor_rates cstate)) 
        with (Some r_y) in is_ry.
        rewrite tx_trade_in in rate_x, bal_x.
        replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate)) 
        with (Some r_x) in is_rx.
        replace (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate)) 
        with (Some x) in is_x.
        replace k0 with (stor_outstanding_tokens cstate) in gt0.
        replace x0 with x in gt0 by (injection is_x; auto).
        replace ry0 with r_y in gt0 by (injection is_ry; auto).
        replace rx0 with r_x in gt0 by (injection is_rx; auto).
        destruct (arbitrage_gt_pf r_x r_y y (stor_outstanding_tokens cstate) x gt0) 
        as [dx calc_dy].
        exists dx.
        intro deplete_store.
        right.
        destruct (trade_tokens_held_update_pf cstate chain ctx msg_payload cstate' acts successful_trade) as [new_bal_y [_ _]].
        unfold get_bal, get_rate in new_bal_y.
        unfold get_bal, t_y.
        replace (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        with (Some y) in new_bal_y.
        replace (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        with (Some r_y) in new_bal_y.
        replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        with (Some r_x) in new_bal_y.
        replace (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        with (Some x) in new_bal_y.
        replace (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        with (Some y).
        rewrite tx_trade_in.
        replace (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        with (Some x).
        unfold get_rate.
        now replace (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        with (Some r_y).
Qed.


(* Pooled Consistency:
    The number of outstanding pool tokens is equal to the value, in pool tokens, of all 
    constituent tokens held by the contract.

    Mathematically, the sum of all the constituent, pooled tokens, multiplied by their value in 
    terms of pooled tokens, always equals the total number of outstanding pool tokens. 

    This means that the pool token is never under- or over-collateralized, and is similar to 
    standard AMMs, where the LP token is always fully backed, representing a percentage of the 
    liquidity pool.
*)

(* map over the keys *)
Definition tokens_to_values (rates : FMap token exchange_rate) (tokens_held : FMap token N) : list N := 
    List.map
        (fun k => 
            let rate := get_rate k rates in 
            let qty_held := get_bal k tokens_held in 
            rate * qty_held)
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
    { now apply FMap.ext_eq. }
    now rewrite <- rates_eq.
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
    { now apply FMap.ext_eq. }
    now rewrite <- rates_eq.
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
    destruct (trade_update_rates_formula_pf prev_state chain ctx t new_state new_acts receive_some) as [tokens_neq update_rates_formula].
    destruct update_rates_formula as [old_rate_in other_rates_unchanged].
    (* ... *)
    pose proof (trade_entrypoint_check_pf prev_state
    chain ctx t new_state new_acts receive_some) 
    as trade_check.
    do 3 destruct trade_check as [* trade_check].
    destruct trade_check as [_ trade_check]. 
    destruct trade_check as [trade_check _].
    clear x1 x.
    pose proof (FMap.keys_already 
        (token_in_trade t) x0 
        (calc_rx'
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
    destruct (trade_update_rates_pf prev_state chain ctx t new_state new_acts receive_some) 
    as [_ update_rates].
    simpl in update_rates.
    (* rewrite <- update_rates in H6 *)
    replace (FMap.add (token_in_trade t)
        (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
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
    + left. now subst.
    + right. now apply IH.
Qed.

Lemma remove_permute : forall { A : Type } a b (l : list A)
    (eq_dec : forall a b, { a = b } + { a <> b }),
    a <> b ->
    (a :: remove eq_dec b l) = (remove eq_dec b (a :: l)).
Proof.
    intros * a_neq_b.
    unfold remove.
    apply not_eq_sym in a_neq_b.
    now destruct (eq_dec b a); try contradiction.
Qed.

Lemma nodup_permute : forall { A : Type } a (l : list A)
    (eq_dec : forall a b, { a = b } + { a <> b }),
    NoDup l -> 
    In a l -> 
    Permutation l (a :: remove eq_dec a l).
Proof.
    intros * nodup_l in_a_l.
    induction l; cbn in in_a_l; try contradiction.
    (* establish NoDup l *)
    apply NoDup_cons_iff in nodup_l as nodup_l'.
    destruct nodup_l' as [not_in_a0_l nodup_l'].
    destruct in_a_l as [a0_eq_a | in_a_l].
    (* a0 = a *)
    -   rewrite a0_eq_a in *.
        replace (remove eq_dec a (a :: l))
        with l.
        2:{ unfold remove.
            destruct (eq_dec a a); try contradiction.
            pose proof (notin_remove eq_dec l a not_in_a0_l) as remove_eq.
            unfold remove in remove_eq.
            now rewrite remove_eq. }
        reflexivity.
    (* In a l *)
    -   destruct (eq_dec a a0) as [a_eq_a0 | a_neq_a0].
        +   rewrite <- a_eq_a0 in *.
            replace (remove eq_dec a (a :: l))
            with l.
            2:{ unfold remove.
                destruct (eq_dec a a); try contradiction. }
            apply Permutation_refl.
        +   rewrite <- remove_permute; try exact (not_eq_sym a_neq_a0).
            pose (perm_swap a a0 (remove eq_dec a l)) as perm_intermediate1.
            pose (perm_skip a0 (IHl nodup_l' in_a_l)) as perm_intermediate2.
            apply (perm_trans perm_intermediate2 perm_intermediate1).
Qed.

Lemma not_in_split : forall {A : Type} (a : A) (l1 l2 : list A),
  ~ In a (l1 ++ l2) -> ~ In a l1 /\ ~ In a l2.
Proof.
  intros A a l1 l2 H_nin.
  split; intros Hcontra; apply H_nin; apply in_or_app; [left|right]; assumption.
Qed.

Lemma nodup_remove_mid : forall { A : Type } a (l1 l2 : list A)
(eq_dec : forall a b, { a = b } + { a <> b }),
    NoDup (l1 ++ l2) /\ ~ In a (l1 ++ l2) -> 
    ((remove eq_dec a (l1 ++ a :: l2)) = l1 ++ l2)%list.
Proof.
    intros * hyp.
    destruct hyp as [nodup_concat not_in].
    rewrite remove_app.
    apply not_in_split in not_in. destruct not_in as [not_in_l1 not_in_l2].
    rewrite (notin_remove eq_dec l1 a not_in_l1).
    rewrite remove_cons.
    now rewrite (notin_remove eq_dec l2 a not_in_l2).
Qed.

Lemma nodup_remove : forall { A : Type } a (l : list A)
    (eq_dec : forall a b, { a = b } + { a <> b }),
    NoDup l -> 
    NoDup (remove eq_dec a l).
Proof.
    intros * nodup_l.
    destruct (in_dec eq_dec a l).
    -   apply in_split in i.
        destruct i as [l1 [l2 i]].
        rewrite i.
        rewrite i in nodup_l.
        apply NoDup_remove in nodup_l.
        rewrite nodup_remove_mid.
        now destruct nodup_l.
        assumption.
    -   now rewrite (notin_remove eq_dec l a n).
Qed.

Lemma remove_permute_2 : forall { A : Type } a (l1 l2 : list A)
    (eq_dec : forall a b, { a = b } + { a <> b }),
    NoDup l1 -> 
    NoDup l2 ->
    Permutation l1 l2 -> 
    Permutation (remove eq_dec a l1) (remove eq_dec a l2).
Proof.
    intros * nodup_l1 nodup_l2 perm.
    destruct (in_dec eq_dec a l1) as [in_l1 | not_in_l1].
    (* a is in l1 *)
    -   (* prove in l2 *)
        pose proof (Permutation_in a perm in_l1)
        as in_l2.
        (* decompose l1 and l2 because in and nodup *)
        apply in_split in in_l1 as l1_decompose.
        destruct l1_decompose as [l1' [l1'' l1_split]].
        apply in_split in in_l2 as l2_decompose.
        destruct l2_decompose as [l2' [l2'' l2_split]].
        rewrite l1_split, l2_split.
        (* remove a explicitly *)
        rewrite l1_split in nodup_l1.
        rewrite l2_split in nodup_l2.
        apply NoDup_remove in nodup_l1, nodup_l2.
        (* retain permutation *)
        repeat rewrite nodup_remove_mid; try assumption.
        apply (Permutation_app_inv l1' l1'' l2' l2'' a).
        rewrite <- l1_split.
        now rewrite <- l2_split.
    (* a not in l1 *)
    -   (* prove not in l2 *)
        destruct (in_dec eq_dec a l2) as [in_l2 | not_in_l2].
        apply Permutation_sym in perm.
        pose proof (Permutation_in a perm in_l2)
        as in_l1.
        contradiction.
        (* show equality with remove *)
        rewrite (notin_remove eq_dec l1 a not_in_l1).
        now rewrite (notin_remove eq_dec l2 a not_in_l2).
Qed.

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
    now rewrite (IHl H_in_ind).
Qed.

Lemma suml_permute_commutes : forall l l',
    Permutation l l' -> suml l = suml l'.
Proof.
    intros. induction H7; auto.
    -   repeat rewrite (suml_extract x).
        now rewrite IHPermutation.
    -   rewrite (suml_extract y). rewrite (suml_extract x).
        rewrite (suml_extract x). rewrite (suml_extract y).
        repeat rewrite N.add_assoc.
        now rewrite (N.add_comm x y).
    -   rewrite IHPermutation1.  
        now rewrite IHPermutation2.
Qed.

(** Theorem (Pooled Consistency):
    The following equation always holds: 
        Sum_{t_x} r_x x = k
*)

Theorem pooled_consistency bstate caddr :
    reachable bstate -> 
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    exists (cstate : State),
    contract_state bstate caddr = Some cstate /\
    (* The sum of all the constituent, pooled tokens, multiplied by their value in terms 
    of pooled tokens, always equals the total number of outstanding pool tokens. *)
    suml (tokens_to_values (stor_rates cstate) (stor_tokens_held cstate)) = (stor_outstanding_tokens cstate).
Proof.
    contract_induction; intros; try exact IH.
    is_sp_destruct.
    (* Please establish the invariant after deployment of the contract *)
    -   (* we use the fact that balances initialize at zero *)
        pose proof (initialized_with_zero_balance_pf chain ctx setup result init_some)
        as zero_bal.
        pose proof (initialized_with_zero_outstanding_pf chain ctx setup result init_some)
        as zero_outstanding.
        rewrite zero_outstanding. 
        clear zero_outstanding.
        unfold tokens_to_values.
        induction (FMap.keys (stor_rates result)); auto.
        rewrite map_cons.
        rewrite zero_bal.
        now rewrite N.mul_0_r.
    (* Please reestablish the invariant after a nonrecursive call *)
    -   destruct msg.
        (* first, msg = None *)
        2:{ is_sp_destruct.
            destruct (none_fails_pf prev_state chain ctx) as [err failed].
            rewrite receive_some in failed.
            inversion failed. }
        (* msg = Some m *)
        is_sp_destruct.
        destruct (msg_destruct_pf m) as [pool | [unpool | [trade | other]]].
        (* m = pool *)
        +   destruct pool as [p msg_pool].
            rewrite msg_pool in receive_some.    
            (* understand how tokens_held has changed *)
            destruct (pool_increases_tokens_held_pf prev_state chain ctx p new_state new_acts
            receive_some) as [bal_update bals_unchanged].
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
                unfold get_rate. 
                now rewrite rates_update. }
            rewrite rates_unchanged. clear rates_unchanged.
            (* now separate the sum *)
            assert (suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state)) = 
                    suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held prev_state)) + get_rate (token_pooled p) (stor_rates prev_state) * qty_pooled p)
            as separate_sum.
            {   unfold tokens_to_values.
                (* some simplifying notation *)
                set (keys_minus_p := (remove token_eq_dec (token_pooled p) 
                    (FMap.keys (stor_rates prev_state)))).
                set (tokens_to_values_new := fun k : token => 
                    get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held new_state)).
                set (tokens_to_values_prev := fun (k : token) => 
                    get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state)).
                (* 1. show there's a Permutation with (token_pooled p) at the front *)
                assert (Permutation
                    (FMap.keys (stor_rates prev_state)) 
                    ((token_pooled p) :: keys_minus_p))
                as keys_permuted.
                {   unfold keys_minus_p.
                    (* In (token_pooled p) (FMap.keys (stor_rates prev_state)) *)
                    destruct (pool_entrypoint_check_pf prev_state new_state chain 
                    ctx p new_acts receive_some) as [r_x rate_exists_el].
                    apply FMap.In_elements in rate_exists_el.
                    pose proof (in_map fst
                        (FMap.elements (stor_rates prev_state))
                        (token_pooled p, r_x)
                        rate_exists_el)
                    as rate_exists_key. 
                    clear rate_exists_el.
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
                        now rewrite H_in. }
                    now rewrite (mapped_eq
                        token N
                        tokens_to_values_new
                        tokens_to_values_prev
                        keys_minus_p
                        tokens_to_vals_eq). }

                (* then to the key that did change *)
                assert
                    (tokens_to_values_new (token_pooled p) = 
                    tokens_to_values_prev (token_pooled p) + 
                    get_rate (token_pooled p) (stor_rates prev_state) * qty_pooled p)
                as new_key_eq.
                {   unfold tokens_to_values_new, tokens_to_values_prev.
                    rewrite bal_update.
                    apply N.mul_add_distr_l. }
                rewrite old_keys_eq. rewrite new_key_eq.
                rewrite <- N.add_assoc.
                rewrite (N.add_comm
                    (get_rate (token_pooled p) (stor_rates prev_state) * qty_pooled p)
                    (suml (map tokens_to_values_prev keys_minus_p))).
                now rewrite N.add_assoc. }
            rewrite separate_sum. clear separate_sum.
            rewrite out_update.
            now rewrite IH.
        (* m = unpool *)
        +   destruct unpool as [u msg_unpool].
            rewrite msg_unpool in receive_some.    
            (* understand how tokens_held has changed *)
            destruct (unpool_decreases_tokens_held_pf prev_state chain ctx u new_state new_acts
            receive_some) as [bal_update bals_unchanged].
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
                rewrite (token_keys_invariant_unpool u new_state new_acts prev_state ctx 
                chain receive_some).
                apply map_ext.
                intro t.
                unfold get_rate. 
                now rewrite rates_update. }
            rewrite rates_unchanged. clear rates_unchanged.
            (* now separate the sum *)
            assert (suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state)) 
            = suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held prev_state)) - 
            qty_unpooled u)
            as separate_sum.
            {   unfold tokens_to_values.
                (* some simplifying notation *)
                set (keys_minus_u := (remove token_eq_dec (token_unpooled u) 
                    (FMap.keys (stor_rates prev_state)))).
                set (tokens_to_values_new := fun k : token => 
                    get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held new_state)).
                set (tokens_to_values_prev := fun k : token => 
                    get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state)).
                (* 1. show there's a Permutation with (token_pooled p) at the front *)
                assert (Permutation
                    (FMap.keys (stor_rates prev_state)) 
                    ((token_unpooled u) :: keys_minus_u))
                as keys_permuted.
                {   unfold keys_minus_u.
                    (* In (token_pooled p) (FMap.keys (stor_rates prev_state)) *)
                    destruct (unpool_entrypoint_check_pf prev_state new_state chain ctx u 
                    new_acts receive_some) as [r_x rate_exists_el].
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
                        now rewrite H_in. }
                    now rewrite (mapped_eq
                        token N
                        tokens_to_values_new
                        tokens_to_values_prev
                        keys_minus_u
                        tokens_to_vals_eq). }
                rewrite old_keys_eq. clear old_keys_eq.

                (* then to the key that did change *)
                assert
                    (tokens_to_values_new (token_unpooled u) = 
                    tokens_to_values_prev (token_unpooled u) - qty_unpooled u)
                as new_key_eq.
                {   unfold tokens_to_values_new, tokens_to_values_prev.
                    (* get the calculation from the specification *)
                    rewrite bal_update.
                    rewrite (N.mul_sub_distr_l
                        (get_bal (token_unpooled u) (stor_tokens_held prev_state))
                        (calc_rx_inv (get_rate (token_unpooled u) (stor_rates prev_state)) 
                        (qty_unpooled u)) (get_rate (token_unpooled u) (stor_rates prev_state))).
                    now rewrite rates_balance_pf. }
                rewrite new_key_eq.
                
                (* this is an additional condition required here so that commutativity applies *)
                assert (qty_unpooled u <= tokens_to_values_prev (token_unpooled u))
                as unpooled_leq. {
                    now unfold tokens_to_values_prev. }
                now rewrite (N.add_sub_swap 
                    (tokens_to_values_prev (token_unpooled u))
                    (suml (map tokens_to_values_prev keys_minus_u))
                    (qty_unpooled u)
                    unpooled_leq). }
            rewrite separate_sum. clear separate_sum.
            now rewrite IH.
        (* m = trade *)
        +   destruct trade as [t msg_trade].
            rewrite msg_trade in receive_some.
            (* understand how tokens_held has changed *)
            destruct (trade_tokens_held_update_pf prev_state chain ctx t new_state new_acts 
            receive_some) 
            as [tokens_held_update_ty [tokens_held_update_tx tokens_held_update_tz]].
            (* how calling trade updates rates *)
            destruct (trade_update_rates_formula_pf prev_state chain ctx t new_state new_acts
            receive_some) as [tx_neq_ty [rx_change rz_unchanged]].
            (* how outstanding_tokens has changed by calling trade *)
            pose proof (trade_outstanding_update_pf prev_state chain ctx t new_state new_acts 
                receive_some) as out_update.
            rewrite out_update.
            clear out_update.
            
            (* LHS equals sum over tokens except for tx and ty, plus r_x' * etc , 
            minus r_y * delta_y *)
            
            (* some notation *)
            unfold tokens_to_values.
            set (keys_minus_trade_in := 
                (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))).
            set (keys_minus_trades := 
                (remove token_eq_dec (token_out_trade t) keys_minus_trade_in)).
            set (tokens_to_values_new := fun k : token => 
                get_rate k (stor_rates new_state) * get_bal k (stor_tokens_held new_state)).
            
            (* LHS *)
            (* permute FMap.keys (stor_tokens_held new_state) to have tx :: ty :: keys' *)
                (* for these, rates and balances are all the same as before *)
            assert (Permutation
                (FMap.keys (stor_rates new_state)) 
                ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades))
            as keys_permuted.
            {   unfold keys_minus_trades.
                unfold keys_minus_trade_in.
                assert (Permutation 
                    (FMap.keys (stor_rates new_state))
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state))))
                as permute_1.
                {   apply (nodup_permute
                        (token_in_trade t)
                        (FMap.keys (stor_rates new_state))
                        token_eq_dec
                        (FMap.NoDup_keys (stor_rates new_state))).
                    assert (exists x, FMap.find (token_in_trade t) (stor_rates new_state) 
                    = Some x) as rate_exists.
                    {   destruct (trade_update_rates_pf prev_state chain ctx t new_state 
                        new_acts receive_some) as [_ update_rates].
                        simpl in update_rates.
                        rewrite update_rates.
                        set (x := (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
                        (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t)
                        (stor_outstanding_tokens prev_state) (get_bal (token_in_trade t) 
                        (stor_tokens_held prev_state)))).
                        exists x.
                        apply FMap.find_add. }
                    destruct rate_exists as [x rate_exists].
                    apply (FMap.In_elements (token_in_trade t) x (stor_rates new_state))
                    in rate_exists.
                    now apply (in_map fst 
                        (FMap.elements (stor_rates new_state))
                        (token_in_trade t, x)). }
                assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))
                    ((token_out_trade t) :: (token_in_trade t) :: 
                    remove token_eq_dec (token_out_trade t) 
                    (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))))
                as permute_2.
                {   assert (Permutation 
                        (token_out_trade t :: token_in_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates new_state))))
                        (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates new_state)))))
                    as permute_step_1. 
                    {   assert (Permutation
                            (token_in_trade t
                            :: remove token_eq_dec (token_out_trade t) (remove token_eq_dec 
                            (token_in_trade t) (FMap.keys (stor_rates new_state))))
                            (remove token_eq_dec (token_out_trade t)
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                            (FMap.keys (stor_rates new_state)))))
                        as inner_permute.
                        {   set (rates_remove_in := (remove token_eq_dec (token_in_trade t) 
                            (FMap.keys (stor_rates new_state)))).
                            rewrite remove_permute; try assumption.
                            apply Permutation_refl. }
                        exact (perm_skip (token_out_trade t) inner_permute). }
                    assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))
                    (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates new_state)))))
                    as permute_step_2.
                    {   apply nodup_permute.
                        (* prove the NoDup result *)
                        -   apply NoDup_cons.
                            +   apply remove_In.
                            +   apply nodup_remove.
                                exact (FMap.NoDup_keys (stor_rates new_state)).
                        (* prove the In result *)
                        -   apply in_cons.
                            apply in_in_remove.
                            +   now apply not_eq_sym.
                            +   assert (exists x, 
                                    FMap.find (token_out_trade t) (stor_rates new_state) 
                                    = Some x) 
                                as rate_exists. 
                                {   pose proof (trade_entrypoint_check_pf prev_state
                                    chain ctx t new_state new_acts receive_some) 
                                    as trade_check.
                                    (* get rate from prev_state *)
                                    do 3 destruct trade_check as [* trade_check].
                                    destruct trade_check as [_ trade_check].
                                    destruct trade_check as [_ prev_rate].
                                    clear x x0.
                                    (* get the rate from the new state *)
                                    rewrite <- (rz_unchanged (token_out_trade t) 
                                    (not_eq_sym tx_neq_ty)) in prev_rate.
                                    now exists x1. }
                                destruct rate_exists as [x rate_exists].
                                apply FMap.In_elements in rate_exists.
                                now apply (in_map fst 
                                    (FMap.elements (stor_rates new_state))
                                    (token_out_trade t, x)). }
                    exact (Permutation_trans permute_step_2 (Permutation_sym permute_step_1)). }
                exact (Permutation_trans permute_1 
                    (Permutation_trans permute_2
                        (perm_swap (token_in_trade t) (token_out_trade t)
                        (remove token_eq_dec (token_out_trade t)
                        (remove token_eq_dec (token_in_trade t) 
                        (FMap.keys (stor_rates new_state))))))). }
            (* Now separate LHS into ^^, plus new rate * t_x, minus rate * t_y *)
            pose proof 
                (Permutation_map tokens_to_values_new)
                    (* list 1 *)
                    (FMap.keys (stor_rates new_state))
                    (* list 2 *)
                    ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades)
                    (* the previous permutation *)
                    keys_permuted
            as lhs_permute_map.
            (* now that we have that permutation, we can decompose the suml *)
            rewrite (suml_permute_commutes
                (map tokens_to_values_new (FMap.keys (stor_rates new_state)))
                (map tokens_to_values_new 
                    ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades))
                lhs_permute_map).
            (* now extract (token_in_trade t) and (token_out_trade t) *)
            rewrite (map_extract 
                (token_in_trade t)
                (token_out_trade t :: keys_minus_trades)
                tokens_to_values_new).
            rewrite (map_extract 
                (token_out_trade t)
                keys_minus_trades
                tokens_to_values_new).
            rewrite (suml_extract (tokens_to_values_new (token_in_trade t))).
            rewrite (suml_extract (tokens_to_values_new (token_out_trade t))).

            (* permute FMap.keys for the OLD suml to MANIPULATE the inductive hypothesis IH *)
            unfold tokens_to_values in IH.
            set (keys_minus_trade_in_prev := 
                (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))).
            set (keys_minus_trades_prev := 
                (remove token_eq_dec (token_out_trade t) keys_minus_trade_in_prev)).
            set (tokens_to_values_prev := fun k : token => 
                get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state)) 
            in IH.

            assert (Permutation
                (FMap.keys (stor_rates prev_state)) 
                ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades_prev))
            as keys_permuted_prev.
            {   unfold keys_minus_trades_prev.
                unfold keys_minus_trade_in_prev.
                assert (Permutation 
                    (FMap.keys (stor_rates prev_state))
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state))))
                as permute_1.
                {   apply (nodup_permute
                        (token_in_trade t)
                        (FMap.keys (stor_rates prev_state))
                        token_eq_dec
                        (FMap.NoDup_keys (stor_rates prev_state))).
                    assert (exists x, FMap.find (token_in_trade t) (stor_rates prev_state) 
                    = Some x) as rate_exists.
                    {   pose proof (trade_entrypoint_check_pf prev_state
                            chain ctx t new_state new_acts receive_some) 
                        as trade_check.
                        do 3 destruct trade_check as [* trade_check].
                        destruct trade_check as [_ trade_check].
                        destruct trade_check as [prev_rate _].
                        clear x x1.
                        now exists x0. }
                    destruct rate_exists as [x rate_exists].
                    apply (FMap.In_elements (token_in_trade t) x (stor_rates prev_state))
                    in rate_exists.
                    now apply (in_map fst 
                        (FMap.elements (stor_rates prev_state))
                        (token_in_trade t, x)). }
                assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))
                    ((token_out_trade t) :: (token_in_trade t) :: 
                    remove token_eq_dec (token_out_trade t) 
                    (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))))
                as permute_2.
                {   assert (Permutation 
                        (token_out_trade t :: token_in_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates prev_state))))
                        (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates prev_state)))))
                    as permute_step_1. 
                    {   assert (Permutation
                            (token_in_trade t
                            :: remove token_eq_dec (token_out_trade t) (remove token_eq_dec 
                            (token_in_trade t) (FMap.keys (stor_rates prev_state))))
                            (remove token_eq_dec (token_out_trade t)
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                            (FMap.keys (stor_rates prev_state)))))
                        as inner_permute.
                        {   set (rates_remove_in := (remove token_eq_dec (token_in_trade t) 
                            (FMap.keys (stor_rates prev_state)))).
                            rewrite remove_permute; try assumption.
                            apply Permutation_refl. }
                        exact (perm_skip (token_out_trade t) inner_permute). }
                    assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))
                    (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates prev_state)))))
                    as permute_step_2.
                    {   apply nodup_permute.
                        (* prove the NoDup result *)
                        -   apply NoDup_cons.
                            +   apply remove_In.
                            +   apply nodup_remove.
                                exact (FMap.NoDup_keys (stor_rates prev_state)).
                        (* prove the In result *)
                        -   apply in_cons.
                            apply in_in_remove.
                            +   now apply not_eq_sym.
                            +   assert (exists x, 
                                    FMap.find (token_out_trade t) (stor_rates prev_state) = Some x) 
                                as rate_exists. 
                                {   pose proof (trade_entrypoint_check_pf prev_state
                                        chain ctx t new_state new_acts receive_some) 
                                    as trade_check.
                                    do 3 destruct trade_check as [* trade_check].
                                    destruct trade_check as [_ trade_check].
                                    destruct trade_check as [_ prev_rate].
                                    clear x x0.
                                    now exists x1. }
                                destruct rate_exists as [x rate_exists].
                                apply FMap.In_elements in rate_exists.
                                now apply (in_map fst 
                                    (FMap.elements (stor_rates prev_state))
                                    (token_out_trade t, x)). }
                    exact (Permutation_trans permute_step_2 (Permutation_sym permute_step_1)). }
                exact (Permutation_trans permute_1 
                    (Permutation_trans permute_2
                        (perm_swap (token_in_trade t) (token_out_trade t)
                        (remove token_eq_dec (token_out_trade t)
                        (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state))))))). }
            (* Now separate LHS into ^^, plus new rate * t_x, minus rate * t_y *)
            pose proof 
                (Permutation_map tokens_to_values_prev)
                    (* list 1 *)
                    (FMap.keys (stor_rates prev_state))
                    (* list 2 *)
                    ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades_prev)
                    (* the previous permutation *)
                    keys_permuted_prev
            as lhs_permute_map_prev.
            (* now that we have that permutation, we can decompose the suml *)
            rewrite (suml_permute_commutes
                (map tokens_to_values_prev (FMap.keys (stor_rates prev_state)))
                (map tokens_to_values_prev ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades_prev))
                lhs_permute_map_prev)
            in IH.
            (* now extract (token_in_trade t) and (token_out_trade t) *)
            rewrite (map_extract 
                (token_in_trade t)
                (token_out_trade t :: keys_minus_trades_prev)
                tokens_to_values_prev)
            in IH.
            rewrite (map_extract 
                (token_out_trade t)
                keys_minus_trades_prev
                tokens_to_values_prev)
            in IH.
            rewrite (suml_extract (tokens_to_values_prev (token_in_trade t))) in IH.
            rewrite (suml_extract (tokens_to_values_prev (token_out_trade t))) in IH.
            rewrite <- IH.

            (* Proceed in two parts *)
            (* excluding the two tokens involved in the trade, all else is equal *)
            assert (suml (map tokens_to_values_new  keys_minus_trades) = 
                    suml (map tokens_to_values_prev keys_minus_trades_prev))
            as unchanged_keys_eq.
            {   apply suml_permute_commutes.
                assert ((map tokens_to_values_prev keys_minus_trades_prev)
                    = (map tokens_to_values_new keys_minus_trades_prev))
                as calc_eq.
                {   (* We use rz_unchanged and tokens_held_update_tz *)
                    apply mapped_eq.
                    intros a in_keys.
                    (* first prove that a <> token_in_trade t and a <> token_out_trade t *)
                    assert (a <> (token_in_trade t) /\ a <> (token_out_trade t))
                    as a_neq_traded.
                    {   unfold keys_minus_trades_prev in in_keys.
                        destruct (in_remove token_eq_dec keys_minus_trade_in_prev a  (token_out_trade t) in_keys) as [a_in_prev a_neq_out].
                        unfold keys_minus_trade_in_prev in a_in_prev.
                        destruct (in_remove token_eq_dec
                            (FMap.keys (stor_rates prev_state))
                            a (token_in_trade t)
                            a_in_prev)
                        as [_ a_neq_in].
                        split;
                        try exact a_neq_out;
                        try exact a_neq_in. }
                    destruct a_neq_traded as [a_neq_in a_neq_out].
                    pose proof (rz_unchanged a a_neq_in) as rates_eq.
                    pose proof (tokens_held_update_tz a a_neq_in a_neq_out) as bal_eq.
                    unfold keys_minus_trades_prev, tokens_to_values_prev, tokens_to_values_new.
                    unfold get_rate.
                    replace (FMap.find a (stor_rates new_state))
                    with (FMap.find a (stor_rates prev_state)).
                    now replace (get_bal a (stor_tokens_held new_state))
                    with (get_bal a (stor_tokens_held prev_state)). }
                rewrite calc_eq.
                apply Permutation_map.
                unfold keys_minus_trades, keys_minus_trades_prev.
                unfold keys_minus_trade_in, keys_minus_trade_in_prev.
                do 2 (apply remove_permute_2; 
                try apply nodup_remove;
                try apply FMap.NoDup_keys).
                (* ... *)
                destruct (trade_update_rates_pf prev_state chain ctx t new_state new_acts receive_some) as [_ update_rates].
                rewrite update_rates. 
                clear update_rates.
                set (x := (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
                (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
                (get_bal (token_in_trade t) (stor_tokens_held prev_state)))).
                assert (exists x', FMap.find (token_in_trade t) (stor_rates prev_state) = Some x')
                as prev_x.
                {   pose proof (trade_entrypoint_check_pf prev_state
                        chain ctx t new_state new_acts receive_some) 
                    as trade_check.
                    do 3 destruct trade_check as [* trade_check].
                    destruct trade_check as [_ trade_check].
                    destruct trade_check as [prev_rate _].
                    clear x0 x2.
                    now exists x1. }
                destruct prev_x as [x' prev_x].
                exact (FMap.keys_already (token_in_trade t) x' x (stor_rates prev_state) prev_x). }

            assert (tokens_to_values_new (token_in_trade t) + tokens_to_values_new (token_out_trade t)
                = tokens_to_values_prev (token_in_trade t) + tokens_to_values_prev (token_out_trade t))
            as changed_keys_eq.
            {   unfold tokens_to_values_new, tokens_to_values_prev.
                set (r_x' := (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
                (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
                (get_bal (token_in_trade t) (stor_tokens_held prev_state)))).
                rewrite tokens_held_update_tx.
                rewrite tokens_held_update_ty.
                set (delta_y := calc_delta_y (get_rate (token_in_trade t) (stor_rates prev_state))
                (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
                (get_bal (token_in_trade t) (stor_tokens_held prev_state))).
                set (r_x := get_rate (token_in_trade t) (stor_rates prev_state)).
                set (x := get_bal (token_in_trade t) (stor_tokens_held prev_state)).
                set (y := get_bal (token_out_trade t) (stor_tokens_held prev_state)).
                assert (get_rate (token_out_trade t) (stor_rates prev_state) = 
                    get_rate (token_out_trade t) (stor_rates new_state)) 
                as ry_unchanged.
                {   unfold get_rate.
                    pose proof (rz_unchanged (token_out_trade t) (not_eq_sym tx_neq_ty)).
                    now replace (FMap.find (token_out_trade t) (stor_rates new_state))
                    with (FMap.find (token_out_trade t) (stor_rates prev_state)). }
                rewrite <- ry_unchanged.
                set (r_y := get_rate (token_out_trade t) (stor_rates prev_state)).
                unfold get_rate.
                replace (FMap.find (token_in_trade t) (stor_rates new_state))
                with (Some r_x').
                (* finally, from the specification *)
                apply rates_balance_2_pf. }
            rewrite unchanged_keys_eq.
            rewrite N.add_assoc.
            rewrite N.add_assoc.
            now rewrite changed_keys_eq.
        (* now for all other entrypoints *)
        +   destruct other as [o msg_other_op].
            rewrite msg_other_op in receive_some.
            rewrite <- (FMap.ext_eq (stor_rates prev_state) (stor_rates new_state) (other_rates_unchanged_pf prev_state new_state chain ctx o new_acts receive_some)).    
            rewrite <- (FMap.ext_eq (stor_tokens_held prev_state) (stor_tokens_held new_state) (other_balances_unchanged_pf prev_state new_state chain ctx o new_acts receive_some)).
            rewrite <- (other_outstanding_unchanged_pf prev_state new_state chain ctx o new_acts receive_some).
            assumption.
    (* Please reestablish the invariant after a recursive call *)
    -   destruct msg.
        (* first, msg = None *)
        2:{ is_sp_destruct.
            pose proof (none_fails_pf prev_state chain ctx) as failed.
            destruct failed as [err failed].
            rewrite receive_some in failed.
            inversion failed. }
        (* msg = Some m *)
        is_sp_destruct.
        pose proof (msg_destruct_pf m) as msg_destruct.
        destruct msg_destruct as [pool | [unpool | [trade | other]]].
        (* m = pool *)
        +   destruct pool as [p msg_pool].
            rewrite msg_pool in receive_some.    
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
                unfold get_rate. 
                now rewrite rates_update. }
            rewrite rates_unchanged. clear rates_unchanged.
            (* now separate the sum *)
            assert (suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state)) = 
                    suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held prev_state)) + get_rate (token_pooled p) (stor_rates prev_state) * qty_pooled p)
            as separate_sum.
            {   unfold tokens_to_values.
                (* some simplifying notation *)
                set (keys_minus_p := (remove token_eq_dec (token_pooled p) (FMap.keys (stor_rates prev_state)))).
                set (tokens_to_values_new := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held new_state)).
                set (tokens_to_values_prev := fun (k : token) => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state)).
                (* 1. show there's a Permutation with (token_pooled p) at the front *)
                assert (Permutation
                    (FMap.keys (stor_rates prev_state)) 
                    ((token_pooled p) :: keys_minus_p))
                as keys_permuted.
                {   unfold keys_minus_p.
                    (* In (token_pooled p) (FMap.keys (stor_rates prev_state)) *)
                    pose proof (pool_entrypoint_check_pf prev_state new_state chain ctx p new_acts receive_some) as rate_exists.
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
                        now rewrite H_in. }
                    now rewrite (mapped_eq
                        token N
                        tokens_to_values_new
                        tokens_to_values_prev
                        keys_minus_p
                        tokens_to_vals_eq). }

                (* then to the key that did change *)
                assert
                    (tokens_to_values_new (token_pooled p) = 
                    tokens_to_values_prev (token_pooled p) + 
                    get_rate (token_pooled p) (stor_rates prev_state) * qty_pooled p)
                as new_key_eq.
                {   unfold tokens_to_values_new, tokens_to_values_prev.
                    rewrite bal_update.
                    apply N.mul_add_distr_l. }
                rewrite old_keys_eq. rewrite new_key_eq.
                rewrite <- N.add_assoc.
                rewrite (N.add_comm
                    (get_rate (token_pooled p) (stor_rates prev_state) * qty_pooled p)
                    (suml (map tokens_to_values_prev keys_minus_p))).
                now rewrite N.add_assoc. }
            rewrite separate_sum. clear separate_sum.
            rewrite out_update.
            now rewrite IH.
        (* m = unpool *)
        +   destruct unpool as [u msg_unpool].
            rewrite msg_unpool in receive_some.    
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
                unfold get_rate. 
                now rewrite rates_update. }
            rewrite rates_unchanged. clear rates_unchanged.
            (* now separate the sum *)
            assert (suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held new_state)) = suml (tokens_to_values (stor_rates prev_state) (stor_tokens_held prev_state)) - qty_unpooled u)
            as separate_sum.
            {   unfold tokens_to_values.
                (* some simplifying notation *)
                set (keys_minus_u := (remove token_eq_dec (token_unpooled u) (FMap.keys (stor_rates prev_state)))).
                set (tokens_to_values_new := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held new_state)).
                set (tokens_to_values_prev := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state)).
                (* 1. show there's a Permutation with (token_pooled p) at the front *)
                assert (Permutation
                    (FMap.keys (stor_rates prev_state)) 
                    ((token_unpooled u) :: keys_minus_u))
                as keys_permuted.
                {   unfold keys_minus_u.
                    (* In (token_pooled p) (FMap.keys (stor_rates prev_state)) *)
                    pose proof (unpool_entrypoint_check_pf prev_state new_state chain ctx u new_acts receive_some) as rate_exists.
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
                        now rewrite H_in. }
                    now rewrite (mapped_eq
                        token N
                        tokens_to_values_new
                        tokens_to_values_prev
                        keys_minus_u
                        tokens_to_vals_eq). }
                rewrite old_keys_eq. clear old_keys_eq.

                (* then to the key that did change *)
                assert
                    (tokens_to_values_new (token_unpooled u) = 
                    tokens_to_values_prev (token_unpooled u) - qty_unpooled u)
                as new_key_eq.
                {   unfold tokens_to_values_new, tokens_to_values_prev.
                    (* get the calculation from the specification *)
                    rewrite bal_update.
                    rewrite (N.mul_sub_distr_l
                        (get_bal (token_unpooled u) (stor_tokens_held prev_state))
                        (calc_rx_inv (get_rate (token_unpooled u) (stor_rates prev_state)) (qty_unpooled u))
                        (get_rate (token_unpooled u) (stor_rates prev_state))).
                    now rewrite rates_balance_pf. }
                rewrite new_key_eq.
                
                (* this is an additional condition required here so that commutativity applies *)
                assert (qty_unpooled u <= tokens_to_values_prev (token_unpooled u))
                as unpooled_leq. {
                    unfold tokens_to_values_prev.
                    exact (unpool_entrypoint_check_2_pf prev_state new_state chain ctx u new_acts receive_some). }
                now rewrite (N.add_sub_swap 
                    (tokens_to_values_prev (token_unpooled u))
                    (suml (map tokens_to_values_prev keys_minus_u))
                    (qty_unpooled u)
                    unpooled_leq). }
            rewrite separate_sum. clear separate_sum.
            now rewrite IH.
        (* m = trade *)
        +   destruct trade as [t msg_trade].
            rewrite msg_trade in receive_some.
            (* understand how tokens_held has changed *)
            destruct (trade_tokens_held_update_pf prev_state chain ctx t new_state new_acts 
            receive_some) as [tokens_held_update_ty [tokens_held_update_tx tokens_held_update_tz]].
            (* how calling trade updates rates *)
            destruct (trade_update_rates_formula_pf prev_state chain ctx t new_state new_acts
            receive_some) as [tx_neq_ty [rx_change rz_unchanged]].
            (* how outstanding_tokens has changed by calling trade *)
            pose proof (trade_outstanding_update_pf prev_state chain ctx t new_state new_acts 
                receive_some) as out_update.
            rewrite out_update. clear out_update.
            
            (* LHS equals sum over tokens except for tx and ty, plus r_x' * etc , minus r_y * delta_y *)
            
            (* some notation *)
            unfold tokens_to_values.
            set (keys_minus_trade_in := (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))).
            set (keys_minus_trades := (remove token_eq_dec (token_out_trade t) keys_minus_trade_in)).
            set (tokens_to_values_new := fun k : token => get_rate k (stor_rates new_state) * get_bal k (stor_tokens_held new_state)).
            
            (* LHS *)
            (* permute FMap.keys (stor_tokens_held new_state) to have tx :: ty :: keys' *)
                (* for these, rates and balances are all the same as before *)
            assert (Permutation
                (FMap.keys (stor_rates new_state)) 
                ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades))
            as keys_permuted.
            {   unfold keys_minus_trades.
                unfold keys_minus_trade_in.
                assert (Permutation 
                    (FMap.keys (stor_rates new_state))
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state))))
                as permute_1.
                {   apply (nodup_permute
                        (token_in_trade t)
                        (FMap.keys (stor_rates new_state))
                        token_eq_dec
                        (FMap.NoDup_keys (stor_rates new_state))).
                    assert (exists x, FMap.find (token_in_trade t) (stor_rates new_state) = Some x) as rate_exists.
                    {   destruct (trade_update_rates_pf prev_state chain ctx t new_state new_acts receive_some) as [_ update_rates].
                        simpl in update_rates.
                        rewrite update_rates.
                        set (x := (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
                        (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t)
                        (stor_outstanding_tokens prev_state) (get_bal (token_in_trade t) (stor_tokens_held prev_state)))).
                        exists x.
                        apply FMap.find_add. }
                    destruct rate_exists as [x rate_exists].
                    apply (FMap.In_elements (token_in_trade t) x (stor_rates new_state))
                    in rate_exists.
                    now apply (in_map fst 
                        (FMap.elements (stor_rates new_state))
                        (token_in_trade t, x)). }
                assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))
                    ((token_out_trade t) :: (token_in_trade t) :: 
                    remove token_eq_dec (token_out_trade t) 
                    (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))))
                as permute_2.
                {   assert (Permutation 
                        (token_out_trade t :: token_in_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates new_state))))
                        (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates new_state)))))
                    as permute_step_1. 
                    {   assert (Permutation
                            (token_in_trade t
                            :: remove token_eq_dec (token_out_trade t) (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state))))
                            (remove token_eq_dec (token_out_trade t)
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))))
                        as inner_permute.
                        {   set (rates_remove_in := (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))).
                            rewrite remove_permute; try assumption.
                            apply Permutation_refl. }
                        exact (perm_skip (token_out_trade t) inner_permute). }
                    assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state)))
                    (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates new_state)))))
                    as permute_step_2.
                    {   apply nodup_permute.
                        (* prove the NoDup result *)
                        -   apply NoDup_cons.
                            +   apply remove_In.
                            +   apply nodup_remove.
                                exact (FMap.NoDup_keys (stor_rates new_state)).
                        (* prove the In result *)
                        -   apply in_cons.
                            apply in_in_remove.
                            +   now apply not_eq_sym.
                            +   assert (exists x, 
                                    FMap.find (token_out_trade t) (stor_rates new_state) = Some x) 
                                as rate_exists. 
                                {   pose proof (trade_entrypoint_check_pf prev_state
                                    chain ctx t new_state new_acts receive_some) 
                                    as trade_check.
                                    (* get rate from prev_state *)
                                    do 3 destruct trade_check as [* trade_check].
                                    destruct trade_check as [_ trade_check].
                                    destruct trade_check as [_ prev_rate].
                                    clear x x0.
                                    (* get the rate from the new state *)
                                    rewrite <- (rz_unchanged (token_out_trade t) (not_eq_sym tx_neq_ty)) in prev_rate.
                                    now exists x1. }
                                destruct rate_exists as [x rate_exists].
                                apply FMap.In_elements in rate_exists.
                                now apply (in_map fst 
                                    (FMap.elements (stor_rates new_state))
                                    (token_out_trade t, x)). }
                    exact (Permutation_trans permute_step_2 (Permutation_sym permute_step_1)). }
                exact (Permutation_trans permute_1 
                    (Permutation_trans permute_2
                        (perm_swap (token_in_trade t) (token_out_trade t)
                        (remove token_eq_dec (token_out_trade t)
                        (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates new_state))))))). }
            (* Now separate LHS into ^^, plus new rate * t_x, minus rate * t_y *)
            pose proof 
                (Permutation_map tokens_to_values_new)
                    (* list 1 *)
                    (FMap.keys (stor_rates new_state))
                    (* list 2 *)
                    ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades)
                    (* the previous permutation *)
                    keys_permuted
            as lhs_permute_map.
            (* now that we have that permutation, we can decompose the suml *)
            rewrite (suml_permute_commutes
                (map tokens_to_values_new (FMap.keys (stor_rates new_state)))
                (map tokens_to_values_new ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades))
                lhs_permute_map).
            (* now extract (token_in_trade t) and (token_out_trade t) *)
            rewrite (map_extract 
                (token_in_trade t)
                (token_out_trade t :: keys_minus_trades)
                tokens_to_values_new).
            rewrite (map_extract 
                (token_out_trade t)
                keys_minus_trades
                tokens_to_values_new).
            rewrite (suml_extract (tokens_to_values_new (token_in_trade t))).
            rewrite (suml_extract (tokens_to_values_new (token_out_trade t))).

            (* permute FMap.keys for the OLD suml to MANIPULATE the inductive hypothesis IH *)
            unfold tokens_to_values in IH.
            set (keys_minus_trade_in_prev := (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))).
            set (keys_minus_trades_prev := (remove token_eq_dec (token_out_trade t) keys_minus_trade_in_prev)).
            set (tokens_to_values_prev := fun k : token => get_rate k (stor_rates prev_state) * get_bal k (stor_tokens_held prev_state)) in IH.

            assert (Permutation
                (FMap.keys (stor_rates prev_state)) 
                ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades_prev))
            as keys_permuted_prev.
            {   unfold keys_minus_trades_prev.
                unfold keys_minus_trade_in_prev.
                assert (Permutation 
                    (FMap.keys (stor_rates prev_state))
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state))))
                as permute_1.
                {   apply (nodup_permute
                        (token_in_trade t)
                        (FMap.keys (stor_rates prev_state))
                        token_eq_dec
                        (FMap.NoDup_keys (stor_rates prev_state))).
                    assert (exists x, FMap.find (token_in_trade t) (stor_rates prev_state) = Some x) as rate_exists.
                    {   pose proof (trade_entrypoint_check_pf prev_state
                            chain ctx t new_state new_acts receive_some) 
                        as trade_check.
                        do 3 destruct trade_check as [* trade_check].
                        destruct trade_check as [_ trade_check].
                        destruct trade_check as [prev_rate _].
                        clear x x1.
                        now exists x0. }
                    destruct rate_exists as [x rate_exists].
                    apply (FMap.In_elements (token_in_trade t) x (stor_rates prev_state))
                    in rate_exists.
                    now apply (in_map fst 
                        (FMap.elements (stor_rates prev_state))
                        (token_in_trade t, x)). }
                assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))
                    ((token_out_trade t) :: (token_in_trade t) :: 
                    remove token_eq_dec (token_out_trade t) 
                    (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))))
                as permute_2.
                {   assert (Permutation 
                        (token_out_trade t :: token_in_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates prev_state))))
                        (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates prev_state)))))
                    as permute_step_1. 
                    {   assert (Permutation
                            (token_in_trade t
                            :: remove token_eq_dec (token_out_trade t) (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state))))
                            (remove token_eq_dec (token_out_trade t)
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))))
                        as inner_permute.
                        {   set (rates_remove_in := (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))).
                            rewrite remove_permute; try assumption.
                            apply Permutation_refl. }
                        exact (perm_skip (token_out_trade t) inner_permute). }
                    assert (Permutation 
                    (token_in_trade t :: 
                    remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state)))
                    (token_out_trade t :: 
                            remove token_eq_dec (token_out_trade t) 
                            (token_in_trade t :: remove token_eq_dec (token_in_trade t) 
                                (FMap.keys (stor_rates prev_state)))))
                    as permute_step_2.
                    {   apply nodup_permute.
                        (* prove the NoDup result *)
                        -   apply NoDup_cons.
                            +   apply remove_In.
                            +   apply nodup_remove.
                                exact (FMap.NoDup_keys (stor_rates prev_state)).
                        (* prove the In result *)
                        -   apply in_cons.
                            apply in_in_remove.
                            +   now apply not_eq_sym.
                            +   assert (exists x, 
                                    FMap.find (token_out_trade t) (stor_rates prev_state) = Some x) 
                                as rate_exists. 
                                {   pose proof (trade_entrypoint_check_pf prev_state
                                        chain ctx t new_state new_acts receive_some) 
                                    as trade_check.
                                    do 3 destruct trade_check as [* trade_check].
                                    destruct trade_check as [_ trade_check].
                                    destruct trade_check as [_ prev_rate].
                                    clear x x0.
                                    now exists x1. }
                                destruct rate_exists as [x rate_exists].
                                apply FMap.In_elements in rate_exists.
                                now apply (in_map fst 
                                    (FMap.elements (stor_rates prev_state))
                                    (token_out_trade t, x)). }
                    exact (Permutation_trans permute_step_2 (Permutation_sym permute_step_1)). }
                exact (Permutation_trans permute_1 
                    (Permutation_trans permute_2
                        (perm_swap (token_in_trade t) (token_out_trade t)
                        (remove token_eq_dec (token_out_trade t)
                        (remove token_eq_dec (token_in_trade t) (FMap.keys (stor_rates prev_state))))))). }
            (* Now separate LHS into ^^, plus new rate * t_x, minus rate * t_y *)
            pose proof 
                (Permutation_map tokens_to_values_prev)
                    (* list 1 *)
                    (FMap.keys (stor_rates prev_state))
                    (* list 2 *)
                    ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades_prev)
                    (* the previous permutation *)
                    keys_permuted_prev
            as lhs_permute_map_prev.
            (* now that we have that permutation, we can decompose the suml *)
            rewrite (suml_permute_commutes
                (map tokens_to_values_prev (FMap.keys (stor_rates prev_state)))
                (map tokens_to_values_prev ((token_in_trade t) :: (token_out_trade t) :: keys_minus_trades_prev))
                lhs_permute_map_prev)
            in IH.
            (* now extract (token_in_trade t) and (token_out_trade t) *)
            rewrite (map_extract 
                (token_in_trade t)
                (token_out_trade t :: keys_minus_trades_prev)
                tokens_to_values_prev)
            in IH.
            rewrite (map_extract 
                (token_out_trade t)
                keys_minus_trades_prev
                tokens_to_values_prev)
            in IH.
            rewrite (suml_extract (tokens_to_values_prev (token_in_trade t))) in IH.
            rewrite (suml_extract (tokens_to_values_prev (token_out_trade t))) in IH.
            rewrite <- IH.

            (* Proceed in two parts *)
            (* excluding the two tokens involved in the trade, all else is equal *)
            assert (suml (map tokens_to_values_new  keys_minus_trades) = 
                    suml (map tokens_to_values_prev keys_minus_trades_prev))
            as unchanged_keys_eq.
            {   apply suml_permute_commutes.
                assert ((map tokens_to_values_prev keys_minus_trades_prev)
                    = (map tokens_to_values_new keys_minus_trades_prev))
                as calc_eq.
                {   (* We use rz_unchanged and tokens_held_update_tz *)
                    apply mapped_eq.
                    intros a in_keys.
                    (* first prove that a <> token_in_trade t and a <> token_out_trade t *)
                    assert (a <> (token_in_trade t) /\ a <> (token_out_trade t))
                    as a_neq_traded.
                    {   unfold keys_minus_trades_prev in in_keys.
                        destruct (in_remove token_eq_dec
                            keys_minus_trade_in_prev
                            a (token_out_trade t)
                            in_keys)
                        as [a_in_prev a_neq_out].
                        unfold keys_minus_trade_in_prev in a_in_prev.
                        destruct (in_remove token_eq_dec
                            (FMap.keys (stor_rates prev_state))
                            a (token_in_trade t)
                            a_in_prev)
                        as [_ a_neq_in].
                        split;
                        try exact a_neq_out;
                        try exact a_neq_in. }
                    destruct a_neq_traded as [a_neq_in a_neq_out].
                    pose proof (rz_unchanged a a_neq_in) as rates_eq.
                    pose proof (tokens_held_update_tz a a_neq_in a_neq_out) as bal_eq.
                    unfold keys_minus_trades_prev, tokens_to_values_prev, tokens_to_values_new.
                    unfold get_rate.
                    replace (FMap.find a (stor_rates new_state))
                    with (FMap.find a (stor_rates prev_state)).
                    now replace (get_bal a (stor_tokens_held new_state))
                    with (get_bal a (stor_tokens_held prev_state)). }
                rewrite calc_eq.
                apply Permutation_map.
                unfold keys_minus_trades, keys_minus_trades_prev.
                unfold keys_minus_trade_in, keys_minus_trade_in_prev.
                do 2 (apply remove_permute_2; 
                try apply nodup_remove;
                try apply FMap.NoDup_keys).
                (* ... *)
                pose proof (trade_update_rates_pf prev_state chain ctx t new_state new_acts receive_some)
                as update_rates.
                destruct update_rates as [_ update_rates].
                rewrite update_rates. clear update_rates.
                set (x := (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
                (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
                (get_bal (token_in_trade t) (stor_tokens_held prev_state)))).
                assert (exists x', FMap.find (token_in_trade t) (stor_rates prev_state) = Some x')
                as prev_x.
                {   pose proof (trade_entrypoint_check_pf prev_state
                        chain ctx t new_state new_acts receive_some) 
                    as trade_check.
                    do 3 destruct trade_check as [* trade_check].
                    destruct trade_check as [_ trade_check].
                    destruct trade_check as [prev_rate _].
                    clear x0 x2.
                    now exists x1. }
                destruct prev_x as [x' prev_x].
                exact (FMap.keys_already (token_in_trade t) x' x (stor_rates prev_state) prev_x). }

            assert (tokens_to_values_new (token_in_trade t) + tokens_to_values_new (token_out_trade t)
                = tokens_to_values_prev (token_in_trade t) + tokens_to_values_prev (token_out_trade t))
            as changed_keys_eq.
            {   unfold tokens_to_values_new, tokens_to_values_prev.
                set (r_x' := (calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
                (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
                (get_bal (token_in_trade t) (stor_tokens_held prev_state)))).
                rewrite tokens_held_update_tx.
                rewrite tokens_held_update_ty.
                set (delta_y := calc_delta_y (get_rate (token_in_trade t) (stor_rates prev_state))
                (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t) (stor_outstanding_tokens prev_state)
                (get_bal (token_in_trade t) (stor_tokens_held prev_state))).
                set (r_x := get_rate (token_in_trade t) (stor_rates prev_state)).
                set (x := get_bal (token_in_trade t) (stor_tokens_held prev_state)).
                set (y := get_bal (token_out_trade t) (stor_tokens_held prev_state)).
                assert (get_rate (token_out_trade t) (stor_rates prev_state) = 
                    get_rate (token_out_trade t) (stor_rates new_state)) 
                as ry_unchanged.
                {   unfold get_rate.
                    pose proof (rz_unchanged (token_out_trade t) (not_eq_sym tx_neq_ty)).
                    now replace (FMap.find (token_out_trade t) (stor_rates new_state))
                    with (FMap.find (token_out_trade t) (stor_rates prev_state)). }
                rewrite <- ry_unchanged.
                set (r_y := get_rate (token_out_trade t) (stor_rates prev_state)).
                unfold get_rate.
                replace (FMap.find (token_in_trade t) (stor_rates new_state))
                with (Some r_x').
                (* finally, from the specification *)
                apply rates_balance_2_pf. }
            rewrite unchanged_keys_eq.
            rewrite N.add_assoc.
            rewrite N.add_assoc.
            now rewrite changed_keys_eq.
        (* now for all other entrypoints *)
        +   destruct other as [o msg_other_op].
            rewrite msg_other_op in receive_some.
            rewrite <- (FMap.ext_eq (stor_rates prev_state) (stor_rates new_state) (other_rates_unchanged_pf prev_state new_state chain ctx o new_acts receive_some)).    
            rewrite <- (FMap.ext_eq (stor_tokens_held prev_state) (stor_tokens_held new_state) (other_balances_unchanged_pf prev_state new_state chain ctx o new_acts receive_some)).
            rewrite <- (other_outstanding_unchanged_pf prev_state new_state chain ctx o new_acts receive_some).
            assumption.
    (* solve remaining facts *)
    -   solve_facts.
Qed.

End AbstractSpecification.