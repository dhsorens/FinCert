(* A Generic AMM Contract Specification *)
From stdpp Require Import decidable.
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
 *  Preliminary Definitions
 * ============================================================================= *)
 Section Prelim.

 End Prelim.


(* =============================================================================
 *  Specification
 * ============================================================================= *)

 Section Specification.
 Context { Base : ChainBase }
        { Setup Msg State Error : Type }
        `{Serializable Setup}  `{Serializable Msg}
        `{Serializable State} `{Serializable Error}.
 Set Primitive Projections.
 Set Nonrecursive Elimination Schemes.

 (* Some preliminary definitions *)
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

 Record trade_data := {
    token_in_trade : token ; 
    token_out_trade : token ; 
    qty_trade : N ; (* the qty of token_in going in *)
 }.

 Record dep_lp_data := {
    token_dep : token ;
    qty_dep : N ;
 }.

 Record wth_lp_data := {
    token_wth : token ;
    qty_wth : N ; (* the qty of pool tokens being turned in *)
 }.

 Definition error := N.

 (* ====
    Typeclasses characterize Setup, Msg, State, Error types 
 * ==== *)
 
 (* Setup spec *)
 Class amm_setup_spec (T : Type) := {
    lp_init_caddr : Address ;
 }.

 (* Msg specification *)
 Class amm_msg_spec (T other_entrypoint : Type) := build_msg_spec {
    deposit_lp : dep_lp_data -> T ;
    wthdraw_lp : wth_lp_data -> T ;
    trade : trade_data -> T ;
    (* any other potential entrypoints *)
    other : other_entrypoint -> option T ;
 }.

 (* State specification *)
 Class amm_state_spec (T : Type) := build_state_spec {
     (* a ledger of balances (incl LP token) *)
     token_ledger : T -> FMap token N ; 
     (* LP token caddr *)
     lp_caddr : T -> Address ;
 }.

 (* Error specification *)
 Class amm_error_spec (T : Type) := build_error_spec {
    error_to_Error : error -> T ;
 }.

 Context {amm_other : Type}
         `{amm_setup_spec Setup} `{amm_msg_spec Msg amm_other}
         `{amm_state_spec State} `{amm_error_spec Error}.

 (* The induction principle for Msg *)
 Definition msg_destruct (contract : Contract Setup Msg State Error) : Prop :=
    forall (m : Msg),
    (exists d, m = deposit_lp d) \/
    (exists w, m = wthdraw_lp w) \/
    (exists t, m = trade t) \/
    (exists o, Some m = other o).

 (* ====
    Entrypoint Specification
 * ==== *)
 
 (* a successful call to the trade entrypoint results in correct balance
    updates *)
 Definition trade_updates_balances (contract : Contract Setup Msg State Error) : Prop :=
    True.
 
 (* a successful call to deposit_lp entrypoint *)
 Definition deposit_updates_balances (contract : Contract Setup Msg State Error) : Prop :=
    True.

 (* a successful call to wthdraw_lp entrypoint *)
 Definition withdraw_updates_balances (contract : Contract Setup Msg State Error) : Prop :=
    True.

 (** Amalgamate the propositions into a single proposition *)
 Definition is_amm (C : Contract Setup Msg State Error) : Prop :=
    trade_updates_balances C /\
    deposit_updates_balances C /\
    withdraw_updates_balances C.

 (* custom tactic which destructs is_amm *)




(* =============================================================================
 *  Metaspecification
 * ============================================================================= *)
 Section MetaSpecification.
 Context {contract : Contract Setup Msg State Error}
        { is_sp : is_amm contract }.


 End MetaSpecification.

 End Specification.