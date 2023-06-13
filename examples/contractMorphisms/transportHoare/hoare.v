From FinCert.Specifications.StructuredPoolsSpec Require Import StructuredPoolsSpec.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractMorphisms.
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

(* TODO description of transporting the Hoare property *)

Section TransportHoare.
Context { Base : ChainBase }.

Context { setup storage error : Type }
        `{setup_ser : Serializable setup}  `{stor_ser : Serializable storage}  
        `{err_ser : Serializable error} `{storage_state : @State_Spec Base storage} 
        `{err_err : Error_Spec error}.

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Inductive entrypoint := 
| Pool : pool_data -> entrypoint 
| Unpool : unpool_data -> entrypoint
| Null : trade_data -> entrypoint.

Inductive entrypoint' := 
| Pool' : pool_data -> entrypoint'
| Unpool' : unpool_data -> entrypoint'
| Trade' : trade_data -> entrypoint'.

Context { other_entrypoint : Type }.

Definition e_pool (p : pool_data) : entrypoint := Pool p.
Definition e_unpool (u : unpool_data) : entrypoint := Unpool u.
Definition e_trade (t : trade_data) : entrypoint := Null t.
Definition e_other (o : other_entrypoint) : option entrypoint := None.
Global Instance entrypoint_msg_spec : Msg_Spec entrypoint := {
    pool := e_pool ; 
    unpool := e_unpool ; 
    trade := e_trade ; 
    other := e_other ; 
}.

Definition e'_pool (p : pool_data) : entrypoint' := Pool' p.
Definition e'_unpool (u : unpool_data) : entrypoint' := Unpool' u.
Definition e'_trade (t : trade_data) : entrypoint' := Trade' t.
Definition e'_other (o : other_entrypoint) : option entrypoint' := None.
Global Instance entrypoint'_msg_spec : @Msg_Spec Base other_entrypoint entrypoint' := {
    pool := e'_pool ; 
    unpool := e'_unpool ; 
    trade := e'_trade ; 
    other := e'_other ; 
}.    

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint. Admitted.
    Global Instance entrypoint'_serializable : Serializable entrypoint'. Admitted.
End Serialization.

Context `{ e_ser : Serializable entrypoint } `{e'_ser : Serializable entrypoint'}.
Context `{ set_setup : @Setup_Spec Base setup }
        `{ stor_state : @State_Spec Base storage }.

Context 
    {C  : Contract setup entrypoint  storage error}
    {C' : Contract setup entrypoint' storage error}.

Context { calc_rx_inv : forall (r_x : N) (q : N), N }
        { calc_delta_y : forall (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N), N }
        { calc_rx' : forall (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N), N }.

Axiom is_sp : @is_structured_pool _ _ _ _ _ _ _ _ _ _ _ _ _ calc_rx_inv calc_delta_y calc_rx' C'.

Definition embed_entrypoint (e : entrypoint) : entrypoint' := 
match e with 
| Pool p => Pool' p 
| Unpool p => Unpool' p 
(* redirect the null entrypoint *)
| Null t => Trade' t
end.

(* some assumptions about C and C' *)
Definition init_coherence_prop : Prop := forall c ctx s, 
    result_functor id id 
        (init C c ctx s) = 
    init C' c ctx (id s).
Axiom init_coherence_pf : init_coherence_prop.

Definition recv_coherence_prop : Prop := forall c ctx st op_msg,
    result_functor (fun '(st, l) => (id st, l)) id 
        (receive C c ctx st op_msg) = 
    receive C' c ctx (id st) (option_map embed_entrypoint op_msg).
Axiom recv_coherence_pf : recv_coherence_prop.


(* construct a contract morphism *)
Definition f : ContractMorphism C C' := {|
    setup_morph := id ;
    msg_morph := embed_entrypoint ;
    state_morph := id ;
    error_morph := id ;
    (* coherence *)
    init_coherence := init_coherence_pf ;
    recv_coherence := recv_coherence_pf ;
|}.


(* TODO get rid of this *)
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


(* Prove the following about C using C' and f *)
Theorem pullback_unpool_emits_txns : unpool_emits_txns C.
Proof.
    pose proof is_sp as is_sp.
    is_sp_destruct.
    pose proof recv_coherence_pf as recv_eq.
    unfold recv_coherence_prop in recv_eq.
    unfold unpool_emits_txns.
    intros * recv_some.
    pose proof (unpool_emits_txns_pf cstate chain ctx msg_payload cstate' acts ) 
    as sp_spec_result.
    pose proof (recv_eq chain ctx cstate (Some (unpool msg_payload))) as recv_eq.
    unfold result_functor in recv_eq.
    rewrite recv_some in recv_eq.
    unfold embed_entrypoint in recv_eq.
    cbn in recv_eq.
    pose proof (eq_sym recv_eq) as recv_eq'.
    now apply sp_spec_result in recv_eq'.
Qed.

End TransportHoare.