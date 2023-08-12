From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.

From FinCert.Meta Require Import ContractMorphisms.
From FinCert.Meta Require Import ContractSystems.
From FinCert.Meta Require Import Bisimulation.

(*  Bisimilar contracts have very similar invariants, depending on the state 
    isomorphism. 
    
    In this example, we show that, for bisimilar contracts C1 and C2, if there 
    is a state invariant of C1 which is preserved by the state isomorphism of 
    the bisimulation, then that same state invariant holds for C2.
*)

Section PropositionalIndistinguishability.
Context {Base : ChainBase}.

Context 
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
(* Consider contracts C1 and C2 ... *)
    {C1 : Contract Setup1 Msg1 State1 Error1}
    {C2 : Contract Setup2 Msg2 State2 Error2}.

(* such that C1 and C2 are bisimilar. *)
Context {m1 : ContractTraceMorphism C1 C2} {m2 : ContractTraceMorphism C2 C1}
        {C1_C2_bisim : is_iso_ctm m1 m2}.

(* Assume that both State1 and State2 have a constant in storage, given by a function 
    const_in_stor *)
Context { const_in_stor_C1 : State1 -> nat } { const_in_stor_C2 : State2 -> nat }
(* and assume that this constant is invariant under the ct_state isomorphism *)
        { const_pres : forall st, 
            const_in_stor_C2 (ct_state_morph C1 C2 m1 st) = const_in_stor_C1 st }.

(* Assume that an invariant holds for C1 ... *)
Axiom invariant_C1_init : forall c ctx s cstate,
    init C1 c ctx s = Ok cstate -> 
    (const_in_stor_C1 cstate > 0)%nat.

Axiom invariant_C1_recv : forall c ctx cstate op_msg new_st nacts,
    receive C1 c ctx cstate op_msg = Ok (new_st, nacts) -> 
    (const_in_stor_C1 new_st > 0)%nat.

(* Because the invariant is preserved under the state isomorphism of the bisimulation,
    we can prove that the same invariant of C2 *)
Theorem invariant_C2 bstate caddr (trace : ChainTrace empty_state bstate):
    (* Forall reachable states with contract at caddr, *)
    env_contracts bstate caddr = Some (C2 : WeakContract) ->
    (* such that cstate is the state of the contract, *)
    exists (cstate : State2),
    contract_state bstate caddr = Some cstate /\
    (* the constant in storage is > 0 *)
    (const_in_stor_C2 cstate > 0)%nat.
Proof.
    intros.
    contract_induction; auto; intros.
    (* deployment *)
    -   assert (is_genesis_cstate C2 result)
        as is_gen2.
        {   unfold is_genesis_cstate.
            now exists chain, ctx, setup. }
        pose proof (genesis_fixpoint C2 C1 m2 result is_gen2)
        as is_gen1.
        destruct is_gen1 as [c2 [ctx2 [s2 init_ok2]]].
        pose proof (invariant_C1_init _ _ _ _ init_ok2)
        as invar_C1.
        rewrite <- const_pres in invar_C1.
        assert ((ct_state_morph C1 C2 m1 (ct_state_morph C2 C1 m2 result)) = result)
        as state_id.
        {   unfold is_iso_ctm in C1_C2_bisim.
            destruct C1_C2_bisim as [iso_l iso_r].
            unfold compose_ctm, id_ctm in *.
            replace (ct_state_morph C1 C2 m1 (ct_state_morph C2 C1 m2 result))
            with (Basics.compose (ct_state_morph C1 C2 m1) (ct_state_morph C2 C1 m2) result).
            2:{ auto. }
            inversion iso_r.
            now rewrite H8. }
        now rewrite state_id in invar_C1.
    (* nonrecursive call *)
    -   assert (ContractStep C2 prev_state new_state)
        as step_C2.
        {   apply (build_contract_step C2 prev_state new_state chain ctx msg 
                new_acts receive_some). }
        pose proof (cstep_morph C2 C1 m2 prev_state new_state step_C2)
        as step_morph.
        destruct step_morph.
        pose proof (invariant_C1_recv seq_chain seq_ctx
            (ct_state_morph C2 C1 m2 prev_state) seq_msg
            (ct_state_morph C2 C1 m2 new_state) seq_new_acts recv_ok_step)
        as invar_C2.
        rewrite <- const_pres in invar_C2.
        replace (ct_state_morph C1 C2 m1 (ct_state_morph C2 C1 m2 new_state))
        with (Basics.compose (ct_state_morph C1 C2 m1) (ct_state_morph C2 C1 m2) new_state)
        in invar_C2.
        2:{ auto. }
        assert (Basics.compose (ct_state_morph C1 C2 m1) (ct_state_morph C2 C1 m2) = id)
        as state_id.
        {   unfold is_iso_ctm in C1_C2_bisim.
            destruct C1_C2_bisim as [iso_l iso_r].
            unfold compose_ctm, id_ctm in *.
            now inversion iso_r. }
        now rewrite state_id in invar_C2.
    (* recursive call *)
    -   assert (ContractStep C2 prev_state new_state)
        as step_C2.
        {   apply (build_contract_step C2 prev_state new_state chain ctx msg 
                new_acts receive_some). }
        pose proof (cstep_morph C2 C1 m2 prev_state new_state step_C2)
        as step_morph.
        destruct step_morph.
        pose proof (invariant_C1_recv seq_chain seq_ctx
            (ct_state_morph C2 C1 m2 prev_state) seq_msg
            (ct_state_morph C2 C1 m2 new_state) seq_new_acts recv_ok_step)
        as invar_C2.
        rewrite <- const_pres in invar_C2.
        replace (ct_state_morph C1 C2 m1 (ct_state_morph C2 C1 m2 new_state))
        with (Basics.compose (ct_state_morph C1 C2 m1) (ct_state_morph C2 C1 m2) new_state)
        in invar_C2.
        2:{ auto. }
        assert (Basics.compose (ct_state_morph C1 C2 m1) (ct_state_morph C2 C1 m2) = id)
        as state_id.
        {   unfold is_iso_ctm in C1_C2_bisim.
            destruct C1_C2_bisim as [iso_l iso_r].
            unfold compose_ctm, id_ctm in *.
            now inversion iso_r. }
        now rewrite state_id in invar_C2.
    (* prove facts *)
    -   solve_facts.
Qed.

End PropositionalIndistinguishability.