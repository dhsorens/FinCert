(* Bisimulations of Contracts and Contract Systems
    In this extension to the contract morphisms module, we develop the notion of bisimulation, first
    of a single contract, and then of multiple contracts taken together as a whole.

    Bisimulations are (graph-)isomorphisms of a contract's (resp. system of contract's) trace.

    It consists of three things:

    1. a function between contract (resp. contract system) states, such that:
    2. the initial state of one contract (resp. contract system) maps to an initial state of the other, and
    3. a function between contract (resp. contract system) steps that respects the function between states.

    These three criteria ensure that the execution traces of the contracts (resp. contract systems) are
    isomorphic when considered as trees.

    The definition of a contract trace is found in the ContractMorphisms module; the definition of a 
    system trace is found here.
*)

From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Sets.Ensembles.
From Coq Require Import ZArith.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Permutation.
From Coq Require Import Relations.
From Coq Require Import FunctionalExtensionality.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From FinCert.Meta Require Import ContractMorphisms.
From FinCert.Meta Require Import ContractSystems.

Import ListNotations.

(** Bisimulations of individual contracts *)
Section ContractBisimulations.
Context {Base : ChainBase}.

(** Contract trace morphisms, or functions between contract traces *)
Section ContractTraceMorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

Record ContractTraceMorphism
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) :=
    build_ct_morph {
        (* a function *)
        ct_state_morph : State1 -> State2 ;
        (* init state C1 -> init state C2 *)
        genesis_fixpoint : forall init_cstate,
            is_genesis_cstate C1 init_cstate ->
            is_genesis_cstate C2 (ct_state_morph init_cstate) ;
        (* coherence *)
        cstep_morph : forall state1 state2,
            ContractStep C1 state1 state2 ->
            ContractStep C2 (ct_state_morph state1) (ct_state_morph state2) ;
    }.

End ContractTraceMorphism.


(** The identity trace morphism *)
Section IdentityCTMorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}.

Definition id_genesis_fixpoint (C : Contract Setup1 Msg1 State1 Error1)
    init_cstate
    (gen_C : is_genesis_cstate C init_cstate) :
    is_genesis_cstate C (id init_cstate) := 
    gen_C.

Definition id_cstep_morph (C : Contract Setup1 Msg1 State1 Error1)
    state1 state2
    (step : ContractStep C state1 state2) :
    ContractStep C (id state1) (id state2) := 
    step.

Definition id_ctm (C : Contract Setup1 Msg1 State1 Error1) : ContractTraceMorphism C C := {|
    ct_state_morph := id ;
    genesis_fixpoint := id_genesis_fixpoint C ;
    cstep_morph := id_cstep_morph C ;
|}.

End IdentityCTMorphism.


(** Equality on trace morphisms *)
Section EqualityOfCTMorphisms.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

Lemma eq_ctm_dep 
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2)
    (ct_st_m : State1 -> State2) 
    (gen_fix1 gen_fix2 : forall init_cstate,
        is_genesis_cstate C1 init_cstate ->
        is_genesis_cstate C2 (ct_st_m init_cstate))
    (cstep_m1 cstep_m2 : forall state1 state2,
        ContractStep C1 state1 state2 ->
        ContractStep C2 (ct_st_m state1) (ct_st_m state2)) :
    cstep_m1 = cstep_m2 ->
    {| ct_state_morph := ct_st_m ;
       genesis_fixpoint := gen_fix1 ;
       cstep_morph := cstep_m1 ; |}
    = 
    {| ct_state_morph := ct_st_m ;
       genesis_fixpoint := gen_fix2 ;
       cstep_morph := cstep_m2 ; |}.
Proof.
    intro cstep_equiv.
    subst.
    f_equal.
    apply proof_irrelevance.
Qed.

End EqualityOfCTMorphisms.


(** Composition of trace morphisms *)
Section CTMorphismComposition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}
        {C3 : Contract Setup3 Msg3 State3 Error3}.

Definition genesis_compose (m2 : ContractTraceMorphism C2 C3) (m1 : ContractTraceMorphism C1 C2)
    init_cstate (gen_C1 : is_genesis_cstate C1 init_cstate) :
    is_genesis_cstate C3 (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) init_cstate) :=
  match m2 with
  | build_ct_morph _ _ _ gen_fix2 step2 =>
      match m1 with
      | build_ct_morph _ _ _ gen_fix1 step1 =>
          gen_fix2 _ (gen_fix1 _ gen_C1)
      end
  end.

Definition cstep_compose (m2 : ContractTraceMorphism C2 C3) (m1 : ContractTraceMorphism C1 C2)
    state1 state2 (step : ContractStep C1 state1 state2) :
    ContractStep C3
        (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) state1)
        (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) state2) :=
  match m2, m1 with
  | build_ct_morph _ _ _ _ step2, build_ct_morph _ _ _ _ step1 =>
          step2 _ _ (step1 _ _ step)
  end.

Definition compose_ctm
    (m2 : ContractTraceMorphism C2 C3) 
    (m1 : ContractTraceMorphism C1 C2) : ContractTraceMorphism C1 C3 := 
{|
    ct_state_morph := compose (ct_state_morph _ _ m2) (ct_state_morph _ _ m1) ; 
    genesis_fixpoint := genesis_compose m2 m1 ;
    cstep_morph := cstep_compose m2 m1 ;
|}.

End CTMorphismComposition.


(** Some results on trace composition *)
Section CTMorphismCompositionResults.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Setup4} `{Serializable Msg4} `{Serializable State4} `{Serializable Error4}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }
        { C4 : Contract Setup4 Msg4 State4 Error4 }.

(* Composition is associative *)
Lemma compose_ctm_assoc 
    (f : ContractTraceMorphism C1 C2)
    (g : ContractTraceMorphism C2 C3)
    (h : ContractTraceMorphism C3 C4) : 
    compose_ctm h (compose_ctm g f) = 
    compose_ctm (compose_ctm h g) f.
Proof. now destruct f, g, h. Qed.

(* Composition with the identity is trivial *)
Lemma compose_id_ctm_left (f : ContractTraceMorphism C1 C2) :
    compose_ctm (id_ctm C2) f = f.
Proof. now destruct f. Qed.

Lemma compose_id_ctm_right (f : ContractTraceMorphism C1 C2) :
    compose_ctm f (id_ctm C1) = f.
Proof. now destruct f. Qed.

End CTMorphismCompositionResults.


(** Contract morphisms lift to contract trace morphisms *)
Section LiftingTheorem.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition lift_genesis (f : ContractMorphism C1 C2) : 
    forall init_cstate,
        is_genesis_cstate C1 init_cstate ->
        is_genesis_cstate C2 (state_morph C1 C2 f init_cstate).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph i_coh r_coh].
    cbn.
    intros * genesis. 
    unfold is_genesis_cstate in *.
    destruct genesis as [c [ctx [s init_coh]]].
    exists c, ctx, (setup_morph s).
    rewrite <- i_coh.
    unfold result_functor.
    now destruct (init C1 c ctx s).
Defined.

Definition lift_cstep_morph (f : ContractMorphism C1 C2) : 
    forall state1 state2,
        ContractStep C1 state1 state2 ->
        ContractStep C2 
            (state_morph C1 C2 f state1) 
            (state_morph C1 C2 f state2).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph i_coh r_coh].
    cbn.
    intros * step.
    destruct step as [seq_chain seq_ctx seq_msg seq_new_acts recv_step].
    apply (build_contract_step C2 (state_morph state1) (state_morph state2) seq_chain seq_ctx 
        (option_map msg_morph seq_msg) seq_new_acts).
    rewrite <- r_coh.
    unfold result_functor.
    destruct (receive C1 seq_chain seq_ctx state1 seq_msg);
    try destruct t;
    now inversion recv_step.
Defined.

(** Lifting Theorem *)
Definition cm_lift_ctm (f : ContractMorphism C1 C2) : ContractTraceMorphism C1 C2 :=
    build_ct_morph _ _ (state_morph _ _ f) (lift_genesis f) (lift_cstep_morph f).

End LiftingTheorem.


(** Some results on lifting *)
Section LiftingTheoremResults.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}
        {C3 : Contract Setup3 Msg3 State3 Error3}.

(* id lifts to id *)
Theorem cm_lift_ctm_id :
    cm_lift_ctm (id_cm C1) = id_ctm C1.
Proof.
    unfold cm_lift_ctm, id_ctm.
    simpl.
    apply (eq_ctm_dep C1 C1 (@id State1)).
    apply functional_extensionality_dep.
    intro st1.
    apply functional_extensionality_dep.
    intro st1'.
    apply functional_extensionality_dep.
    intro cstep.
    destruct cstep as [s_chn s_ctx s_msg s_nacts s_recv].
    unfold id_cstep_morph.
    cbn.
    unfold option_map.
    destruct s_msg;
    cbn;
    f_equal;
    apply proof_irrelevance.
Qed.

(* compositions lift to compositions *)
Theorem cm_lift_ctm_compose 
    (g : ContractMorphism C2 C3) (f : ContractMorphism C1 C2) : 
    cm_lift_ctm (compose_cm g f) = 
    compose_ctm (cm_lift_ctm g) (cm_lift_ctm f).
Proof.
    unfold cm_lift_ctm, compose_ctm.
    cbn.
    apply (eq_ctm_dep C1 C3 (compose (state_morph C2 C3 g) (state_morph C1 C2 f))).
    apply functional_extensionality_dep.
    intro st1.
    apply functional_extensionality_dep.
    intro st1'.
    apply functional_extensionality_dep.
    intro cstep.
    destruct cstep as [s_chn s_ctx s_msg s_nacts s_recv].
    unfold lift_cstep_morph.
    destruct g as [smorph_g msgmorph_g stmorph_g errmorph_g initcoh_g recvcoh_g].
    destruct f as [smorph_f msgmorph_f stmorph_f errmorph_f initcoh_f recvcoh_f].
    cbn.
    destruct s_msg;
    cbn;
    f_equal;
    apply proof_irrelevance.
Qed.

End LiftingTheoremResults.


(* define contract bisimulations with contract traces *)
Section ContractBisimulation.

Section ContractTraceIsomorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

(* a bisimulation of contracts, or an isomorphism of contract traces *)
Definition is_iso_ctm 
    (m1 : ContractTraceMorphism C1 C2) (m2 : ContractTraceMorphism C2 C1) := 
    compose_ctm m2 m1 = id_ctm C1 /\
    compose_ctm m1 m2 = id_ctm C2.

(* contract isomorphism -> contract trace isomorphism *)
Corollary ciso_to_ctiso (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) :
    is_iso_cm f g -> is_iso_ctm (cm_lift_ctm f) (cm_lift_ctm g).
Proof.
    unfold is_iso_cm, is_iso_ctm.
    intro iso_cm.
    destruct iso_cm as [iso_cm_l iso_cm_r].
    rewrite <- (cm_lift_ctm_compose g f).
    rewrite <- (cm_lift_ctm_compose f g).
    rewrite iso_cm_l.
    rewrite iso_cm_r.
    now repeat rewrite cm_lift_ctm_id.
Qed.

End ContractTraceIsomorphism.


Definition contracts_bisimilar 
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) :=
    exists (f : ContractTraceMorphism C1 C2) (g : ContractTraceMorphism C2 C1),
    is_iso_ctm f g.

(* bisimilarity is an equivalence relation *)
Lemma bisim_refl 
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    contracts_bisimilar C C.
Proof.
    exists (id_ctm C), (id_ctm C).
    unfold is_iso_ctm.
    split; apply compose_id_ctm_left.
Qed.

Lemma bisim_sym 
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) :
    contracts_bisimilar C1 C2 ->
    contracts_bisimilar C2 C1.
Proof.
    intro c_bisim.
    unfold contracts_bisimilar in *.
    destruct c_bisim as [f [f' iso_f_g]].
    exists f', f.
    unfold is_iso_ctm in *.
    destruct iso_f_g as [f_id1 f_id2].
    split.
    -   apply f_id2.
    -   apply f_id1.
Qed.

Lemma bisim_trans
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
    {C1 : Contract Setup1 Msg1 State1 Error1}
    {C2 : Contract Setup2 Msg2 State2 Error2}
    {C3 : Contract Setup3 Msg3 State3 Error3} :
    contracts_bisimilar C1 C2 /\ contracts_bisimilar C2 C3 ->
    contracts_bisimilar C1 C3.
Proof.
    intros c_bisims.
    destruct c_bisims as [[f [f' iso_f]] [g [g' iso_g]]].
    unfold contracts_bisimilar in *.
    exists (compose_ctm g f), (compose_ctm f' g').
    destruct iso_g as [g_id1 g_id2].
    destruct iso_f as [f_id1 f_id2].
    unfold is_iso_ctm.
    split.
    -   rewrite <- compose_ctm_assoc.
        replace (compose_ctm g' (compose_ctm g f)) with (compose_ctm (compose_ctm g' g) f).
        2:{ now rewrite <- compose_ctm_assoc. }
        rewrite g_id1.
        rewrite compose_id_ctm_left.
        apply f_id1.
    -   rewrite <- compose_ctm_assoc.
        replace (compose_ctm f (compose_ctm f' g')) with (compose_ctm (compose_ctm f f') g').
        2:{ now rewrite <- compose_ctm_assoc. }
        rewrite f_id2.
        rewrite compose_id_ctm_left.
        apply g_id2.
Qed.

(* an isomorphism of contracts lifts to a bisimulation *)
Theorem c_iso_to_bisim
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    {C1 : Contract Setup1 Msg1 State1 Error1}
    {C2 : Contract Setup2 Msg2 State2 Error2} :
    contracts_isomorphic C1 C2 -> contracts_bisimilar C1 C2.
Proof.
    intro c_iso.
    destruct c_iso as [f [g [is_iso_1 is_iso_2]]].
    unfold contracts_bisimilar.
    exists (cm_lift_ctm f), (cm_lift_ctm g).
    unfold is_iso_ctm.
    split;
    rewrite <- cm_lift_ctm_compose;
    try rewrite is_iso_1;
    try rewrite is_iso_2;
    now rewrite cm_lift_ctm_id.
Qed.

End ContractBisimulation.

End ContractBisimulations.


(** Bisimulations of systems of contracts, encoded as n-trees *)
Section SystemBisimulations.
Context {Base : ChainBase}.

(** Define the notion of a contract system's trace, which is a chained list of 
    a chained list of successful system calls *)
Section SystemTrace.

Section SingleSteps.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}.

(* system state stepping forward *)
Record SingleSystemStep (sys : ContractPlaceGraph Setup Msg State Error)
    (prev_sys_state next_sys_state : State) :=
    build_sys_single_step {
    sys_step_chain : Chain ;
    sys_step_ctx : ContractCallContext ;
    sys_step_msg : option Msg ;
    sys_step_nacts : list ActionBody ;
    (* we can call receive successfully *)
    sys_recv_ok_step :
        sys_receive sys sys_step_chain sys_step_ctx prev_sys_state sys_step_msg =
        Ok (next_sys_state, sys_step_nacts) ;
}.

Definition ChainedSingleSteps (sys : ContractPlaceGraph Setup Msg State Error) :=
    ChainedList State (SingleSystemStep sys).

End SingleSteps.

Record ContractSystem
    (Setup Msg State Error : Type)
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st  : Serializable State}
    `{sys_err : Serializable Error} := 
    build_contract_system {
        sys_place : ContractPlaceGraph Setup Msg State Error ;
        sys_link  : State -> State -> Type ;
        (* the link graph has semantics in ChanedSingleSteps *)
        sys_link_semantics : forall st1 st2,
            sys_link st1 st2 -> 
            ChainedSingleSteps sys_place st1 st2 ;
    }.

Context `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}.

Section Aux.

Definition sys_place' (sys : ContractSystem Setup Msg State Error) :=
    sys_place _ _ _ _ sys.

Definition sys_link' (sys : ContractSystem Setup Msg State Error) :=
    sys_link _ _ _ _ sys.

Definition sys_link_semantics' (sys : ContractSystem Setup Msg State Error) :=
    sys_link_semantics _ _ _ _ sys.

End Aux.

Definition SystemStep (sys : ContractSystem Setup Msg State Error) :=
    sys_link' sys.

Definition SystemTrace (sys : ContractSystem Setup Msg State Error) :=
    ChainedList State (SystemStep sys).

Definition is_genesis_sys_state
    (sys : ContractSystem Setup Msg State Error) (init_sys_state : State) : Prop :=
    exists sys_init_chain sys_init_ctx sys_init_setup,
    sys_init (sys_place' sys) sys_init_chain sys_init_ctx sys_init_setup =
    Ok init_sys_state.

Definition sys_state_reachable
    (sys : ContractSystem Setup Msg State Error) (sys_state : State) : Prop :=
    exists init_sys_state,
    (* init_sys_state is a valid initial sys_state *)
    is_genesis_sys_state sys init_sys_state /\
    (* with a trace to sys_state *)
    inhabited (SystemTrace sys init_sys_state sys_state).

Lemma inhab_trace_trans (sys : ContractSystem Setup Msg State Error) :
forall from mid to,
    (SystemStep sys mid to) ->
    inhabited (SystemTrace sys from mid) ->
    inhabited (SystemTrace sys from to).
Proof.
    intros from mid to step.
    apply inhabited_covariant.
    intro mid_t.
    apply (snoc mid_t step).
Qed.

End SystemTrace.


Section SystemTraceMorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

Record SystemTraceMorphism
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :=
    build_st_morph {
        (* a function *)
        st_state_morph : State1 -> State2 ;
        (* init state sys1 -> init state sys2 *)
        sys_genesis_fixpoint : forall init_sys_state,
            is_genesis_sys_state sys1 init_sys_state ->
            is_genesis_sys_state sys2 (st_state_morph init_sys_state) ;
        (* step morphism *)
        sys_step_morph : forall sys_state1 sys_state2,
            SystemStep sys1 sys_state1 sys_state2 ->
            SystemStep sys2 (st_state_morph sys_state1) (st_state_morph sys_state2) ;
    }.

End SystemTraceMorphism.


(** The identity system trace morphism *)
Section IdentitySTMorphism.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}.

Definition id_sys_genesis_fixpoint (sys : ContractSystem Setup Msg State Error) :
    forall init_sys_state,
    is_genesis_sys_state sys init_sys_state ->
    is_genesis_sys_state sys (id init_sys_state).
Proof. auto. Defined.

Definition id_sys_step_morph (sys : ContractSystem Setup Msg State Error)
    sys_state1 sys_state2 (step : SystemStep sys sys_state1 sys_state2) :
    SystemStep sys (id sys_state1) (id sys_state2) :=
    step.

Definition id_stm (sys : ContractSystem Setup Msg State Error) : SystemTraceMorphism sys sys := 
{| 
    st_state_morph := id ;
    sys_genesis_fixpoint := id_sys_genesis_fixpoint sys ;
    sys_step_morph := id_sys_step_morph sys ;
|}.

End IdentitySTMorphism.


(* Equality on system trace morphisms *)
Section EqualityOfSTMorphisms.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

Lemma eq_stm_dep
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2)
    (st_st_m : State1 -> State2)
    sys_gen_fix1 sys_gen_fix2
    (sys_step_m1 sys_step_m2 : forall sys_state1 sys_state2,
        SystemStep sys1 sys_state1 sys_state2 ->
        SystemStep sys2 (st_st_m sys_state1) (st_st_m sys_state2)) : 
    sys_step_m1 = sys_step_m2 ->
    {| st_state_morph := st_st_m ;
       sys_genesis_fixpoint := sys_gen_fix1 ;
       sys_step_morph := sys_step_m1 ; |}
    = 
    {| st_state_morph := st_st_m ;
       sys_genesis_fixpoint := sys_gen_fix2 ;
       sys_step_morph := sys_step_m2 ; |}.
Proof.
    intro cstep_equiv.
    subst.
    f_equal.
    apply proof_irrelevance.
Qed.

End EqualityOfSTMorphisms.


Section STMorphismComposition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        {sys1 : ContractSystem Setup1 Msg1 State1 Error1}
        {sys2 : ContractSystem Setup2 Msg2 State2 Error2}
        {sys3 : ContractSystem Setup3 Msg3 State3 Error3}.

Definition sys_genesis_compose
    (m2 : SystemTraceMorphism sys2 sys3) (m1 : SystemTraceMorphism sys1 sys2)
    init_sys_state (gen_s1 : is_genesis_sys_state sys1 init_sys_state) :
    is_genesis_sys_state sys3
        (compose (st_state_morph sys2 sys3 m2) (st_state_morph sys1 sys2 m1) init_sys_state) :=
    match m2, m1 with 
    | build_st_morph _ _ _ gen_fix2 step2, build_st_morph _ _ _ gen_fix1 step1 => 
        gen_fix2 _ (gen_fix1 _ gen_s1)
    end.

Definition sys_step_compose
    (m2 : SystemTraceMorphism sys2 sys3) (m1 : SystemTraceMorphism sys1 sys2)
    sys_state1 sys_state2
    (step : SystemStep sys1 sys_state1 sys_state2) :
    SystemStep sys3
        (compose (st_state_morph sys2 sys3 m2) (st_state_morph sys1 sys2 m1) sys_state1)
        (compose (st_state_morph sys2 sys3 m2) (st_state_morph sys1 sys2 m1) sys_state2) :=
    match m2, m1 with
    | build_st_morph _ _ _ _ step2, build_st_morph _ _ _ _ step1 =>
        step2 _ _ (step1 _ _ step)
    end.

Definition compose_stm
    (m2 : SystemTraceMorphism sys2 sys3)
    (m1 : SystemTraceMorphism sys1 sys2) : SystemTraceMorphism sys1 sys3 :=
{| 
    st_state_morph := compose (st_state_morph _ _ m2) (st_state_morph _ _ m1) ;
    sys_genesis_fixpoint := sys_genesis_compose m2 m1 ;
    sys_step_morph := sys_step_compose m2 m1 ;
|}.

End STMorphismComposition.


(** Some results on trace composition *)
Section STMorphismCompositionResults.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Setup4} `{Serializable Msg4} `{Serializable State4} `{Serializable Error4}
        { sys1 : ContractSystem Setup1 Msg1 State1 Error1}
        { sys2 : ContractSystem Setup2 Msg2 State2 Error2}
        { sys3 : ContractSystem Setup3 Msg3 State3 Error3}
        { sys4 : ContractSystem Setup4 Msg4 State4 Error4}.

(* Composition is associative *)
Lemma compose_stm_assoc
    (f : SystemTraceMorphism sys1 sys2)
    (g : SystemTraceMorphism sys2 sys3)
    (h : SystemTraceMorphism sys3 sys4) :
    compose_stm h (compose_stm g f) =
    compose_stm (compose_stm h g) f.
Proof. now destruct f, g, h. Qed.

(* Composition with the identity is trivial *)
Lemma compose_id_stm_left (f : SystemTraceMorphism sys1 sys2) :
    compose_stm (id_stm sys2) f = f.
Proof. now destruct f. Qed.

Lemma compose_id_stm_right (f : SystemTraceMorphism sys1 sys2) :
    compose_stm f (id_stm sys1) = f.
Proof. now destruct f. Qed.

End STMorphismCompositionResults.


(** System morphisms lift to system trace morphisms with the trivial link graph *)
Section LiftingTheorem.

Section TrivialLinkSys.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}.

Definition triv_link (sys : ContractPlaceGraph Setup Msg State Error) st1 st2 := 
    SingleSystemStep sys st1 st2.

Definition trivial_link_semantics (sys : ContractPlaceGraph Setup Msg State Error) 
    st1 st2 (step : triv_link sys st1 st2) :
    ChainedSingleSteps sys st1 st2 :=
    (snoc clnil step).

Definition trivial_sys (sys : ContractPlaceGraph Setup Msg State Error) := {|
    sys_place := sys ;
    sys_link := triv_link sys ;
    sys_link_semantics := trivial_link_semantics sys ; 
|}.

End TrivialLinkSys.

Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {sys1 : ContractPlaceGraph Setup1 Msg1 State1 Error1}
        {sys2 : ContractPlaceGraph Setup2 Msg2 State2 Error2}.

Definition lift_sys_genesis (f : SystemMorphism sys1 sys2) :
    forall init_sys_state,
        is_genesis_sys_state (trivial_sys sys1) init_sys_state ->
        is_genesis_sys_state (trivial_sys sys2) (sys_state_morph sys1 sys2 f init_sys_state).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph i_coh r_coh].
    cbn.
    intros * genesis.
    unfold is_genesis_sys_state in *.
    destruct genesis as [c [ctx [s init_coh]]].
    exists c, ctx, (setup_morph s).
    rewrite <- i_coh.
    cbn in init_coh.
    unfold result_functor.
    now destruct (sys_init sys1 c ctx s).
Defined.

Definition lift_sys_step_morph (f : SystemMorphism sys1 sys2) :
    forall sys_state1 sys_state2,
        SystemStep (trivial_sys sys1) sys_state1 sys_state2 ->
        SystemStep (trivial_sys sys2)
            (sys_state_morph sys1 sys2 f sys_state1)
            (sys_state_morph sys1 sys2 f sys_state2).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph i_coh r_coh].
    cbn.
    intros * step.
    destruct step as [seq_chain seq_ctx seq_msg seq_new_acts recv_step].
    apply (build_sys_single_step sys2 (state_morph sys_state1) (state_morph sys_state2)
        seq_chain seq_ctx (option_map msg_morph seq_msg) seq_new_acts).
    rewrite <- r_coh.
    unfold result_functor.
    destruct (sys_receive sys1 seq_chain seq_ctx sys_state1 seq_msg);
    try destruct t;
    now inversion recv_step.
Defined.

(** Lifting Theorem *)
Definition sm_lift_stm (f : SystemMorphism sys1 sys2) : 
    SystemTraceMorphism (trivial_sys sys1) (trivial_sys sys2) :=
    build_st_morph _ _ (sys_state_morph _ _ f) (lift_sys_genesis f) (lift_sys_step_morph f).

End LiftingTheorem.


(** Some results on lifting *)
Section LiftingTheoremResults.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        {sys1 : ContractPlaceGraph Setup1 Msg1 State1 Error1}
        {sys2 : ContractPlaceGraph Setup2 Msg2 State2 Error2}
        {sys3 : ContractPlaceGraph Setup3 Msg3 State3 Error3}.

(* id lifts to id *)
Theorem sm_lift_stm_id : 
    sm_lift_stm (id_sm sys1) = id_stm (trivial_sys sys1).
Proof.
    apply (eq_stm_dep (trivial_sys sys1) (trivial_sys sys1) (@id State1)).
    apply functional_extensionality_dep.
    intro st1.
    apply functional_extensionality_dep.
    intro st1'.
    apply functional_extensionality_dep.
    intro sys_step.
    destruct sys_step.
    unfold lift_sys_step_morph, id_sm, trivial_sys, option_map, id_sys_step_morph.
    cbn.
    do 2 f_equal; auto.
    destruct sys_step_msg0;
    apply f_equal;
    apply proof_irrelevance.
Qed.

(* compositions lift to compositions *)
Theorem sm_lift_stm_compose 
    (g : SystemMorphism sys2 sys3) (f : SystemMorphism sys1 sys2) :
    sm_lift_stm (compose_sm g f) =
    compose_stm (sm_lift_stm g) (sm_lift_stm f).
Proof.
    apply (eq_stm_dep (trivial_sys sys1) (trivial_sys sys3)
        (compose (sys_state_morph sys2 sys3 g) (sys_state_morph sys1 sys2 f))).
    apply functional_extensionality_dep.
    intro st1.
    apply functional_extensionality_dep.
    intro st1'.
    apply functional_extensionality_dep.
    intro sys_step.
    induction sys_step.
    destruct g as [smorph_g msgmorph_g stmorph_g errmorph_g initcoh_g recvcoh_g].
    destruct f as [smorph_f msgmorph_f stmorph_f errmorph_f initcoh_f recvcoh_f].
    unfold lift_sys_step_morph, sys_step_compose, compose_sm.
    destruct sys_step_msg0;
    cbn;
    f_equal;
    apply proof_irrelevance.
Qed.

End LiftingTheoremResults.


(* System Bisimulations *)
Section SystemBisimulation.

Section SystemTraceIsomorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {sys1 : ContractSystem Setup1 Msg1 State1 Error1}
        {sys2 : ContractSystem Setup2 Msg2 State2 Error2}.

(** A bisimulation of systems, or an isomorphism of system traces *)
Definition is_iso_stm
    (m1 : SystemTraceMorphism sys1 sys2) (m2 : SystemTraceMorphism sys2 sys1) :=
    compose_stm m2 m1 = id_stm sys1 /\
    compose_stm m1 m2 = id_stm sys2.

End SystemTraceIsomorphism.


Section IsomorphismLift.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {sys1 : ContractPlaceGraph Setup1 Msg1 State1 Error1}
        {sys2 : ContractPlaceGraph Setup2 Msg2 State2 Error2}.

(* system isomorphism -> system trace isomorphism *)
Corollary siso_to_stiso (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1) :
    is_iso_sm f g -> is_iso_stm (sm_lift_stm f) (sm_lift_stm g).
Proof.
    unfold is_iso_sm, is_iso_stm.
    intro iso_sm.
    destruct iso_sm as [iso_sm_l iso_sm_r].
    rewrite <- (sm_lift_stm_compose g f).
    rewrite <- (sm_lift_stm_compose f g).
    rewrite iso_sm_l.
    rewrite iso_sm_r.
    now repeat rewrite sm_lift_stm_id.
Qed.

End IsomorphismLift.


Definition systems_bisimilar 
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :=
    exists (f : SystemTraceMorphism sys1 sys2) (g : SystemTraceMorphism sys2 sys1),
    is_iso_stm f g.

(* bisimilarity is an equivalence relation *)
Lemma sys_bisim_refl
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    (sys : ContractSystem Setup Msg State Error) :
    systems_bisimilar sys sys.
Proof.
    exists (id_stm sys), (id_stm sys).
    unfold is_iso_stm.
    split; apply compose_id_stm_left.
Qed.

Lemma sys_bisim_sym
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :
    systems_bisimilar sys1 sys2 ->
    systems_bisimilar sys2 sys1.
Proof.
    intro sys_bisim.
    unfold systems_bisimilar in *.
    destruct sys_bisim as [f [f' iso]].
    exists f', f.
    unfold is_iso_stm in *.
    destruct iso as [f_id1 f_id2].
    split.
    -   apply f_id2.
    -   apply f_id1.
Qed.

Lemma iso_stm_trans
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
    {sys1 : ContractSystem Setup1 Msg1 State1 Error1}
    {sys2 : ContractSystem Setup2 Msg2 State2 Error2}
    {sys3 : ContractSystem Setup3 Msg3 State3 Error3} :
    systems_bisimilar sys1 sys2 /\ systems_bisimilar sys2 sys3 ->
    systems_bisimilar sys1 sys3.
Proof.
    intros sys_bisims.
    destruct sys_bisims as [[f [f' [f_id1 f_id2]]] [g [g' [g_id1 g_id2]]]].
    unfold systems_bisimilar in *.
    exists (compose_stm g f), (compose_stm f' g').
    unfold is_iso_stm.
    split.
    -   rewrite <- compose_stm_assoc.
        replace (compose_stm g' (compose_stm g f)) with (compose_stm (compose_stm g' g) f).
        2:{ now rewrite <- compose_stm_assoc. }
        rewrite g_id1.
        rewrite compose_id_stm_left.
        apply f_id1.
    -   rewrite <- compose_stm_assoc.
        replace (compose_stm f (compose_stm f' g')) with (compose_stm (compose_stm f f') g').
        2:{ now rewrite <- compose_stm_assoc. }
        rewrite f_id2.
        rewrite compose_id_stm_left.
        apply g_id2.
Qed.

(* an isomorphism of systems lifts to a bisimulation *)
Theorem sys_iso_to_bisim
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    {sys1 : ContractPlaceGraph Setup1 Msg1 State1 Error1}
    {sys2 : ContractPlaceGraph Setup2 Msg2 State2 Error2} :
    systems_isomorphic sys1 sys2 -> systems_bisimilar (trivial_sys sys1) (trivial_sys sys2).
Proof.
    intro sys_iso.
    destruct sys_iso as [f [g [is_iso_1 is_iso_2]]].
    unfold systems_bisimilar.
    exists (sm_lift_stm f), (sm_lift_stm g).
    unfold is_iso_stm.
    split;
    rewrite <- sm_lift_stm_compose;
    try rewrite is_iso_1;
    try rewrite is_iso_2;
    now rewrite sm_lift_stm_id.
Qed.

(* a contract lifts to a morphism of singleton systems *)
Section CMtoSM.

Section LiftCMtoSM.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1}
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition lift_cm_to_sm (f : ContractMorphism C1 C2) :
    SystemMorphism (singleton_sys C1) (singleton_sys C2).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph init_coherence recv_coherence].
    apply (build_system_morphism (singleton_sys C1) (singleton_sys C2)
        setup_morph msg_morph state_morph error_morph);
    unfold singleton_sys, singleton_ntree, sys_init, sys_receive, ntree_fold_left in *.
    -   apply init_coherence.
    -   intros.
        rewrite <- recv_coherence.
        cbn.
        now destruct (receive C1 c ctx st op_msg).
Defined.

Definition lift_ctm_to_stm (f : ContractTraceMorphism C1 C2) :
    SystemTraceMorphism (trivial_sys (singleton_sys C1)) (trivial_sys (singleton_sys C2)).
Proof.
    destruct f as [ct_st_morph gen_fixp cstep_morph].
    apply (build_st_morph 
        (trivial_sys (singleton_sys C1)) (trivial_sys (singleton_sys C2)) ct_st_morph);
    unfold singleton_sys, singleton_ntree, sys_init, sys_receive, ntree_fold_left in *.
    -   apply gen_fixp.
    -   intros * step.
        assert (ContractStep C2 (ct_st_morph sys_state1) (ct_st_morph sys_state2)
        -> SingleSystemStep (Node (Contract Setup2 Msg2 State2 Error2) C2 []) 
        (ct_st_morph sys_state1) (ct_st_morph sys_state2))
        as H_step.
        {   intro cstep.
            destruct cstep as [c ctx msg nacts recv_ok].
            apply (build_sys_single_step _ _ _ c ctx msg nacts).
            unfold sys_receive.
            cbn.
            destruct (receive C2 c ctx (ct_st_morph sys_state1) msg); auto.
            now destruct t. }
        apply H_step, cstep_morph.
        clear H_step.
        destruct step as [c ctx msg nacts recv_ok].
        apply (build_contract_step C1 sys_state1 sys_state2 c ctx msg nacts).
        unfold sys_receive in recv_ok.
        cbn in *.
        destruct (receive C1 c ctx sys_state1 msg); auto.
        destruct t.
        now inversion recv_ok.
Defined.

End LiftCMtoSM.

(* id lifts to id *)
Lemma lift_id_cm_to_id_sm 
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    {C : Contract Setup Msg State Error} : 
    lift_cm_to_sm (id_cm C) = id_sm (singleton_sys C).
Proof.
    unfold lift_cm_to_sm, id_cm, id_sm, singleton_sys.
    cbn.
    f_equal;
    apply proof_irrelevance.
Qed.

(* compositions lift to compositions *)
Lemma lift_cm_to_sm_comp
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
    {C1 : Contract Setup1 Msg1 State1 Error1}
    {C2 : Contract Setup2 Msg2 State2 Error2}
    {C3 : Contract Setup3 Msg3 State3 Error3}
    (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C3) :
    lift_cm_to_sm (compose_cm g f) = compose_sm (lift_cm_to_sm g) (lift_cm_to_sm f).
Proof.
    destruct g as [smorph_g msgmorph_g stmorph_g errmorph_g initcoh_g recvcoh_g].
    destruct f as [smorph_f msgmorph_f stmorph_f errmorph_f initcoh_f recvcoh_f].
    unfold compose_cm, compose_sm, lift_cm_to_sm.
    cbn.
    f_equal;
    apply proof_irrelevance.
Qed.

(* isomorphic contracts => isomorphic singleton systems *)
Lemma c_iso_csys_iso
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    {C1 : Contract Setup1 Msg1 State1 Error1}
    {C2 : Contract Setup2 Msg2 State2 Error2} :
    contracts_isomorphic C1 C2 -> 
    systems_isomorphic (singleton_sys C1) (singleton_sys C2).
Proof.
    intro c_iso.
    destruct c_iso as [f [g [is_iso_1 is_iso_2]]].
    unfold systems_isomorphic.
    exists (lift_cm_to_sm f), (lift_cm_to_sm g).
    unfold is_iso_sm.
    split;
    rewrite <- lift_cm_to_sm_comp;
    try rewrite is_iso_1;
    try rewrite is_iso_2;
    now rewrite lift_id_cm_to_id_sm.
Qed.

End CMtoSM.

End SystemBisimulation.

End SystemBisimulations.