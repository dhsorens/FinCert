From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ChainedList.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ProofIrrelevance.
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

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** An example of a system of contracts, where an backend contract is nested 
    with an interface contract. The tree structure would be something like:
    
        C_interface
             /
         C_backend
    
    Under the condition of a link graph specification, these contracts are 
*)

Section InterfaceBackend.
Context { Base : ChainBase }.
Context {interface_caddr backend_caddr : Address}.

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* the various contract types *)
Definition setup := unit.
Inductive entrypoint := 
| incr (n : nat).
Record state := build_state { counter : nat }.
Definition error := nat.

(* for the interface *)
Definition setup_i := unit.
Inductive entrypoint_i := 
| incr_i (n : nat).
(* Record state_i := build_state_i  { backend_address : Address }. *)
Definition state_i := unit.
Definition error_i := nat.

(* for the backend *)
Definition setup_b := unit.
Inductive entrypoint_b := 
| incr_b (n : nat).
(* Record state_b := 
    build_state_b { interface_address : Address ; counter_backend : nat }. *)
Record state_b := 
    build_state_b { counter_backend : nat }.
Definition error_b := nat.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := 
        Derive Serializable entrypoint_rect<incr>.
    Global Instance entrypoint_i_serializable : Serializable entrypoint_i := 
        Derive Serializable entrypoint_i_rect<incr_i>.
    Global Instance entrypoint_b_serializable : Serializable entrypoint_b := 
        Derive Serializable entrypoint_b_rect<incr_b>.
    Global Instance state_serializable : Serializable state := 
        Derive Serializable state_rect<build_state>.
    (* Global Instance state_i_serializable : Serializable state_i := 
        Derive Serializable state_i_rect<build_state_i>.*)
    Global Instance state_b_serializable : Serializable state_b := 
        Derive Serializable state_b_rect<build_state_b>.
End Serialization.


Section Mono.

(* initialize with 0 in storage *)
Definition init 
    (_ : Chain)
    (_ : ContractCallContext)
    (_ : setup) : result state error := 
    Ok (build_state 0).

(* receive *)
Definition receive
    (_ : Chain)
    (_ : ContractCallContext)
    (st : state) 
    (msg : option entrypoint) : result (state * list ActionBody) error :=
    match msg with 
    | Some (incr n) => 
        Ok (build_state (counter st + n), [])
    | None => Err 0%nat
    end.

Definition contract_mono := build_contract init receive.

End Mono.


Section Modular.

Section Interface.

(* initialize with 0 in storage *)
Definition init_i
    (_ : Chain)
    (_ : ContractCallContext)
    (_ : setup_i) : result state_i error_i := 
    Ok tt.

(* receive *)
Definition receive_i
    (_ : Chain)
    (_ : ContractCallContext)
    (st : state_i) 
    (msg : option entrypoint_i) : result (state_i * list ActionBody) error_i :=
    match msg with
    | Some (incr_i n) => 
        let act_incr := act_call backend_caddr 0 (serialize (incr_b n)) in
        Ok (st, [ act_incr ])
    | None => Err 0%nat
    end.

Definition contract_interface := build_contract init_i receive_i.

End Interface.

Section Backend.

(* initialize with 0 in storage *)
Definition init_b
    (_ : Chain)
    (_ : ContractCallContext)
    (_ : setup_b) : result state_b error_b := 
    Ok (build_state_b 0).

(* receive *)
Definition receive_b
    (_ : Chain)
    (ctx : ContractCallContext)
    (st : state_b) 
    (msg : option entrypoint_b) : result (state_b * list ActionBody) error_b :=
    if address_eqb (ctx_from ctx) interface_caddr then 
        match msg with 
        | Some (incr_b n) => 
            Ok (build_state_b (counter_backend st + n), [])
        | None => Err 0%nat
        end
    else Err 0%nat.

Definition contract_backend := build_contract init_b receive_b.

End Backend.

End Modular.

(* the systems in question *)
Definition mono_place := singleton_place_graph contract_mono.
Definition modu_place := nest contract_interface contract_backend.


Section Bisimulation.

Definition permissioned_ctx ctx := {|
    ctx_origin := interface_caddr ;
    ctx_from := interface_caddr ;
    ctx_contract_address := backend_caddr ;
    ctx_contract_balance := ctx_contract_balance ctx ; (* 0? ... *)
    ctx_amount := 0 ;
|}.

Section LinkGraph.

(* The link graph specification for mono : steps are simply single system steps *)
Definition mono_link st1 st2 := SingleSystemStep mono_place st1 st2.

Definition mono_link_semantics st1 st2 (step : mono_link st1 st2) :
    ChainedSingleSteps mono_place st1 st2 := 
    (snoc clnil step).

Definition mono_sys := {|
    sys_place := mono_place ;
    sys_link := mono_link ;
    sys_link_semantics := mono_link_semantics ; 
|}.


(* the link graph specification for modu : steps are a pair of interface/backend calls *)
Inductive modu_link st1 st2 := 
|   step_incr c ctx n
        (interface_ok : sys_receive modu_place c ctx st1 (Some (inl (incr_i n))) = 
                        Ok (st1, [act_call backend_caddr 0 (serialize (incr_b n))]))
        (backend_ok : sys_receive modu_place c (permissioned_ctx ctx) st1 (Some (inr (incr_b n))) =
                        Ok (st2, nil)).

Definition modu_link_semantics st1 st2 (step : modu_link st1 st2) :
    ChainedSingleSteps modu_place st1 st2.
Proof.
    destruct step.
    assert (SingleSystemStep modu_place st1 st1) as call_interface.
    {   apply (build_sys_single_step modu_place st1 st1 c ctx (Some (inl (incr_i n)))
                [act_call backend_caddr 0 (serialize (incr_b n))] interface_ok). }
    assert (SingleSystemStep modu_place st1 st2) as call_backend.
    {   apply (build_sys_single_step modu_place st1 st2 c (permissioned_ctx ctx) (Some (inr (incr_b n)))
                nil backend_ok). }
    apply (snoc (snoc clnil call_interface) call_backend).
Defined.

Definition modu_sys := {|
    sys_place := modu_place ;
    sys_link := modu_link ;
    sys_link_semantics := modu_link_semantics ;
|}.

End LinkGraph.


(* the morphisms *)
(* mono -> modu *)
Definition stm_mono_modu : SystemTraceMorphism mono_sys modu_sys.
Proof.
    apply (build_st_morph mono_sys modu_sys
        (* the function between state types *)
        (fun st =>
            (tt, build_state_b (counter st)))).
    -   intros st gen_mono.
        unfold is_genesis_sys_state in *.
        destruct gen_mono as [c [ctx [s init_ok]]].
        exists c, ctx, (tt, tt).
        unfold sys_init, modu_sys, mono_sys in *.
        cbn in *.
        unfold init in init_ok.
        now inversion init_ok.
    -   intros st1 st2 step.
        destruct step, sys_step_msg.
        2:{ unfold mono_place in *. 
            cbn in *.
            inversion sys_recv_ok_step. }
        destruct e.
        apply (step_incr 
            (tt, {| counter_backend := counter st1 |})
            (tt, {| counter_backend := counter st2 |})
            sys_step_chain
            sys_step_ctx
            n).
        +   auto.
        +   unfold modu_place.
            cbn.
            unfold receive_b, permissioned_ctx.
            cbn.
            rewrite (address_eq_refl interface_caddr).
            do 4 f_equal.
            unfold mono_place in sys_recv_ok_step.
            cbn in sys_recv_ok_step.
            now inversion sys_recv_ok_step.
Defined.


(* modu -> mono *)
Definition stm_modu_mono : SystemTraceMorphism modu_sys mono_sys.
Proof.
    apply (build_st_morph modu_sys mono_sys
        (* the function between state types *)
        (fun '(st_i, st_b) => build_state (counter_backend st_b))).
    -   intros st gen_modu.
        unfold is_genesis_sys_state, mono_sys, modu_sys in *.
        destruct gen_modu as [c [ctx [s init_ok]]].
        exists c, ctx, tt.
        destruct st as [st_i st_b].
        destruct s as [s_i s_b].
        cbn in *.
        unfold sys_init, nest, init in *.
        now inversion init_ok.
    -   intros * step.
        destruct sys_state1 as [st1_i st1_b].
        destruct sys_state2 as [st2_i st2_b].
        destruct step.
        (* just need to build a single system step *)
        apply (build_sys_single_step mono_place 
            {| counter := counter_backend st1_b |} {| counter := counter_backend st2_b |}
            c ctx (Some (incr n)) nil).
        unfold mono_place, modu_place, permissioned_ctx in *.
        cbn in *.
        unfold receive_b in *.
        cbn in *.
        destruct (interface_caddr =? interface_caddr)%address; 
        now inversion backend_ok.
Defined.

Definition aux_fun : forall (init_sys_state : state_i * state_b) (gen_sys : is_genesis_sys_state modu_sys init_sys_state), is_genesis_sys_state modu_sys
(Basics.compose (st_state_morph mono_sys modu_sys stm_mono_modu)
   (st_state_morph modu_sys mono_sys stm_modu_mono) init_sys_state).
Proof.
    assert
            (id = (Basics.compose 
                (st_state_morph mono_sys modu_sys stm_mono_modu)
                (st_state_morph modu_sys mono_sys stm_modu_mono)))
        as H_id_eq.
        {   auto.
            unfold stm_mono_modu, stm_modu_mono.
            cbn.
            apply functional_extensionality.
            simpl.
            intros [sti stb].
            now destruct sti, stb. }
        assert (forall init_sys_state,
            is_genesis_sys_state modu_sys init_sys_state = 
            is_genesis_sys_state modu_sys (Basics.compose 
                        (st_state_morph mono_sys modu_sys stm_mono_modu) 
                        (st_state_morph modu_sys mono_sys stm_modu_mono) init_sys_state))
        as H_gen_eq.
        {   intros [sti stb].
            now rewrite <- H_id_eq. }
    intros * gen_sys.
    rewrite <- (H_gen_eq init_sys_state).
    exact gen_sys.
Defined.

Definition aux_fun2 : forall (sys_state1 sys_state2 : state_i * state_b) (step : SystemStep modu_sys sys_state1 sys_state2), SystemStep modu_sys (Basics.compose (st_state_morph mono_sys modu_sys stm_mono_modu)
(st_state_morph modu_sys mono_sys stm_modu_mono) sys_state1) (Basics.compose (st_state_morph mono_sys modu_sys stm_mono_modu)
(st_state_morph modu_sys mono_sys stm_modu_mono) sys_state2).
Proof.
    assert
            (id = (Basics.compose 
                (st_state_morph mono_sys modu_sys stm_mono_modu)
                (st_state_morph modu_sys mono_sys stm_modu_mono)))
        as H_id_eq.
        {   auto.
            unfold stm_mono_modu, stm_modu_mono.
            cbn.
            apply functional_extensionality.
            simpl.
            intros [sti stb].
        now destruct sti, stb. }
    assert (forall init_sys_state,
        is_genesis_sys_state modu_sys init_sys_state = 
        is_genesis_sys_state modu_sys (Basics.compose 
                    (st_state_morph mono_sys modu_sys stm_mono_modu) 
                    (st_state_morph modu_sys mono_sys stm_modu_mono) init_sys_state))
    as H_gen_eq.
    {   intros [sti stb].
        now rewrite <- H_id_eq. }
    intros * step.
    rewrite <- H_id_eq.
    exact step.
Defined.

(* transport via eq_rect_r *)
(* Check eq_rect_r. *)
Definition transport_id_stm
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    {sys : ContractSystem Setup Msg State Error}
    {st_morph : State -> State}
    (H_id_eq : st_morph = id) : 
    forall sys_state1 sys_state2,
        SystemStep sys sys_state1 sys_state2 ->
        SystemStep sys (st_morph sys_state1) (st_morph sys_state2) :=
    fun st1 st2 step =>
        eq_rect_r
            (fun st_morph : State -> State => SystemStep sys (st_morph st1) (st_morph st2))
            step
            H_id_eq.

(* transport over  *)
Lemma dep_transport
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    (sys : ContractSystem Setup Msg State Error)
    (st_mph : State -> State)
    sys_gen_fix
    (sys_step_m : forall sys_state1 sys_state2,
        SystemStep sys sys_state1 sys_state2 ->
        SystemStep sys (st_mph sys_state1) (st_mph sys_state2))
    (H_id_eq : st_mph = id) :
    (* transport  *)
    sys_step_m = transport_id_stm H_id_eq ->
    {| st_state_morph := st_mph ;
       sys_genesis_fixpoint := sys_gen_fix ;
       sys_step_morph := sys_step_m ; |}
    = id_stm sys.
Admitted.

Theorem mono_modu_bisim : systems_bisimilar mono_sys modu_sys.
Proof.
    unfold systems_bisimilar.
    exists stm_mono_modu, stm_modu_mono.
    unfold is_iso_stm.
    unfold compose_stm, id_stm.
    split.
    (* mono -> mono = id *)
    -   apply (eq_stm_dep mono_sys mono_sys 
            (Basics.compose 
                (st_state_morph modu_sys mono_sys stm_modu_mono)
                (st_state_morph mono_sys modu_sys stm_mono_modu))
            (sys_genesis_compose stm_modu_mono stm_mono_modu)
            (id_sys_genesis_fixpoint mono_sys)).
        apply functional_extensionality_dep.
        intro st1.
        apply functional_extensionality_dep.
        intro st2.
        apply functional_extensionality_dep.
        intro step.
        unfold id_sys_step_morph, sys_step_compose.
        destruct step.
        destruct sys_step_msg;
        cbn.
        +   destruct e.
            pose sys_recv_ok_step as sys_recv_ok2.
            cbn in sys_recv_ok2.
            inversion sys_recv_ok2.
            subst.
            apply f_equal.
            apply proof_irrelevance.
        +   unfold sys_receive, mono_place in sys_recv_ok_step.
            cbn in sys_recv_ok_step.
            inversion sys_recv_ok_step.
    (* modu -> modu = id *)
    -   assert
            (Basics.compose 
                (st_state_morph mono_sys modu_sys stm_mono_modu)
                (st_state_morph modu_sys mono_sys stm_modu_mono) = id)
        as H_id_eq.
        {   auto.
            unfold stm_mono_modu, stm_modu_mono.
            cbn.
            apply functional_extensionality.
            simpl.
            intros [sti stb].
            now destruct sti, stb. }
        apply (dep_transport modu_sys
            (Basics.compose
                (st_state_morph _ _ stm_mono_modu)
                (st_state_morph _ _ stm_modu_mono))
            (sys_genesis_compose stm_mono_modu stm_modu_mono)
            (sys_step_compose stm_mono_modu stm_modu_mono)
            H_id_eq).
        unfold transport_id_stm.
        cbn.
        apply functional_extensionality_dep.
        intros st1.
        apply functional_extensionality_dep.
        intros st2.
        Check eq_rect_r.
        apply functional_extensionality_dep.
        intro link.
        (* rewrite sys_step_compose *)
        destruct link.
        cbn.
        
        (* state a lemma for this *)

        replace (sys_step_compose stm_mono_modu stm_modu_mono st1 st2 link)
        with (sys_step_morph mono_sys modu_sys stm_mono_modu _ _
            (sys_step_morph modu_sys mono_sys stm_modu_mono st1 st2 link)).
        2:{ admit. }

        

        Check (eq_rect_r
        (fun st_morph : state_i * state_b -> state_i * state_b =>
         modu_link (st_morph st1) (st_morph st2)) link H_id_eq).
        with link.

        unfold sys_step_compose.
        
        simpl.
        destruct step.
        
        (* *)
        
        unfold sys_step_compose.
        unfold eq_rect_r, eq_rect.
        
        

        admit.
Admitted.


End Bisimulation.


End InterfaceBackend.