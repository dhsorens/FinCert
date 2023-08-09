From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From FinCert.Meta Require Import ContractMorphisms.
From FinCert.Meta Require Import ContractSystems.
From ConCert.Execution Require Import ChainedList.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Ensembles.
From Coq Require Import ZArith.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.

Import ListNotations.
Open Scope string.

(* an example which unifies an interface contract with its backend *)
Section System.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.


Section Interface.

(* Interface contract types definition *)
Definition setup := unit.
Inductive  entrypoint := | incr (n : nat) | decr (n : nat) | reset.
Record storage := build_storage { backend_address : Address }.
Definition error := nat.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

(* Backend contract types definition *)
Definition setup' := unit.
Inductive  entrypoint' := | incr' (n : nat) | decr' (n : nat) | reset'.
Record storage' := build_storage' { 
        interface_address : Address ;
        counter : nat ; }.
Definition error' := nat.
Definition result' : Type := ResultMonad.result (storage' * list ActionBody) error'.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint :=
        Derive Serializable entrypoint_rect<incr, decr, reset>.
    Global Instance entrypoint'_serializable : Serializable entrypoint' :=
        Derive Serializable entrypoint'_rect<incr', decr', reset'>.
    Global Instance storage_serializable : Serializable storage :=
        Derive Serializable storage_rect<build_storage>.
    Global Instance storage'_serializable : Serializable storage' :=
        Derive Serializable storage'_rect<build_storage'>.
End Serialization.

(* Interface Contract *)
(* init function definition *)
Definition init backend_caddr
                (_ : Chain)
                (_ : ContractCallContext)
                (_ : setup)
                : ResultMonad.result storage error :=
    Ok ({| backend_address := backend_caddr |}).

(* receive function definition *)
Definition receive 
                (_ : Chain)
                (_ : ContractCallContext)
                (st : storage)
                (msg : option entrypoint)
                : result :=
    match msg with 
    | Some (incr n) => 
        let act_fwd := act_call st.(backend_address) 0 (serialize (incr' n)) in 
        Ok (st, [ act_fwd ])
    | Some (decr n) => 
        let act_fwd := act_call st.(backend_address) 0 (serialize (decr' n)) in 
        Ok (st, [ act_fwd ])
    | Some reset => 
        let act_fwd := act_call st.(backend_address) 0 (serialize (reset')) in 
        Ok (st, [ act_fwd ])
    | None => Err 0
    end.

(* construct the contract *)
Definition interface backend_caddr : Contract setup entrypoint storage error := 
    build_contract (init backend_caddr) receive.


(** Backend Contract Definition *)
(* init function definition for C' *)
Definition init' interface_caddr
                (_ : Chain)
                (_ : ContractCallContext)
                (_ : setup')
                : ResultMonad.result storage' error' :=
    let init_storage := {|
        interface_address := interface_caddr ;
        counter := 0 ;
    |} in
    Ok (init_storage).

(* receive function definition for C' *)
Definition receive'
        (_ : Chain)
        (ctx : ContractCallContext)
        (st : storage')
        (msg : option entrypoint')
        : result' :=
    (* check the call comes from the interface contract *)
    if address_eqb ctx.(ctx_from) (interface_address st) then
    (* execute the call *)
    match msg with
    | Some (incr' n) =>
        let st' := {|
            interface_address := (interface_address st) ;
            counter := st.(counter) + 1 ;
        |} in
        Ok (st', [])
    | Some (decr' n) =>
        let st' := {|
            interface_address := (interface_address st) ;
            counter := st.(counter) - 1 ;
        |} in
        Ok (st', [])
    | Some reset' =>
        let st' := {|
            interface_address := (interface_address st) ; 
            counter := 0 ;
        |} in 
        Ok (st', [])
    | None => Err 0
    end
    else Err 0.

(* construct the contract *)
Definition backend interface_caddr : Contract setup' entrypoint' storage' error' := 
    build_contract (init' interface_caddr) receive'.

End Interface.


Section Monolithic.

(* contract types definition for C'' *)
Definition setup'' := unit.
Inductive  entrypoint'' := | incr'' (n : nat) | decr'' (n : nat) | reset''.
Record storage'' := build_storage'' { counter'' : nat ; }.
Definition error'' := nat.
Definition result'' : Type := ResultMonad.result (storage'' * list ActionBody) error''.

Section Serialization.
    Global Instance entrypoint''_serializable : Serializable entrypoint'' := 
        Derive Serializable entrypoint''_rect<incr'',decr'',reset''>.
    Global Instance storage''_serializable : Serializable storage'' :=
        Derive Serializable storage''_rect<build_storage''>.
End Serialization.

(* init function definition for C'' *)
Definition init'' (_ : Chain)
                (_ : ContractCallContext)
                (_ : setup'')
                : ResultMonad.result storage'' error'' := 
    let init_storage := {| 
        counter'' := 0 ; 
    |} in 
    Ok (init_storage).

(* receive function definition for C' *)
Definition receive'' (_ : Chain)
                (_ : ContractCallContext)
                (st : storage'')
                (msg : option entrypoint'')
                : result'' :=
    match msg with 
    | Some (incr'' n) => 
        let st'' := {| 
            counter'' := st.(counter'') + 1 ;
        |} in 
        Ok (st'', [])
    | Some (decr'' n) => 
        let st'' := {| 
            counter'' := st.(counter'') - 1 ;
        |} in
        Ok (st'', [])
    | Some reset'' =>
        let st'' := {|
            counter'' := 0 ;
        |} in 
        Ok (st'', [])
    | None => Err 0
    end.

(* construct the contract *)
Definition mono : Contract setup'' entrypoint'' storage'' error'' := 
    build_contract init'' receive''.

End Monolithic.


Section SystemBisimulation.
Context {interface_caddr backend_caddr : Address}.

(* the systems *)
Definition modular_sys := nest (interface backend_caddr) (backend interface_caddr).
Definition mono_sys := singleton_sys mono.

(* the auxiliary functions *)
Definition st_morph_modular_mono : storage * storage' -> storage'' :=
    (fun '(st, st') => build_storage'' st'.(counter)).

Definition st_morph_mono_modular : storage'' -> storage * storage' := 
    (fun st'' => (build_storage backend_caddr, build_storage' interface_caddr st''.(counter''))).

Definition permissioned_ctx (ctx : ContractCallContext) : ContractCallContext :=
    {|  ctx_origin := ctx.(ctx_origin) ;
        ctx_from := interface_caddr ;
        ctx_contract_address := ctx.(ctx_contract_address) ;
        ctx_contract_balance := ctx.(ctx_contract_balance) ;
        ctx_amount := ctx.(ctx_amount) ;
     |}.

(* mono -> modular *)
Definition stm_mono_modular : SystemTraceMorphism mono_sys modular_sys.
Proof.
    apply (build_st_morph mono_sys modular_sys st_morph_mono_modular).
    -   intros * is_gen.
        unfold is_genesis_sys_state in *.
        destruct is_gen as [sinit_c [sinit_ctx [sinit_s sinit_ok]]].
        exists sinit_c, sinit_ctx.
        exists (tt, tt).
        unfold modular_sys, nest, interface, backend, sys_init, st_morph_mono_modular.
        cbn.
        do 3 f_equal.
        unfold sys_init, mono_sys, singleton_sys, singleton_ntree, mono, init'' in sinit_ok.
        destruct sinit_s.
        simpl in *.
        now inversion sinit_ok.
    -   intros * sys_step.
        induction sys_step.
        +   apply clnil.
        +   destruct l as [seq_chain seq_ctx seq_msg seq_new_acts recv_step].
            destruct seq_msg.
            (* treat the None case, which leads to a contradiction *)
            2:{ unfold sys_receive, mono_sys in recv_step.
                now cbn in recv_step. }
            (* now we have some message, destruct along the message *)
            destruct e.
            (* incr'' n *)
            *   apply (snoc IHsys_step).
                clear IHsys_step.
                apply (build_sys_single_step modular_sys
                    (st_morph_mono_modular mid)
                    (st_morph_mono_modular to)
                seq_chain
                (permissioned_ctx seq_ctx)
                (Some (inr (incr' n)))
                seq_new_acts).
                unfold modular_sys, sys_receive, st_morph_mono_modular.
                simpl.
                unfold receive'.
                cbn.
                rewrite (address_eq_refl interface_caddr).
                do 4 f_equal;
                unfold sys_receive, mono_sys in *;
                cbn in *;
                now inversion recv_step.
            (* decr'' n *)
            *   apply (snoc IHsys_step).
                clear IHsys_step.
                apply (build_sys_single_step modular_sys 
                    (st_morph_mono_modular mid)
                    (st_morph_mono_modular to)
                seq_chain 
                (permissioned_ctx seq_ctx)
                (Some (inr (decr' n)))
                seq_new_acts).
                unfold modular_sys, sys_receive, st_morph_mono_modular.
                simpl.
                unfold receive'.
                simpl.
                rewrite (address_eq_refl interface_caddr).
                do 4 f_equal;
                unfold sys_receive, mono_sys in *;
                cbn in *;
                now inversion recv_step.
            (* reset'' *)
            *   apply (snoc IHsys_step).
                clear IHsys_step.
                apply (build_sys_single_step modular_sys 
                    (st_morph_mono_modular mid)
                    (st_morph_mono_modular to)
                seq_chain 
                (permissioned_ctx seq_ctx)
                (Some (inr reset'))
                seq_new_acts).
                unfold modular_sys, sys_receive, st_morph_mono_modular.
                simpl.
                unfold receive'.
                cbn.
                rewrite (address_eq_refl interface_caddr).
                do 4 f_equal;
                unfold sys_receive, mono_sys in *;
                cbn in *;
                now inversion recv_step.
Defined.


(* modular -> mono *)
Definition stm_modular_mono : SystemTraceMorphism modular_sys mono_sys.
Proof.
    apply (build_st_morph modular_sys mono_sys st_morph_modular_mono).
    -   intros * is_gen.
        unfold is_genesis_sys_state in *.
        destruct is_gen as [sinit_c [sinit_ctx [sinit_s sinit_ok]]].
        exists sinit_c, sinit_ctx, tt.
        unfold sys_init, mono_sys, st_morph_modular_mono.
        destruct init_sys_state, s0.
        cbn.
        unfold init''.
        do 2 f_equal.
        destruct sinit_s.
        unfold modular_sys, nest, interface, backend, sys_init, st_morph_mono_modular in *.
        cbn in *.
        now inversion sinit_ok.
    -   intros * sys_step.
        induction sys_step.
        +   apply clnil.
        +   destruct l as [seq_chain seq_ctx seq_msg seq_new_acts recv_step].
            destruct seq_msg.
            (* if seq_msg = None, the system does nothing *)
            2:{ clear sys_step.
                unfold sys_receive, modular_sys in *.
                unfold nest in *.
                destruct mid.
                cbn in *.
                (* by induction, since mid = to *)
                now inversion recv_step. }
            destruct s.
            (* all messages to the interface contract go to clnil by induction *)
            *   unfold sys_receive, modular_sys in recv_step.
                destruct e, mid;
                cbn in recv_step;
                (* by induction, since mid = to *)
                now inversion recv_step.
            (* messages to the backend contract *)
            *   destruct e;
                apply (snoc IHsys_step);
                clear IHsys_step.
                (* incr' *)
                **  apply (build_sys_single_step mono_sys 
                        (st_morph_modular_mono mid)
                        (st_morph_modular_mono to)
                        seq_chain
                        seq_ctx
                        (Some (incr'' n))
                        seq_new_acts).
                    unfold mono_sys, sys_receive, st_morph_modular_mono.
                    simpl.
                    destruct mid as [st1_mid st2_mid].
                    destruct to  as [st1_to  st2_to].
                    simpl.
                    assert (address_eqb seq_ctx.(ctx_from) (interface_address st2_mid) = true) 
                    as H_caddr'.
                    {   unfold sys_receive, modular_sys in *.
                        cbn in *.
                        unfold receive' in *.
                        destruct (ctx_from seq_ctx =? interface_address st2_mid)%address; auto.
                        inversion recv_step. }
                    do 3 f_equal;
                    unfold sys_receive, modular_sys in *;
                    cbn in *;
                    unfold receive' in *;
                    rewrite H_caddr' in recv_step;
                    now inversion recv_step.
                (* decr' *)
                **  apply (build_sys_single_step mono_sys 
                        (st_morph_modular_mono mid)
                        (st_morph_modular_mono to)
                        seq_chain 
                        seq_ctx 
                        (Some (decr'' n))
                        seq_new_acts).
                    unfold mono_sys, sys_receive, st_morph_modular_mono.
                    simpl.
                    destruct mid as [st1_mid st2_mid].
                    destruct to  as [st1_to  st2_to].
                    simpl.
                    assert (address_eqb seq_ctx.(ctx_from) (interface_address st2_mid) = true) 
                    as H_caddr'. 
                    {   unfold sys_receive, modular_sys in *.
                        cbn in *.
                        unfold receive' in *.
                        destruct (ctx_from seq_ctx =? interface_address st2_mid)%address; auto.
                        inversion recv_step. }
                    do 3 f_equal;
                    unfold sys_receive, modular_sys in *;
                    cbn in *;
                    unfold receive' in *;
                    rewrite H_caddr' in recv_step;
                    now inversion recv_step.
                (* reset' *)
                **  apply (build_sys_single_step mono_sys 
                        (st_morph_modular_mono mid)
                        (st_morph_modular_mono to)
                        seq_chain 
                        seq_ctx 
                        (Some reset'')
                        seq_new_acts).
                    unfold mono_sys, sys_receive, st_morph_modular_mono.
                    simpl.
                    destruct mid as [st1_mid st2_mid].
                    destruct to  as [st1_to  st2_to].
                    simpl.
                    assert (address_eqb seq_ctx.(ctx_from) (interface_address st2_mid) = true) 
                    as H_caddr'. 
                    {   unfold sys_receive, modular_sys in *.
                        cbn in *.
                        unfold receive' in *.
                        destruct (ctx_from seq_ctx =? interface_address st2_mid)%address; auto.
                        inversion recv_step. }
                    do 3 f_equal;
                    unfold sys_receive, modular_sys in *;
                    cbn in *;
                    unfold receive' in *;
                    rewrite H_caddr' in recv_step;
                    now inversion recv_step.
Defined.


(* the systems are bisimilar *)
Theorem mono_modular_bisimilar :
    systems_bisimilar modular_sys mono_sys.
Proof.
    unfold systems_bisimilar.
    exists stm_modular_mono, stm_mono_modular.
    intros step_id_modular step_id_mono.
    unfold is_iso_stm.
    split;
    unfold compose_stm, id_stm.
    (* modular -> mono -> modular *)
    -   admit.
    (* mono -> modular -> mono *)
    -   rewrite <- (eq_stm_dep mono_sys mono_sys
            (compose (st_state_morph modular_sys mono_sys stm_modular_mono)
                     (st_state_morph mono_sys modular_sys stm_mono_modular))
            (id_sys_genesis_fixpoint mono_sys)
            (sys_genesis_compose stm_modular_mono stm_mono_modular)
            (id_sys_step_morph mono_sys)
            (sys_step_compose stm_modular_mono stm_mono_modular));
        try f_equal.
        apply functional_extensionality_dep.
        intro st1.
        apply functional_extensionality_dep.
        intro st2.
        apply functional_extensionality.
        intro step.
        induction step.
        +   now unfold id_sys_step_morph, sys_step_compose, stm_modular_mono, stm_mono_modular.
        +   destruct l, sys_step_msg.
            (* msg = Some e *)
            *   destruct e.
                (* incr'' *)
                --  unfold id_sys_step_morph, sys_step_compose in *.
                    rewrite IHstep.
                    clear IHstep.
                    unfold stm_modular_mono, stm_mono_modular.
                    cbn.
                    do 2 f_equal;
                    cbn.
                    ++  admit.
                    ++  (* hmmm ... this tells us the connectivity! *)
                        admit.
                    ++  apply proof_irrelevance.
                (* decr'' *)
                --  unfold id_sys_step_morph, sys_step_compose in *.
                    rewrite IHstep.
                    clear IHstep.
                    unfold sys_step_compose, stm_modular_mono, stm_mono_modular.
                    cbn.
                    do 2 f_equal.
                    cbn.
                    ++  
                        admit.
                    ++  (* hmmm ... this tells us the connectivity! *)
                        admit.
                    ++  apply proof_irrelevance.
                (* reset'' *)
                --  unfold id_sys_step_morph, sys_step_compose in *.
                    rewrite IHstep.
                    clear IHstep.
                    unfold sys_step_compose, stm_modular_mono, stm_mono_modular.
                    cbn.
                    do 2 f_equal.
                    cbn.
                    ++  
                        admit.
                    ++  (* hmmm ... this tells us the connectivity! *)
                        admit.
                    ++  apply proof_irrelevance.
            (* msg = None *)
            *   unfold id_sys_step_morph in *.
                rewrite IHstep.
                now unfold sys_step_compose, stm_modular_mono, stm_mono_modular.
Admitted.



End SystemBisimulation.

End System.