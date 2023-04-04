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

(* the upgradeable example *)

Section UpgradeableContract.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* contract types definition *)
Inductive entrypoint := 
    | next (u : unit)
    | upgrade_fun (s' : N -> N).
Record storage := build_storage {
    n : N ; 
    s : N -> N ; }.
Definition setup := storage.
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

(* derive serializable typeclass *)
Section Serialization.
    Global Instance storage_serializable : Serializable storage := todo "".
    Global Instance entrypoint_serializable : Serializable entrypoint := todo "".
End Serialization.

(* init function definition *)
Definition init (_ : Chain)
                (_ : ContractCallContext)
                (init_state : setup)
                : ResultMonad.result storage N := 
    Ok (init_state).

(* receive function definition *)
Definition receive (_ : Chain)
                (_ : ContractCallContext)
                (storage : storage)
                (msg : option entrypoint)
                : result :=
    match msg with 
    | Some (next _) => 
        let st := {| n := storage.(s) storage.(n) ; s := storage.(s) ; |} in 
        Ok (st, [])
    | Some (upgrade_fun s') => 
        let st := {| n := storage.(n) ; s := s' ; |} in 
        Ok (st, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup entrypoint storage error := 
    build_contract init receive.

End UpgradeableContract.


Section SkeletonContract.
Context { Base : ChainBase }.

(* contract types definition *)
Definition setup_s := unit.
Inductive entrypoint_s := 
    | next_s (u : unit)
    | upgrade_fun_s (s' : N -> N).
Record storage_s := build_storage_s { n_s : N ; s_s : N -> N ; }.
Definition error_s := N.
Definition result_s : Type := ResultMonad.result (storage_s * list ActionBody) error_s.

(* derive serializable typeclass *)
Section Serialization.
    Global Instance storage_s_serializable : Serializable storage_s := todo "".
    Global Instance entrypoint_s_serializable : Serializable entrypoint_s := todo "".
End Serialization.

(* init function definition *)
Definition init_s (_ : Chain)
                (_ : ContractCallContext)
                (_ : setup_s)
                : ResultMonad.result storage_s N := 
    let storage_s := {|
        n_s := 0 ; 
        s_s := (fun (n : N) => 0) ; |} in 
    Ok (storage_s).

(* receive function definition *)
Definition receive_s (_ : Chain)
                (_ : ContractCallContext)
                (storage_s : storage_s)
                (msg : option entrypoint_s)
                : result_s :=
    match msg with 
    | Some (next_s _) => 
        let st := {| n_s := storage_s.(s_s) storage_s.(n_s) ; s_s := storage_s.(s_s) ; |} in 
        Ok (st, [])
    | Some (upgrade_fun_s _) => Ok (storage_s, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C_s : Contract setup_s entrypoint_s storage_s error_s := 
    build_contract init_s receive_s.

End SkeletonContract.

Section Projection.
Context { Base : ChainBase }.

(* using the simple morphism construction *)
Definition msg_morph (e : entrypoint) : entrypoint_s := 
    match e with 
    | next _ => next_s tt 
    | upgrade_fun s' => upgrade_fun_s s'
    end.
Definition setup_morph : setup -> setup_s := (fun (_ : setup) => tt).
Definition state_morph (st : storage) : storage_s := 
    {| n_s := 0 ; s_s := (fun (n : N) => 0) ; |}.
    (* {| n_s := st.(n) ; s_s := st.(s) |}. *)
Definition error_morph : error -> error_s := id.

(* the coherence results *)
Lemma init_coherence : forall c ctx s, 
    (init_result_transform state_morph error_morph) ((Blockchain.init C) c ctx s) = 
    (Blockchain.init C_s) c ctx (setup_morph s).
Proof. auto. Qed.

Lemma recv_coherence : forall c ctx st op_msg, 
    (recv_result_transform state_morph error_morph) ((Blockchain.receive C) c ctx st op_msg) = 
    (Blockchain.receive C_s) c ctx (state_morph st) (option_map msg_morph op_msg).
Proof.
    intros. cbn.
    destruct op_msg; auto. 
    destruct e; auto.
Qed. 

(* construct the morphism *)
Definition f_s : ContractMorphism C C_s := 
    simple_cm msg_morph setup_morph state_morph error_morph init_coherence recv_coherence.

(* TODO this is a problem -- you want all *reachable* states of the contract ... *)
Theorem f_s_is_surj : is_surj_cm f_s.
Proof.
    unfold is_surj_cm. repeat split; unfold is_surj; intro x.
    -   destruct x as [x s_s]. destruct x as [c ctx].
        pose (s := {| n := 0 ; s := (fun _ : N => 0) |}).
        exists (c, ctx, s).
        cbn. unfold setup_morph. destruct s_s. 
        reflexivity.
    -   destruct x.
        +   admit.
        +   exists (Err 0). cbn. unfold error_morph. admit.
    -   admit.
    -   admit.
Admitted.

End Projection.

Section MutableFunctionality.
Context { Base : ChainBase }.

(* contract types definition *)
Definition setup_i := N.
Inductive entrypoint_i := | next_i (u : unit).
Record storage_i := build_storage_i { n_i : N ; }.
Definition error_i := N.
Definition result_i : Type := ResultMonad.result (storage_i * list ActionBody) error_i.

(* derive serializable typeclass *)
Section Serialization.
    Global Instance storage_i_serializable : Serializable storage_i := todo "".
    Global Instance entrypoint_i_serializable : Serializable entrypoint_i := todo "".
End Serialization.

(* init function definition *)
Definition init_i (_ : Chain)
                (_ : ContractCallContext)
                (n : setup_i)
                : ResultMonad.result storage_i N := 
    let storage_i := {| n_i := n ; |} in 
    Ok (storage_i).

(* receive function definition *)
Axiom s_next : N -> N.

Definition receive_i (_ : Chain)
                (_ : ContractCallContext)
                (storage_i : storage_i)
                (msg : option entrypoint_i)
                : result_i :=
    match msg with 
    | Some (next_i _) => 
        let st := {| n_i := s_next storage_i.(n_i) ; |} in 
        Ok (st, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C_i : Contract setup_i entrypoint_i storage_i error_i := 
    build_contract init_i receive_i.

End MutableFunctionality.

Section Embedding.
Context { Base : ChainBase }.

(* using the simple morphism construction *)
Definition msg_morph' (e : entrypoint_i) : entrypoint := 
    match e with 
    | next_i _ => next tt
    end.
Definition setup_morph' (st_i : setup_i) : setup := {| 
    n := st_i ; 
    s := s_next ; |}.
Definition state_morph' (st_i : storage_i) : storage := 
    {| n := st_i.(n_i) ; s := s_next ; |}.
Definition error_morph' : error_i -> error := id.

(* the coherence results *)
Lemma init_coherence' : forall c ctx s, 
    (init_result_transform state_morph' error_morph') ((Blockchain.init C_i) c ctx s) = 
    (Blockchain.init C) c ctx (setup_morph' s).
Proof. auto. Qed. 

Lemma recv_coherence' : forall c ctx st op_msg, 
    (recv_result_transform state_morph' error_morph') ((Blockchain.receive C_i) c ctx st op_msg) = 
    (Blockchain.receive C) c ctx (state_morph' st) (option_map msg_morph' op_msg).
Proof.
    intros. cbn.
    destruct op_msg; auto.
    destruct e; auto.
Qed. 

(* construct the morphism *)
Definition f_i : ContractMorphism C_i C := 
    simple_cm msg_morph' setup_morph' state_morph' error_morph' init_coherence' recv_coherence'.

Theorem f_s_is_inj : is_inj_cm f_s.
Proof.
    unfold is_inj_cm, is_inj. repeat split; intros.
Admitted.

End Embedding.

Section UpgradeabilityThm.

Theorem upgrade_mechanism : 
    forall bstate caddr cstate msg s' cstate' acts chain ctx,
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (C : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* a call to upgrade_fun was successful *)
    msg = upgrade_fun s' ->  
    receive C chain ctx cstate (Some msg) = Ok(cstate', acts) -> 
    (* exists a contract C_i and an embedding *)
    exists C_i (f_i : ContractMorphism C_i C), 
    is_inj_cm f_i /\ 
    (* with storage as desired *)
    cstate' = 
    (state_morph f_i) {| n := cstate'.(n) ; |}.    
Proof.
Admitted.


Theorem upgradeability_invariance : 
    forall bstate caddr cstate msg s' cstate' acts,
    (* state is reachable *)
    reachable bstate -> 
    (* the contract address is caddr with state cstate *)
    env_contracts bstate caddr = Some (C : WeakContract) -> 
    contract_state bstate caddr = Some cstate -> 
    (* exists a surjection onto C_s *)
    exists (f_s : ContractMorphism C C_s).
Proof. intros. exact f_s. Qed.

End UpgradeabilityThm.