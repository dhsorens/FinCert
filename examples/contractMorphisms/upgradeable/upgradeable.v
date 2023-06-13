From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractMorphisms.
From ConCert.Execution Require Import ContractSystems.
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
Section Upgradeable.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(** Goal: 
    - A family of versioned contracts C_f : for all version v, C_f v
    - Forall v, C_f v -> C -> C_b which decomposes the upgradeability structure of C
*)

Section ContractDefinitions.
(*** Contract types definition *)
(** Main contract C *)
Inductive entrypoint := 
| next (u : unit)
| upgrade_fun (s' : N -> N).
Record storage := { n : N ; s : N -> N ; }.
Definition setup := storage.
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

(** Skeleton contract C_skel (to be C_b) *)
Inductive entrypoint_skel := 
| upgrade_fun_b (s' : N -> N).
Record storage_b := { s_b : N -> N ; }.
Definition setup_b := storage_b.
Definition error_b := N.
Definition result_b : Type := ResultMonad.result (storage_b * list ActionBody) error_b.

(** Version contracts C_f v, for v : storage_b *)
Inductive entrypoint_version := | next_f (u : unit).
Record storage_version := { n_f : N }.
Definition entrypoint_f : storage_b -> Type := fun v => entrypoint_version.
Definition storage_f    : storage_b -> Type := fun v => storage_version.
Definition setup_f      : storage_b -> Type := fun v => N.
Definition error_f      : storage_b -> Type := fun v => N.
Definition result_f     : storage_b -> Type := 
    fun v => ResultMonad.result ((storage_f v) * list ActionBody) (error_f v).

Section Serialization.
    Global Instance storage_serializable : Serializable storage := todo "".
    Global Instance entrypoint_serializable : Serializable entrypoint := todo "".
    Global Instance storage_s_serializable : Serializable storage_b := todo "".
    Global Instance entrypoint_s_serializable : Serializable entrypoint_skel := todo "".
    Global Instance storage_f_serializable : forall v, Serializable (storage_f v) := todo "".
    Global Instance entrypoint_f_serializable : forall v, Serializable (entrypoint_f v) := todo "".
End Serialization.

(** Contract, init, and receive definitions *)

(** Main contract C *)
(* init *)
Definition init (_ : Chain)
                (_ : ContractCallContext)
                (init_state : setup)
                : ResultMonad.result storage N := 
    Ok (init_state).

(* receive *)
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

(* the contract C *)
Definition C : Contract setup entrypoint storage error := 
    build_contract init receive.

(** Skeleton Contract (to be the base contract) *)
(* init *)
Definition init_skel (_ : Chain)
                (_ : ContractCallContext)
                (init_state_b : setup_b)
                : ResultMonad.result storage_b N := 
    Ok (init_state_b).

(* receive *)
Definition receive_skel (_ : Chain)
                (_ : ContractCallContext)
                (_ : storage_b)
                (msg : option entrypoint_skel)
                : result_b :=
    match msg with 
    | Some (upgrade_fun_b s_new) => 
        let st := {| s_b := s_new ; |} in 
        Ok (st, [])
    | None => Err 0
    end.

(* the contract C_skel *)
Definition C_skel : Contract setup_b entrypoint_skel storage_b error_b :=
    build_contract init_skel receive_skel.

(** For the morphisms, we define the base contract *)
Definition C_b := pointed_contract C_skel.
Definition entrypoint_b := (entrypoint_skel + unit)%type.


(** The family of version contracts C_f *)
(* init *)
Definition init_f (version : storage_b)
                (_ : Chain)
                (_ : ContractCallContext)
                (n : setup_f version)
                : ResultMonad.result (storage_f version) (error_f version) := 
    let storage_f := {| n_f := n ; |} in 
    Ok (storage_f).

(* receive *)
Definition receive_f (version : storage_b)
                (_ : Chain)
                (_ : ContractCallContext)
                (storage_f : storage_f version)
                (msg : option (entrypoint_f version))
                : result_f version :=
    match msg with 
    | Some (next_f _) => 
        let st := {| n_f := version.(s_b) storage_f.(n_f) ; |} in 
        Ok (st, [])
    | None => Err 0
    end.

(* the contract C_f *)
Definition C_f (version : storage_b) : Contract (setup_f version) (entrypoint_f version) (storage_f version) (error_f version) := 
    build_contract (init_f version) (receive_f version).

End ContractDefinitions.


(** Define the contract morphisms  *)
Section Morphisms.

(** f_p : C ->> C_b *)
Section Quotient.
Definition zero_fn : N -> N := (fun (x : N) => 0).
Definition null_storage_b : storage_b := {| s_b := zero_fn |}.
Definition null_setup_b : setup_b := {| s_b := zero_fn |}.

(* component morphisms *)
Definition msg_morph_p (e : entrypoint) : entrypoint_b := 
    match e with 
    | next _ => inr tt (* not upgrade functionality *)
    | upgrade_fun s' => inl (upgrade_fun_b s') (*  *)
    end.
Definition state_morph_p : storage -> storage_b := (fun (x : storage) => {| s_b := x.(s) ; |}).
Definition setup_morph_p : setup -> setup_b := (fun (x : setup) => {| s_b := x.(s) |}).
Definition error_morph_p : error -> error_b := (fun (x : error) => x).

(* the coherence results *)
Lemma init_coherence_p : 
    init_coherence_prop C C_b 
        setup_morph_p state_morph_p error_morph_p.
Proof. unfold init_coherence_prop. auto. Qed.

Lemma recv_coherence_p : 
    recv_coherence_prop C C_b 
        msg_morph_p state_morph_p error_morph_p.
Proof.
    unfold recv_coherence_prop.
    intros.
    unfold result_functor.
    cbn.
    destruct op_msg; cbn.
    -   unfold msg_morph_p.
        destruct e eqn:H_e.
        +   now destruct st.
        +   now unfold state_morph_p.
    -   now unfold error_morph_p.
Qed.

(* construct the morphism *)
Definition f_p : ContractMorphism C C_b := 
    build_contract_morphism C C_b
        (* the morphisms *)
        setup_morph_p msg_morph_p state_morph_p error_morph_p 
        (* coherence *)
        init_coherence_p recv_coherence_p.

End Quotient.


(** f_i : forall v, C_f v -> C *)
Section Embedding.

Definition msg_morph_i (v : storage_b) (e : entrypoint_f v) : entrypoint := 
    match e with 
    | next_f _ => next tt
    end.
Definition setup_morph_i (v : storage_b) (st_f : setup_f v) : setup := {| 
    n := st_f ; 
    s := s_b v ; |}.
Definition state_morph_i (v : storage_b) (st_f : storage_f v) : storage := 
    {| n := st_f.(n_f) ; s := s_b v ; |}.
Definition error_morph_i (v : storage_b) : error_f v -> error := id.

(* the coherence results *)
Lemma init_coherence_i (v : storage_b) : 
    init_coherence_prop (C_f v) C (setup_morph_i v) (state_morph_i v) (error_morph_i v).
Proof. unfold init_coherence_prop. auto. Qed. 

Lemma recv_coherence_i (v : storage_b) : 
    recv_coherence_prop (C_f v) C (msg_morph_i v) (state_morph_i v) (error_morph_i v).
Proof.
    unfold recv_coherence_prop.
    intros.
    destruct op_msg; auto.
    now destruct e.
Qed.

(* construct the morphism *)
Definition fi_param (v : storage_b) : ContractMorphism (C_f v) C := 
    build_contract_morphism (C_f v) C 
        (* the morphisms *)
        (setup_morph_i v) (msg_morph_i v) (state_morph_i v) (error_morph_i v) 
        (* coherence results *)
        (init_coherence_i v) (recv_coherence_i v).

End Embedding.


(** Here we prove the core result that the family of versioned contracts and the 
    base contract given above provide an upgradeability decomposition of our contract C. *)
Section UpgradeabilityDecomposition.
Definition extract_version (m : entrypoint_skel) : storage_b := 
    match m with | upgrade_fun_b s_b => {| s_b := s_b |} end.
Definition new_version_state old_v msg (st : storage_f old_v) : storage_f (extract_version msg) := st.

Theorem upgradeability_decomposition :
    upgradeability_decomposition fi_param f_p extract_version new_version_state.
Proof.
    unfold upgradeability_decomposition.
    repeat split.
    (* msg_required *)
    -   unfold ContractMorphisms.msg_required. 
        intros. 
        now exists 0.
    (* init_versioned *)
    -   unfold init_versioned.
        intros ? ? ? s init_ok.
        destruct init_state as [n_i s_i].
        unfold is_versioned.
        now exists {| s_b := s_i |}, {| n_f := n_i |}.
    (* msg_decomposable *)
    (* -> *)
    -   simpl.
        intro H_null.
        unfold msg_morph_p in H_null.
        destruct m; try inversion H_null.
        destruct u.
        now exists (next_f tt).
    (* <- *)
    -   simpl.
        intro H_preim.
        unfold msg_morph_i in H_preim.
        destruct H_preim as [m' H_preim].
        destruct m'.
        unfold msg_morph_p.
        now destruct m; try inversion H_preim.
    (* states categorized *)
    (* -> *)
    -   simpl.
        intro H_preim.
        destruct H_preim as [st_f H_preim].
        destruct st_f as [nf].
        unfold state_morph_i in H_preim.
        simpl in H_preim.
        destruct st as [n s].
        now inversion H_preim.
    (* <- *)
    -   simpl.
        unfold state_morph_p, state_morph_i.
        destruct c_version as [sb], st as [n s].
        cbn.
        intro H.
        inversion H.
        now exists {| n_f := n |}.
    (* version transition *)
    -   unfold version_transition.
        simpl.
        unfold msg_morph_p, state_morph_i.
        intros * H_cstate_preim ? ? ? ? ? ? recv_some is_upgrade_msg.
        destruct msg; try inversion is_upgrade_msg.
        inversion recv_some.
        f_equal.
        unfold new_version_state.
        now rewrite H_cstate_preim.
Qed.

End UpgradeabilityDecomposition.

End Morphisms.

Section Decomposition.

(** Theorem: all reachable contract states are versioned according to this indexing *)
Theorem all_states_versioned : 
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    (* where C is at caddr with state cstate, *)
    env_contracts bstate caddr = Some (C : WeakContract) -> 
    exists (cstate : storage),
    contract_state bstate caddr = Some cstate /\
    (* then every contract state cstate is versioned *)
    is_versioned fi_param cstate.
Proof.
    intros * ? c_at_caddr.
    pose proof (versioned_invariant fi_param f_p extract_version new_version_state bstate caddr trace c_at_caddr).
    destruct H as [cstate [cstate_st versioned]].
    exists cstate.
    split; auto.
    apply (versioned upgradeability_decomposition).
Qed.

(** Theorem: Versioning moves along as we've described it. *)
Theorem upgrade_decomposed : 
    (* Forall versioned contract states (incl. all reachable states), *)
    forall cstate c_version cstate_f,
    cstate = state_morph (C_f c_version) C (fi_param c_version) cstate_f ->
    (* And forall calls to the versioned contract *)
    forall chain ctx m new_state new_acts,
    receive chain ctx cstate (Some m) = Ok (new_state, new_acts) -> 
    (* the contract state either stays within this version *)
    (exists cstate_f', new_state = state_morph (C_f c_version) C (fi_param c_version) cstate_f') \/
    (* or it moves onto a new version as we've described it. *)
    (exists c_version' cstate_f',
    new_state = state_morph (C_f c_version') C (fi_param c_version') cstate_f').
Proof.
    intros * cstate_preim * recv_some.
    apply (upgradeability_decomposed fi_param f_p extract_version new_version_state cstate c_version cstate_f upgradeability_decomposition cstate_preim chain ctx m new_state new_acts recv_some).
Qed.

End Decomposition.

End Upgradeable.