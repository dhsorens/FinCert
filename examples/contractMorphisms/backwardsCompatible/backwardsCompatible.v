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


Section BackwardsCompatible.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(** The initial contract C *)
(* contract types definition *)
Inductive entrypoint := | incr (u : unit).
Definition storage := N.
Definition setup := N.
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := 
    Derive Serializable entrypoint_rect<incr>.
End Serialization.

(* init function definition *)
Definition init (_ : Chain) (_ : ContractCallContext) (n : setup) :
    ResultMonad.result storage N := 
    Ok (n).

(* receive function definition *)
Definition receive (_ : Chain) (_ : ContractCallContext) (n : storage) 
    (msg : option entrypoint) : result :=
    match msg with 
    | Some (incr _) => Ok (n + 1, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup entrypoint storage error := 
    build_contract init receive.


(** The updated contract C' *)
(* contract types definition *)
Inductive entrypoint' := | incr' (u : unit) | decr (u : unit).

Section Serialization.
    Global Instance entrypoint'_serializable : Serializable entrypoint' := 
    Derive Serializable entrypoint'_rect<incr',decr>.
End Serialization.

(* receive function definition *)
Definition receive' (_ : Chain) (_ : ContractCallContext) (n : storage) 
    (msg : option entrypoint') : result :=
    match msg with 
    | Some (incr' _) => Ok (n + 1, [])
    | Some (decr _) => Ok (n - 1, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C' : Contract setup entrypoint' storage error := 
    build_contract init receive'.


(** The contract morphism confirming backwards compatibility *)
Definition msg_morph (e : entrypoint) : entrypoint' := 
    match e with | incr _ => incr' tt end.
Definition setup_morph : setup -> setup := id.
Definition state_morph : storage -> storage := id.
Definition error_morph : error -> error := id.

(* the coherence results *)
Lemma init_coherence : forall c ctx s, 
    (init_result_transform state_morph error_morph) ((Blockchain.init C) c ctx s) = 
    (Blockchain.init C') c ctx (setup_morph s).
Proof. auto. Qed.

Lemma recv_coherence : forall c ctx st op_msg, 
    (recv_result_transform state_morph error_morph) ((Blockchain.receive C) c ctx st op_msg) = 
    (Blockchain.receive C') c ctx (state_morph st) (option_map msg_morph op_msg).
Proof.
    intros. cbn. unfold recv_result_transform.
    unfold msg_morph. unfold state_morph. unfold error_morph.
    cbn. induction op_msg; cbn; auto.
    destruct a. auto.
Qed.


(* construct the morphism *)
Definition f : ContractMorphism C C' := 
    simple_cm msg_morph setup_morph state_morph error_morph init_coherence recv_coherence.


(* this theorem shows a strong notion of backwards compatibility because there is an embedding of the old contract into the new *)
Theorem embedding : is_inj_cm f. 
Proof.
    unfold is_inj_cm; unfold is_inj. 
    repeat split; intros.
    -   destruct a as [(c,ctx) s]. destruct a' as [(c',ctx') s'].
        cbn in H. unfold setup_morph in H. cbn in H.
        exact H.
    -   destruct a, a'; cbn in H.
        +   unfold state_morph in H. auto.   
        +   unfold state_morph, error_morph in H. cbn in H. inversion H.
        +   unfold error_morph, state_morph in H. cbn in H. inversion H.
        +   unfold error_morph in H. cbn in H. auto.
    -   destruct a as [((c,ctx),st) o].
        destruct a' as [((c',ctx'),st') o'].
        cbn in H. unfold state_morph, msg_morph in H. simpl in H.
        destruct o, o'; cbn in H.
        +   destruct e, e0. cbn in H.
            destruct u, u0. 
            inversion H.
            f_equal.
        +   inversion H.   
        +   inversion H.
        +   inversion H. 
            f_equal.
    -   destruct a, a'.
        +   destruct t, t0.
            cbn in H. unfold state_morph in H. simpl in H. 
            exact H.
        +   destruct t.
            cbn in H. unfold state_morph, error_morph in H. simpl in H.
            inversion H.
        +   destruct t.
            cbn in H. unfold error_morph, state_morph in H.
            inversion H.   
        +   cbn in H. unfold error_morph in H. simpl in H.
            exact H.
Qed.

End BackwardsCompatible.

