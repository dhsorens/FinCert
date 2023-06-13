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
From Coq Require Import Lia.
From Coq Require Import FunctionalExtensionality.
From Coq.Init Require Import Byte.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** Hello, World! 
    This example introduces contract morphisms on three simple counter contracts.
    Each contract keeps some (n : N) in storage and has an entrypoint `incr` which 
    can be called to increment the natural number in storage.

    The contracts are:
    1. C1  := initializes with a natural number `n` given at initialization,
              increments by `m` when given a message `incr m`
    2. C2  := initializes with a natural number `2 * n`, for `n` given at initialization
              increments by `2 * m` for a message `incr m`
    3. C3 := initializes with a natural number n, for `n` given at initialization
              increments by `2 * m` for a message `incr m`

    Notably:
    - C2 has the same functionality as C1, except that it doubles everything.
    - C3 initializes like C1, but receives messages like C2
*)

Section HelloWorld.
Context {Base : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Axiom todo : string -> forall {A}, A.

(** Now we give our contract definitions, starting with contract types: *)
Definition storage := N.
Definition setup := N.
Inductive entrypoint := | incr (n : N).
Definition error := N.
Definition result := ResultMonad.result (storage * list ActionBody) error.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := todo "".
End Serialization.

(** Define Contract C1:
    - Initializes with the number `init_n` given to `init`
    - Increments the storage by `m` for a message `incr m`
    - Fails if given no message
*)
Definition init_1 (_ : Chain)
                (_ : ContractCallContext)
                (init_n : setup)
                : ResultMonad.result storage error := 
    Ok init_n.

Definition receive_1 (_ : Chain)
                (_ : ContractCallContext)
                (n : storage)
                (op_msg : option entrypoint)
                : result :=
    match op_msg with 
    | Some msg => 
        match msg with | incr m => Ok (n + m, []) end 
    | None =>
        Ok (n, [])
    end.

Definition C1 := build_contract init_1 receive_1.


(** Define C2:
    - Initializes with the number `2 * init_n`, for `init_n` given to `init`
    - Increments the storage by `2 * m` for a message `incr m`
    - Fails if given no message
*)
Definition init_2 (_ : Chain)
                (_ : ContractCallContext)
                (init_n : setup)
                : ResultMonad.result storage error := 
    Ok (2 * init_n).

Definition receive_2 (_ : Chain)
                (_ : ContractCallContext)
                (n : storage)
                (op_msg : option entrypoint)
                : result :=
    match op_msg with 
    | Some msg => 
        match msg with | incr m => Ok (n + 2 * m, []) end 
    | None =>
        Ok (n, [])
    end.

Definition C2 := build_contract init_2 receive_2.


(** Define C3:
    - Initializes with the number `init_n` given to `init` (like C1)
    - Increments the storage by `2 * m` for a message `incr m` (like C2)
    - Fails if given no message
*)
Definition init_3 (_ : Chain)
                (_ : ContractCallContext)
                (init_n : setup)
                : ResultMonad.result storage error := 
    Ok (init_n).

Definition receive_3 (_ : Chain)
                (_ : ContractCallContext)
                (n : storage)
                (op_msg : option entrypoint)
                : result :=
    match op_msg with 
    | Some msg => 
        match msg with | incr m => Ok (n + 2 * m, []) end 
    | None =>
        Ok (n, [])
    end.

Definition C3 := build_contract init_3 receive_3.


End HelloWorld.


(** Now let's see how C1, C2, and C3 relate to each other with contract morphisms *)
Section HelloWorldMorphisms.
Context {Base : ChainBase}.

Definition n_double := (fun (n : N) => 2 * n).

(** f1 : C1 -> C2 (an embedding) *)
Definition msg_morph_1 := @id entrypoint.
Definition setup_morph_1 := @id setup.
Definition state_morph_1 := n_double.
Definition error_morph_1 := @id error.

Lemma init_coherence_1 : forall c ctx s, 
(init_result_transform state_morph_1 error_morph_1) (init C1 c ctx s) = 
init C2 c ctx (setup_morph_1 s).
Proof. 
    intros.
    unfold init_result_transform, state_morph_1, error_morph_1, setup_morph_1, n_double.
    cbn.
    destruct s.
    -   now unfold init_2.
    -   unfold init_2. 
        now cbn.
Qed.
Lemma recv_coherence_1 : forall c ctx st op_msg, 
(recv_result_transform state_morph_1 error_morph_1) (receive C1 c ctx st op_msg) = 
receive C2 c ctx (state_morph_1 st) (option_map msg_morph_1 op_msg).
Proof.
    intros.
    unfold recv_result_transform, state_morph_1, error_morph_1, msg_morph_1, n_double.
    destruct op_msg; cbn; auto.
    destruct e.
    destruct st; auto.
    destruct n; auto.
Qed.

(** The embedding *)
Definition f1 : ContractMorphism C1 C2 := 
    simple_cm msg_morph_1 setup_morph_1 state_morph_1 error_morph_1 
        init_coherence_1 recv_coherence_1.



(** f2 : C2 ->> C1 (a surjection) *)
Definition n_div_2 := (fun (n : N) => n / 2).
Lemma double_half1 : forall n, n_div_2 (n_double n) = n. Admitted.
Lemma double_half2 : forall n, N.pos (2 * n) / 2 = N.pos n. Admitted.

Definition msg_morph_2 := @id entrypoint.
Definition setup_morph_2 := @id setup.
Definition state_morph_2 := n_div_2.
Definition error_morph_2 := @id error.

Lemma init_coherence_2 : forall c ctx s, 
(init_result_transform state_morph_2 error_morph_2) (init C2 c ctx s) = 
init C1 c ctx (setup_morph_2 s).
Proof.
    intros.
    unfold init_result_transform, state_morph_2, error_morph_2, setup_morph_2, n_div_2.
    cbn.
    destruct s.
    -   now unfold init_1.
    -   unfold init_1.
        rewrite (double_half2 p).
        now cbn.
Qed.
Lemma recv_coherence_2 : forall c ctx st op_msg, 
(recv_result_transform state_morph_2 error_morph_2) (receive C2 c ctx st op_msg) = 
receive C1 c ctx (state_morph_2 st) (option_map msg_morph_2 op_msg).
Proof.
    intros.
    unfold recv_result_transform, state_morph_2, error_morph_2, msg_morph_2, n_div_2.
    destruct op_msg; auto.
    destruct e.
Admitted.

(** The surjection *)
Definition f2 : ContractMorphism C2 C1 := 
    simple_cm msg_morph_2 setup_morph_2 state_morph_2 error_morph_2 
        init_coherence_2 recv_coherence_2.


(** these are actually *isomorphisms* *)
Theorem C1_C2_iso : is_iso_cm f1 f2.
Proof.
    apply iso_cm_components.
    repeat split; unfold init_inputs, init_cm; cbn; apply functional_extensionality; 
    intro.
    -   unfold setup_morph_1, setup_morph_2.
        destruct x.
        now destruct p as [c ctx].
    -   unfold setup_morph_1, setup_morph_2.
        destruct x.
        now destruct p as [c ctx].
    -   unfold init_result_transform, state_morph_1, error_morph_1, state_morph_2, error_morph_2.
        destruct x; simpl; auto.
        now rewrite double_half1.
    -   unfold init_result_transform, state_morph_1, error_morph_1, state_morph_2, error_morph_2.
        destruct x; simpl; auto.
        (* ISSUE : this is a weaker form of "isomorphic" -- only on reachable states
            (i.e. via the induction/whatever property) *)
Admitted.





(** f1' : C1 -> C3 (an embedding) *)
Definition storage_morph_1' := @id storage.
Definition setup_morph_1' := @id setup.
Definition entrypoint_morph_1' := @id entrypoint.
Definition error_morph_1' := @id error.

(** f2' : C3 -> C1 (a surjection?) *)
Definition storage_morph_2' := @id storage.
Definition setup_morph_2' := @id setup.
Definition entrypoint_morph_2' := @id entrypoint.
Definition error_morph_2' := @id error.

(** note that this is NOT an isomorphism *)

End HelloWorldMorphisms.



(* Old notes *)
(** There have been some examples of contracts which aren't iso (counter, counter *2 for eg)
    but would be for all reachable states.
    In that eg, counter *2 always has an even number in storage, so there is an isomorphism
    ** OF REACHABLE STATES **.
    That's different from a contract isomorphism. *)
