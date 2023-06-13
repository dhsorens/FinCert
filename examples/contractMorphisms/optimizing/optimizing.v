From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractMorphisms.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
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

(** An example that shows how one might use a contract isomorphism to prove that an
    optimized contract is behaviorally equivalent to its predecessor.

    In this example, C has some extra, unnecessary data in storage. Since a large storage 
    leads to gas inefficiency, one very simple optimization tactic might be to eliminate 
    the extra data in storage. We do so, and prove an isomorphism.

    This example also shows that isomorphisms are very strong, and in practice what is 
    probably preferred would be a contract equivalence, or a bisimulation, which is 
    weaker than an isomorphism but harder to prove.
*)

Section ContractOptimization.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Axiom todo : string -> forall {A}, A.

Section Contract.
Inductive entrypoint := | incr (u : unit).
Record storage := build_storage { n_1 : N ; extra_data : unit }.
Definition setup := N.
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := 
    Derive Serializable entrypoint_rect<incr>.
    Global Instance storage_serializable : Serializable storage := todo "".
End Serialization.

(* init function definition *)
Definition init (_ : Chain) (_ : ContractCallContext) (n : setup) :
    ResultMonad.result storage error := 
    Ok ({| n_1 := n ; extra_data := tt |}).

(* receive function definition *)
Definition receive (_ : Chain) (_ : ContractCallContext) (st : storage) 
    (msg : option entrypoint) : result :=
    match msg with 
    | Some (incr _) => Ok ({| n_1 := st.(n_1) + 1 ; extra_data := tt ; |}, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup entrypoint storage error := 
    build_contract init receive.

End Contract.

Section Contract'.
Inductive entrypoint' := | incr' (u : unit).
Record storage' := build_storage' { n : N ; }.
Definition setup' := N.
Definition error' := N.
Definition result' : Type := ResultMonad.result (storage' * list ActionBody) error'.

Section Serialization.
    Global Instance entrypoint'_serializable : Serializable entrypoint' := 
    Derive Serializable entrypoint'_rect<incr'>.

    Global Instance storage'_serializable : Serializable storage' := todo "".
End Serialization.

(* init function definition *)
Definition init' (_ : Chain) (_ : ContractCallContext) (n : setup') :
    ResultMonad.result storage' error' := 
    Ok ({| n := n ; |}).

(* receive function definition *)
Definition receive' (_ : Chain) (_ : ContractCallContext) (st : storage') 
    (msg : option entrypoint') : result' :=
    match msg with 
    | Some (incr' _) => Ok ({| n := st.(n) + 1 ; |}, [])
    | None => Err 0
    end.

(* construct the contract *)
Definition C' : Contract setup' entrypoint' storage' error' := 
    build_contract init' receive'.

End Contract'.


Section Isomorphism.

(* a morphism C -> C' *)
Definition msg_morph (e : entrypoint) : entrypoint' := 
    match e with | incr _ => incr' tt end.
Definition setup_morph : setup -> setup' := id.
Definition state_morph (st : storage) : storage' := {| n := st.(n_1) |}.
Definition error_morph : error -> error' := id.

Lemma init_coherence : init_coherence_prop C C' setup_morph state_morph error_morph.
Proof. now unfold init_coherence_prop. Qed.

Lemma recv_coherence : recv_coherence_prop C C' msg_morph state_morph error_morph.
Proof.
    unfold recv_coherence_prop.
    intros.
    simpl.
    unfold result_functor, receive, receive'.
    destruct op_msg; auto.
    now destruct e.
Qed.

Definition f : ContractMorphism C C' := 
    build_contract_morphism C C' setup_morph msg_morph state_morph error_morph 
        init_coherence recv_coherence.

(* a morphism C' -> C *)
Definition msg_morph' (e : entrypoint') : entrypoint := 
    match e with | incr' _ => incr tt end.
Definition setup_morph' : setup' -> setup := id.
Definition state_morph' (st : storage') : storage := 
        {| n_1 := st.(n) ; extra_data := tt ; |}.
Definition error_morph' : error' -> error := id.

Lemma init_coherence' : init_coherence_prop C' C setup_morph' state_morph' error_morph'.
Proof. now unfold init_coherence_prop. Qed.

Lemma recv_coherence' : recv_coherence_prop C' C msg_morph' state_morph' error_morph'.
Proof.
    unfold recv_coherence_prop.
    intros.
    simpl.
    unfold result_functor, receive, receive'.
    destruct op_msg; auto.
    now destruct e.
Qed.

Definition g : ContractMorphism C' C := 
    build_contract_morphism C' C setup_morph' msg_morph' state_morph' error_morph' 
        init_coherence' recv_coherence'.


(* f and g are isomorphisms *)
Theorem c_c'_equivalent : is_iso_cm f g.
Proof.
    unfold is_iso_cm, compose_cm, id_cm.
    split; apply eq_cm; cbn;
    unfold setup_morph, setup_morph', msg_morph, msg_morph', state_morph, state_morph',
        error_morph, error_morph';
    auto;
    apply functional_extensionality;
    intros.
    -   now destruct x, u.
    -   now destruct x, extra_data0.
    -   now destruct x, u.
Qed.

End Isomorphism.