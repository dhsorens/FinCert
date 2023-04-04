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

(* TODO: description of isomorphism *)
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Section Contract.
Inductive entrypoint := | incr (u : unit).
Record storage := build_storage { n_1 : N ; n_2 : N }.
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
    Ok ({| n_1 := n ; n_2 := n |}).

(* receive function definition *)
Definition receive (_ : Chain) (_ : ContractCallContext) (st : storage) 
    (msg : option entrypoint) : result :=
    match msg with 
    | Some (incr _) => Ok ({| n_1 := st.(n_1) + 1 ; n_2 := st.(n_1) + 1 ; |}, [])
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

Lemma init_coherence : forall c ctx s, 
    (init_result_transform state_morph error_morph) ((Blockchain.init C) c ctx s) = 
    (Blockchain.init C') c ctx (setup_morph s).
Proof. auto. Qed.

Lemma recv_coherence : forall c ctx st op_msg, 
    (recv_result_transform state_morph error_morph) ((Blockchain.receive C) c ctx st op_msg) = 
    (Blockchain.receive C') c ctx (state_morph st) (option_map msg_morph op_msg).
Proof. Admitted.

Definition f : ContractMorphism C C' := 
    simple_cm msg_morph setup_morph state_morph error_morph 
        init_coherence recv_coherence.
    

(* a morphism C' -> C *)
Definition msg_morph' (e : entrypoint') : entrypoint := 
    match e with | incr' _ => incr tt end.
Definition setup_morph' : setup' -> setup := id.
Definition state_morph' (st : storage') : storage := 
        {| n_1 := st.(n) ; n_2 := st.(n) ; |}.
Definition error_morph' : error' -> error := id.

Lemma init_coherence' : forall c ctx s, 
    (init_result_transform state_morph' error_morph') ((Blockchain.init C') c ctx s) = 
    (Blockchain.init C) c ctx (setup_morph' s).
Proof. auto. Qed.

Lemma recv_coherence' : forall c ctx st op_msg, 
    (recv_result_transform state_morph' error_morph') ((Blockchain.receive C') c ctx st op_msg) = 
    (Blockchain.receive C) c ctx (state_morph' st) (option_map msg_morph' op_msg).
Proof. Admitted.

Definition g : ContractMorphism C' C := 
    simple_cm msg_morph' setup_morph' state_morph' error_morph' 
        init_coherence' recv_coherence'.


(* f and g are isomorphisms *)        
Theorem c_c'_equivalent : is_iso_cm f g.
Proof.
    unfold is_iso_cm. split; apply is_eq_cm; try apply is_eq_cm_init; try apply is_eq_cm_recv; apply functional_extensionality; intros; unfold composition_cm, id_cm; cbn.
    -   destruct x as [x s]. destruct x as [c ctx]. auto.
    -   destruct x; auto. cbn. destruct t.
        unfold state_morph', state_morph, id_fun. cbn. 
Admitted.

End Isomorphism.