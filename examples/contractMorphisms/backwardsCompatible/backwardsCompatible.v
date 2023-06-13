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
    result_functor state_morph error_morph (init c ctx s) = 
    init c ctx (setup_morph s).
Proof. auto. Qed.

Lemma recv_coherence : forall c ctx st op_msg, 
    result_functor (fun '(st, l) => (state_morph st, l)) error_morph (receive c ctx st op_msg) = 
    receive' c ctx (state_morph st) (option_map msg_morph op_msg).
Proof.
    intros. 
    unfold result_functor, msg_morph, state_morph, error_morph.
    induction op_msg; auto.
    now destruct a.
Qed.

(* construct the morphism *)
Definition f : ContractMorphism C C' := 
    build_contract_morphism C C' setup_morph msg_morph state_morph error_morph 
        init_coherence recv_coherence.


(* This theorem shows a strong notion of backwards compatibility because there is 
    an embedding of the old contract into the new *)
Theorem embedding : is_inj_cm f.
Proof.
    unfold is_inj_cm; unfold is_inj. 
    repeat split; intros.
    -   cbn in H. 
        now unfold setup_morph in H.
    -   now destruct a, a', u, u0.
    -   cbn in H.
        now unfold state_morph in H.
    -   cbn in H.
        now unfold error_morph in H.
Qed.

(** Theorem: 
    All reachable states have a corresponding reachable state, related by the 
    *embedding* f. *)
Theorem injection_invariant bstate caddr (trace : ChainTrace empty_state bstate):
    (* Forall reachable states with contract C at caddr, *)
    env_contracts bstate caddr = Some (C : WeakContract) ->
    (* forall reachable states of C cstate, there's a corresponding reachable state
        cstate' of C', related by the injection *)
    exists (cstate' cstate : storage),
    contract_state bstate caddr = Some cstate /\ 
    (* cstate' is a contract-reachable state of C' *)
    cstate_reachable C' cstate' /\
    (* .. equal to cstate *)
    cstate' = cstate.
Proof.
    intros c_at_caddr.
    pose proof (left_cm_induction f bstate caddr trace c_at_caddr)
    as H_cm_ind.
    destruct H_cm_ind as [cstate [cstate_c [cstate' [reach H_cm_ind]]]].
    now exists cstate', cstate.
Qed.

End BackwardsCompatible.