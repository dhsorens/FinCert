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


(** Example 5.5.2: Mutable and Immutable Parts: Splitting an Upgradeable Contract 
    This example ... TODO 

*)

Section UpgradeTheory.
Context { Base : ChainBase }.

Context `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
        `{Serializable Msg_fnct} `{Serializable Setup_fnct} 
        `{Serializable State_fnct} `{Serializable Error_fnct}
        `{Serializable Msg_base} `{Serializable Setup_base} 
        `{Serializable State_base} `{Serializable Error_base}.

(* I have three contracts: C, C_fnct, C_base *)
Context 
  (* C is the full contract *)
  { C : Contract Setup Msg State Error } 
  (* C_fnct is "current", non-upgradeable contract version/functionality *)
  { C_fnct : Contract Setup_fnct Msg_fnct State_fnct Error_fnct }
  (* C_skel is the skeleton/constant contract; we will sum this with null_contract *)
  { C_skel : Contract Setup_base Msg_base State_base Error_base }.

(*  *)
Definition C_base := pointed_contract C_skel.

(* We have an EMBEDDING of C_fnct into C *)
Context { msg_morph_i : Msg_fnct -> Msg } 
  { state_morph_i : State_fnct -> State }
  { setup_morph_i : Setup_fnct -> Setup }
  { error_morph_i : Error_fnct -> Error }
  { msg_morph_i_inj : is_inj msg_morph_i } 
  { state_morph_i_inj : is_inj state_morph_i }
  { setup_morph_i_inj : is_inj setup_morph_i }.

Definition Msg_base' := (Msg_base + unit)%type.

(* We have a QUOTIENT of C_fnct onto C_base *)
Context {msg_morph_p : Msg -> Msg_base'}
  {state_morph_p : State -> State_base}
  {setup_morph_p : Setup -> Setup_base}
  {error_morph_p : Error -> Error_base}
  {msg_morph_p_surj : is_surj msg_morph_p}
  {state_morph_p_surj : is_surj state_morph_p}
  {setup_morph_p_surj : is_surj setup_morph_p}.

(* We have exact sequences on the message type *)
Context { null_state : State_base } { null_setup : Setup_base }
  { msg_exact : forall m,
  msg_morph_p m = inr tt <-> 
  (exists m', m = msg_morph_i m') }
  { state_exact : forall st, 
  state_morph_p st = null_state <->
  (exists st', st = state_morph_i st')}
  { setup_exact : forall s, 
  setup_morph_p s = null_setup <->
  (exists s', s = setup_morph_i s')}.



(** This is an "exact sequence" of contracts: 
    (null ->) C -> C_fnct ->> C_skel (-> null) *)

(** Now we construct the morphisms. *)

(* Construct the Embedding *)
Context { init_coherence_i : init_coherence_prop C_fnct C setup_morph_i state_morph_i error_morph_i }
        { recv_coherence_i : recv_coherence_prop C_fnct C msg_morph_i state_morph_i error_morph_i }.

(* The Embedding *)
Definition cm_embed : ContractMorphism C_fnct C := 
    build_contract_morphism C_fnct C 
      (* the morphisms *)
      setup_morph_i msg_morph_i state_morph_i error_morph_i
      (* coherence *)
      init_coherence_i recv_coherence_i.

(** Construct the Surjection *)
Context { init_coherence_p : init_coherence_prop C C_base setup_morph_p state_morph_p error_morph_p }
        { recv_coherence_p : recv_coherence_prop C C_base msg_morph_p state_morph_p error_morph_p }.

(* The Surjection *)
Definition cm_quot : ContractMorphism C C_base := 
    build_contract_morphism C C_base
      (* the morphisms *)
      setup_morph_p msg_morph_p state_morph_p error_morph_p
      (* coherence *)
      init_coherence_p recv_coherence_p.

(** Now we have an "exact" sequence of contracts. *)
  
(* A theorem that states that 
    "every execution trace is either from C_fnct or conforms to C_base" *)
Theorem exact_decompose : forall c ctx prev_state next_state new_acts msg, 
  (* If receive C executes successfully with some msg, then ...  *)
  receive C c ctx prev_state (Some msg) = Ok (next_state, new_acts) ->
  (* EITHER prev_state and msg have preimages in C_f, or ... *)
  (exists prev_state_f msg_f,
    (* msg is coming from one or the other *)
    msg = msg_morph_i msg_f /\
    (* for which coherence holds, prob not this *)
    prev_state = state_morph_i prev_state_f /\
    (* and the images of each are uninteresting in C_base *)
    state_morph_p prev_state = null_state /\
    msg_morph_p msg = inr tt) \/
  (* OR the image in C_b is nontrivial *)
  (exists m,
    state_morph_p prev_state <> null_state /\
    msg_morph_p msg = inl m).
Proof.
Admitted.


End UpgradeTheory.