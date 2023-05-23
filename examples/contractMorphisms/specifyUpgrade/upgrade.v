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


(** Example 5.3.1: 
    This example recalls the Uranium Finance hack of 2021 due to an incorrect upgrade:
    A constant `k` was changed from 1_000 to 1_000_000 in all but one of its instances 
    in the contract.

    This example illustrates how a contract upgrade can be *specified* using contract 
    morphisms, and uses that example.
    We have formulated this example to be as general as possible.
*)

Section UpgradeSpec.
Context { Base : ChainBase }.

(** Assume we have a calculate_trade function which is used to calculate trades in 
    a smart contract. It takes some input in N and returns the output of the trade, also in N. *)
Context  { calculate_trade : N -> N }.

(** Assume that we have some storage type which keeps track of balances via
    a function `get_bal` *)
Context { storage : Type } `{ storage_ser : Serializable storage }
        { get_bal : storage -> N }
        (* Also assume some other relevant types of the contract. *)
        { setup : Type } `{ setup_ser : Serializable setup }
        { other_entrypoint : Type }.

(** We assume that entrypoint type includes a trade function, among other entrypoints. *)
Class Msg_Spec (T : Type) := {
    trade : N -> T ; 
    (* for any other entrypoint types *)
    other : other_entrypoint -> option T ;
}.

Context { entrypoint : Type } `{ e_ser : Serializable entrypoint } `{ e_msg : Msg_Spec entrypoint }.

(** And we assume anything in the entrypoint type is of the form `trade n` or (roughly) `other o`. *)
Definition msg_destruct : Prop := 
    forall e,
    (exists n, e = trade n) \/ 
    (exists o, Some e = other o).
Context { e_msg_destruct : msg_destruct }.

(** Thus, the entrypoint type has this form:

    Inductive entrypoint := 
        | trade (qty : N)
        | ... .
*)

(* final definitions of contract types *)
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

(*** Now suppose that we have a contract with those types ... *)
Context { C : Contract setup entrypoint storage error }.

(** such that get_bal changes according to calculate_trade, meaning that: *)
Definition spec_trade : Prop :=
    forall cstate chain ctx qty cstate' acts,
    (** for any successful call to the trade entrypoint of C, *)
    receive C chain ctx cstate (Some (trade qty)) = Ok(cstate', acts) -> 
    (** the balance in storage updates as follows. *)
    get_bal cstate' = 
    get_bal cstate + calculate_trade qty.

Context { spec_trade : Prop }.

(** Now suppose that we have another calculate_trade function, this time which calculates 
    trades at three more digits of precision. *)
Definition round_down (n : N) := n / 1_000.

Context { calculate_trade_precise : N -> N }
    (** (i.e. calculate_trade_precise rounds down to calculate_trade) *)
    { calc_trade_coherence : forall n, 
        round_down (calculate_trade_precise n) = 
        calculate_trade (round_down n) }.

(** Suppose also that we have a round-down function on the storage type. *)
Context { state_morph : storage -> storage }
    { state_rounds_down : forall st, get_bal (state_morph st) = round_down (get_bal st) }.

(** And that we have another contract, C', ... *)
Context { C' : Contract setup entrypoint storage error }.

(** but now trades are calculated in line with calculate_trade_precise. *)
Definition spec_trade_precise : Prop :=
    forall cstate chain ctx qty cstate' acts,
    (** ... meaning that for a successful call to the trade entrypoint of C', *)
    receive C' chain ctx cstate (Some (trade qty)) = Ok(cstate', acts) -> 
    (** the balance held in storage goes up by calculate_trade_precise. *)
    get_bal cstate' = 
    get_bal cstate + calculate_trade_precise qty.

Context { spec_trade_precise : Prop }.


(** Now, to specify the *upgrade* from C to C', we specify that there exist some morphism 
    f : C -> C' which satisfies the following conditions: *)

(** 1. f rounds trades down when it maps inputs *)
Definition f_recv_input_rounds_down (f : ContractMorphism C' C) : Prop := 
    forall c ctx st e t,
    (*  *)
    e = trade t -> 
    (*  *)
    recv_inputs C' C (recv_cm f) (c, ctx, st, (Some e)) = 
    (c, ctx, state_morph st, Some (trade (round_down t))).

(** 2. aside from trade, f doesn't touch the other entrypoints *)
Definition f_recv_input_other_equal (f : ContractMorphism C' C) : Prop := 
    forall e o,
    (*  *)
    e = other o ->
    (*  *)
    recv_inputs C' C (recv_cm f) = id.

(** 3. f rounds down on the storage, but doesn't touch anything else. *)
Definition f_recv_output_ok (f : ContractMorphism C' C) : Prop := 
    forall x st acts,
    x = Ok (st, acts) ->
    recv_outputs C' C (recv_cm f) x = Ok (state_morph st, acts).

(** 4. f is the identity on error values *)
Definition f_recv_output_err (f : ContractMorphism C' C) : Prop := 
    forall x e,
    x = Err e ->
    recv_outputs C' C (recv_cm f) x = x.

(** 5. f is the identity on contract initialization *)
Definition f_init_id (f : ContractMorphism C' C) : Prop := 
    init_inputs C' C (init_cm f) = id /\
    init_outputs C' C (init_cm f) = id.

(** Now we have a specification of the correct upgrade in terms of the existence of 
    a contract morphism. *)
Definition upgrade_spec (f : ContractMorphism C' C) : Prop := 
    f_recv_input_rounds_down f /\
    f_recv_input_other_equal f /\
    f_recv_output_ok f /\
    f_recv_output_err f /\
    f_init_id f.




(** The Upgrade Metaspecification.
    To justify that upgrade_spec actually specifies a correct upgrade, we prove the following
    result(s). *)

(*** Suppose there exists some f : C' -> C satisfying upgrade_spec. *)
Context { f : ContractMorphism C' C } { is_upgrade_morph : upgrade_spec f }.


(** Then (TODO) A property that formalizes "does the same but different" *)





End UpgradeSpec.