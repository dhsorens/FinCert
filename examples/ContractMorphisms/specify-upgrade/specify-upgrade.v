From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From FinCert.Meta Require Import ContractMorphisms.
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

(** This example recalls the Uranium Finance hack of 2021 due to an incorrect 
    upgrade:
    
    A constant `k` was changed from 1_000 to 10_000 in all but one of its 
    instances in the contract.

    This example illustrates how a contract upgrade can be *specified* using 
    contract morphisms, and uses that example.

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
Context { trade_data : Type } { trade_qty : trade_data -> N }.

Class Msg_Spec (T : Type) := {
    trade : trade_data -> T ; 
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
    forall cstate chain ctx trade_data cstate' acts,
    (** for any successful call to the trade entrypoint of C, *)
    receive C chain ctx cstate (Some (trade trade_data)) = Ok(cstate', acts) -> 
    (** the balance in storage updates as follows. *)
    get_bal cstate' = 
    get_bal cstate + calculate_trade (trade_qty trade_data).

Context { spec_trade : Prop }.

(** Now suppose that we have another calculate_trade function, this time which calculates 
    trades at one more digit of precision. *)
Definition round_down (n : N) := n / 10.

Context { calculate_trade_precise : N -> N }
    (** (i.e. calculate_trade_precise rounds down to calculate_trade) *)
    { calc_trade_coherence : forall n, 
        round_down (calculate_trade_precise n) = 
        calculate_trade (round_down n) }.

(** Suppose also that we have a round-down function on the storage type. *)

(** And that we have another contract, C', ... *)
Context { C' : Contract setup entrypoint storage error }.

(** but now trades are calculated in line with calculate_trade_precise. *)
Definition spec_trade_precise : Prop :=
    forall cstate chain ctx trade_data cstate' acts,
    (** ... meaning that for a successful call to the trade entrypoint of C', *)
    receive C' chain ctx cstate (Some (trade trade_data)) = Ok(cstate', acts) -> 
    (** the balance held in storage goes up by calculate_trade_precise. *)
    get_bal cstate' = 
    get_bal cstate + calculate_trade_precise (trade_qty trade_data).

Context { spec_trade_precise : Prop }.


(** Now, to specify the *upgrade* from C to C', we specify that there exist some morphism 
    f : C -> C' which satisfies the following conditions: *)
Context { st_morph : storage -> storage }
        { state_rounds_down : forall st, get_bal (st_morph st) = round_down (get_bal st) }.

(** 1. f rounds trades down when it maps inputs *)
Definition f_recv_input_rounds_down (f : ContractMorphism C' C) : Prop := 
    forall t', exists t,
    (msg_morph C' C f) (trade t') = trade t /\ 
    trade_qty t = round_down (trade_qty t').

(** 2. aside from trade, f doesn't touch the other entrypoints *)
Definition f_recv_input_other_equal (f : ContractMorphism C' C) : Prop := 
    forall msg o,
    (* for calls to all other entrypoints, *)
    msg = other o ->
    (* f is the identity *)
    option_map (msg_morph C' C f) (other o) = other o.

(** 3. f rounds down on the storage, but doesn't touch anything else. *)
Definition f_state_morph (f : ContractMorphism C' C) : Prop := 
    (state_morph C' C f) = st_morph.

(** 4. f is the identity on error values *)
Definition f_recv_output_err (f : ContractMorphism C' C) : Prop := 
    (error_morph C' C f) = @id error.

(** 5. f is the identity on the setup *)
Definition f_init_id (f : ContractMorphism C' C) : Prop := 
    (setup_morph C' C f) = @id setup.

(** Now we have a specification of the correct upgrade in terms of the existence of 
    a contract morphism. *)
Definition upgrade_spec (f : ContractMorphism C' C) : Prop := 
    f_recv_input_rounds_down f /\
    f_recv_input_other_equal f /\
    f_state_morph f /\
    f_recv_output_err f /\
    f_init_id f.


(** The Upgrade Metaspecification.
    To justify that upgrade_spec actually specifies a correct upgrade, we prove 
    the following result(s). *)

(*** Suppose there exists some f : C' -> C satisfying upgrade_spec. *)
Context { f : ContractMorphism C' C }
        { is_upgrade_morph : upgrade_spec f }.

(* All states of C' relate to equivalent states of C by rounding down *)
Theorem rounding_down_invariant bstate caddr (trace : ChainTrace empty_state bstate):
    (* Forall reachable states with contract at caddr, *)
    env_contracts bstate caddr = Some (C' : WeakContract) ->
    (* cstate is the state of the contract AND *)
    exists (cstate' cstate : storage),
    contract_state bstate caddr = Some cstate' /\
    (* cstate is contract-reachable for C AND *)
    cstate_reachable C cstate /\
    (* such that for cstate, the state of C in bstate, 
        the balance in cstate is rounded-down from the balance of cstate' *)
    get_bal cstate = round_down (get_bal cstate').
Proof.
    intros c_at_caddr.
    pose proof (left_cm_induction f bstate caddr trace c_at_caddr)
    as H_cm_ind.
    destruct H_cm_ind as [cstate' [contr_cstate' [cstate [reach H_cm_ind]]]].
    exists cstate', cstate.
    repeat split; auto.
    cbn in H_cm_ind.
    rewrite H_cm_ind.
    destruct is_upgrade_morph as [_ [_ [f_state [_ _]]]].
    now rewrite f_state.
Qed.

End UpgradeSpec.