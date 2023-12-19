(* A Generic Token Contract Specification *)
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Ensembles.
From Coq Require Import Permutation.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.
From Coq Require Import Lia.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(* =============================================================================
*  Specification
* ============================================================================= *)

Section Specification.
Context { Base : ChainBase }
    { Setup Msg State Error : Type }
    `{Serializable Setup} `{Serializable Msg}
    `{Serializable State} `{Serializable Error}.

(* Some preliminary definitions *)
Record transfer_destination :=
    build_transfer_destination {
    to_ : Address ;
    amount : N ;
}.

Record transfer_param :=
    build_transfer {
    from_ : Address ;
    txs : list transfer_destination ;
}.

Definition error := N.

Definition get_bal (addr : Address) (balances : FMap Address N) : N :=
    match FMap.find addr balances with | Some r => r | None => 0 end.

Definition suml l := fold_right N.add 0 l.

(* ====
    Typeclasses characterize Setup, Msg, State, Error types 
 * ==== *)

(* Setup specification *)
Class token_setup_spec (T : Type) := {
    (* derive the initial ledger *)
    init_ledger : T -> FMap Address N ;
}.

(* Msg specification *)
Class token_msg_spec (T other_entrypoint : Type) := build_token_msg_spec {
    transfer : transfer_param -> T ;
    (* any other potential entrypoints, e.g. giving permissions *)
    other : other_entrypoint -> option T ;
}.

(* State specification *)
Class token_state_spec (T : Type) := {
    (* the token_id parameter for token IDs in more advanced tokens *)
    ledger : T -> FMap Address N ;
}.

(* Error specification *)
Class token_error_spec (T : Type) := build_error_spec {
    error_to_Error : error -> T ;
}.

(* we assume that our contract types satisfy the type specifications *)
Context {token_other : Type}
        `{token_setup_spec Setup} `{token_msg_spec Msg other_entrypoint}
        `{token_state_spec State} `{token_error_spec Error}.

(* First, we assume that all successful calls require a message *)
Definition msg_required (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx,
    (* the receive function returns an error if the token to be pooled is not in the 
       rates map held in the storage (=> is not in the semi-fungible family) *)
    exists err : Error, 
    receive contract chain ctx cstate None = Err err.

(* We also specify that the Msg type is fully characterized by its typeclass
    (this is an induction principle for the Msg type) *)
Definition msg_destruct (contract : Contract Setup Msg State Error) : Prop :=
    forall (m : Msg),
    (exists t, m = transfer t) \/
    (exists o, Some m = other o).


(* ====
    Entrypoint Specification
 * ==== *)

 (* if Transfer succeeds, the balance changes accordingly *)
 Definition transfer_updates_balances (contract : Contract Setup Msg State Error) : Prop :=
    forall cstate chain ctx msg_payload cstate' acts,
    (* the TRANSFER entrypoint was called successfully *)
    receive contract chain ctx cstate (Some (transfer msg_payload)) =
        Ok (cstate', acts) ->
    (* destruct msg_payload *)
    let addr_from := from_ msg_payload in
    let txn_list := txs msg_payload in
    (* the balance of the sender, addr_from, decreases by the amt they sent *)
    let from_bal  := get_bal addr_from (ledger cstate)  in 
    let from_bal' := get_bal addr_from (ledger cstate') in 
    let sum_sent  := suml (List.map (fun t => amount t) txn_list) in 
    from_bal' = from_bal - sum_sent /\
    (* the sum sent does not exceed the balance of the sender *)
    sum_sent <= from_bal /\
    (* the balance of each recipient increases by how much they were sent *)
    forall addr,
    let sum_recip :=
        suml (List.map (fun t => amount t)
            (List.filter (fun t => address_eqb addr (to_ t)) txn_list)) in
    let to_bal  := get_bal addr (ledger cstate) in
    let to_bal' := get_bal addr (ledger cstate') in
    to_bal' = to_bal + sum_recip.

(* possibly something to characterize the "other" entrypoint *)

(* ====
    We amalgamate the propositions into a single proposition
 * ==== *)
Definition is_token (C : Contract Setup Msg State Error) : Prop := 
    transfer_updates_balances C.

(* ====
    A custom tactic which destructs is_token, for reasoning about token contracts
 * ==== *)

(* no need, for now *)

(* =============================================================================
*  Metaspecification
* ============================================================================= *)
Section MetaSpecification.
Context {contract : Contract Setup Msg State Error}
    { is_sp : is_token contract }.


End MetaSpecification.

End Specification.