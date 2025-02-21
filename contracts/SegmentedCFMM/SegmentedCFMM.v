(* A Segmented Liquidity CFMM 

* Reference implementation: https://github.com/tezos-checker/segmented-cfmm 
* Specification: https://github.com/tezos-checker/segmented-cfmm/blob/master/docs/specification.md
*)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From FinCert.Meta Require Import ContractMorphisms.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.
(* contract dependencies *)
From FinCert.Contracts Require Import SegmentedCFMMTypes.
(* const *)
(* helpers *)
(* transfers *)
From FinCert.Contracts Require Import SegmentedCFMMMath.
From FinCert.Contracts Require Import SegmentedCFMMSwaps.
(* token/FA2.mligo analogue *)
(* import the specification *)
From FinCert.Specifications Require Import SegmentedCFMMSpec.


Import ListNotations.
Open Scope N_scope.
Open Scope string.

Section SegmentedCFMM.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.


(* TODO *)
Axiom todo : forall {A}, A.


(** Type Definitions **)


(* entrypoint type definition *)
Inductive entrypoint :=
| x_to_y (p : x_to_y_param)
| y_to_x (p : y_to_x_param)
| x_to_x_prime (p : x_to_x_prime_param)
| set_position (p : set_position_param)
| update_position (p : update_position_param)
| get_position_info (p : get_position_info_param)
| call_FA2 (p : call_FA2_param)
| snapshot_cumulatives_inside (p: cumulatives_inside_snapshot_param)
| observe (p : observe_param)
| increase_observation_count (p : increase_observation_count_param).

(* setup type definition *)
Definition setup := N.


Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := 
    (* Derive Serializable entrypoint_rect<incr>. *) todo.
End Serialization.


(** Entrypoint Function Definitions *)



Definition fn_x_to_x_prime
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : x_to_x_prime_param) : result :=
    todo.

Definition fn_set_position
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : set_position_param) : result :=
    todo.

Definition fn_call_FA2
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : call_FA2_param) : result :=
    todo.

Definition fn_update_position
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : update_position_param) : result :=
    todo.

Definition fn_get_position_info
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : get_position_info_param) : result :=
    todo.

Definition fn_snapshot_cumulatives_inside
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : cumulatives_inside_snapshot_param) : result :=
    todo.

Definition fn_observe
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : observe_param) : result :=
    todo.

Definition fn_increase_observation_count
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : increase_observation_count_param) : result :=
    todo.


(** Contract Definition **)

(* init function definition *)
Definition init (_ : Chain) (_ : ContractCallContext) (n : setup) :
    ResultMonad.result storage N := 
    todo.

(* receive function definition *)
Definition receive (c : Chain) (ctx : ContractCallContext) (st : storage)
    (msg : option entrypoint) : result :=
    match msg with
    | Some param =>
        match param with
        | x_to_y p => fn_x_to_y c ctx st p
        | y_to_x p => fn_y_to_x c ctx st p
        | x_to_x_prime p => fn_x_to_x_prime c ctx st p
        | set_position p => fn_set_position c ctx st p
        | call_FA2 p => fn_call_FA2 c ctx st p
        | update_position p => fn_update_position c ctx st p
        | get_position_info p => fn_get_position_info c ctx st p
        | snapshot_cumulatives_inside p =>
            fn_snapshot_cumulatives_inside c ctx st p
        | observe p => fn_observe c ctx st p
        | increase_observation_count p =>
            fn_increase_observation_count c ctx st p
        end
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup entrypoint storage error := 
    build_contract init receive.

End SegmentedCFMM.