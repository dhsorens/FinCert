(* A Structured Pool contract implementation

* Specification: https://ieeexplore.ieee.org/abstract/document/10174866
* Paper associated with this: 
    Sorensen, D. (In)Correct Smart Contract Specifications. ICBC 2024.
*)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From FinCert.Meta Require Import ContractMorphisms.
(* import the specification *)
From FinCert.Specifications Require Import StructuredPoolsSpec.
(* *)
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

Section StructuredPools.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* TODO *)
Axiom todo : forall {A}, A.

(* the dntrypoint Type *)
Inductive msg := 
| pool (p : pool_data)
| unpool (u : unpool_data)
| trade (t : trade_data).

(* msg type conforms to msg spec *)
(* Global Instance msg_is_Msg : Msg_Sepc msg := todo. *)

(* the state type *)
Record state := build_state {
    stor_rates : FMap token exchange_rate ;
    stor_tokens_held : FMap token N ;
    stor_pool_token : token ;
    stor_outstanding_tokens : N ; 
}.

(* Global Instance state_is_State : State_Spec state := todo. *)

(* the setup type *)
Record setup := build_setup {
    init_rates : FMap token exchange_rate ;
    init_pool_token : token ;
}.

(* Global Instance setup_is_Setup : Setup_Spec setup := todo. *)


(* the result type *)
Definition result : Type := ResultMonad.result (state * list ActionBody) error.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable msg := todo.
    (* Derive Serializable msg_rect<pool,unpool,trade>. *) 
    Global Instance state_serializable : Serializable state := todo.
    Global Instance setup_serializable : Serializable setup := todo.
End Serialization.

(* init function definition *)
Definition init (_ : Chain) (_ : ContractCallContext) (n : setup) :
    ResultMonad.result state error := 
    todo.

(* entrypoint function definitions *)
Definition pool_entrypoint (st : state) (p : pool_data) : result := 
    (* check that the token has an exchange rate *)
    match FMap.find (token_pooled p) (stor_rates st) with 
    | Some pooled_rate => Ok (todo)
    | None => Err 0
    end.
    (* tokens_held goes up appropriately *)
    (* outstanding tokens change appropriately *)
    (* rates don't change *)
    (* emit a TRANSFER call to the token in storage *)

Definition calc_rx_inv (r_x : N) (q : N) : N := todo.

Definition unpool_entrypoint (st : state) (u : unpool_data) : result := 
    (* checks for an exchange rate *)
    (* tokens_held goes down appropriately *)
    (* outstanding tokens change appropriately *)
    (* rates don't change *)
    (* emits a BURN call to the pool_token in storage *)
    todo.

(* lots *)
Definition calc_delta_y (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N) : N := todo.

(* rate_decrease property; rates_balance property; rates_balance_2 *)
Definition calc_rx' (rate_in : N) (rate_out : N) (qty_trade : N) (d : N) (x : N) : N := todo.

Definition trade_entrypoint (st : state) (t : trade_data) : result := 
    (* check that token_in and token_out have exchange rates *)
    (* check inputs to the trade calculation are all positive *)
    (* trade is priced calc_delta_y appropriately *)
    (* change in rate calculated with calc_rx' *)
    (* trade emits two TRANSFER actions *)
    (* tokens_held updated appropriately *)
    (* outstanding updated appropriately *)
    (* trade amts are nonnegative *)
    todo.

(* receive function definition *)
Definition receive (_ : Chain) (_ : ContractCallContext) (st : state) 
    (op_msg : option msg) : result :=
    match op_msg with 
    | Some (pool p) => pool_entrypoint st p
    | Some (unpool u) => unpool_entrypoint st u
    | Some (trade t) => trade_entrypoint st t
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup msg state error := 
    build_contract init receive.

End StructuredPools.