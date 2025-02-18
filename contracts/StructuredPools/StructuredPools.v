(* A Structured Pool contract implementation

* Specification: https://ieeexplore.ieee.org/abstract/document/10174866
* Paper associated with this: 
    Sorensen, D. (In)Correct Smart Contract Specifications. ICBC 2024.
*)

(* import the specification of a structured pool and an FA2 contract *)
From FinCert.Specifications Require Import StructuredPoolsSpec.
From FinCert.Specifications.FA2Spec Require FA2Spec.
From FinCert.Meta Require Import ContractMorphisms.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
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
    Global Instance error_serializable : Serializable error := todo.
End Serialization.

(* init function definition *)
Definition init (_ : Chain) (_ : ContractCallContext) (n : setup) :
    ResultMonad.result state error := 
    todo.

(* entrypoint function definitions *)
Definition pool_entrypoint 
    (ctx: ContractCallContext) (st : state) (p : pool_data) : result := 
    (* check that the token has an exchange rate *)
    match FMap.find (token_pooled p) (stor_rates st)
    with | None => Err 0 | Some r_x =>
    (* tokens_held goes up appropriately *)
    let token := token_pooled p in
    let qty := qty_pooled p in
    let old_bal := get_bal token (stor_tokens_held st) in
    let st' := FMap.add token (old_bal + qty) (stor_tokens_held st) in
    (* outstanding tokens change appropriately *)
    let stor_outstanding_tokens' := stor_outstanding_tokens st + r_x * qty in
    (* emit a TRANSFER call to the token in storage *)
    let transfer_data := FA2Spec.Build_transfer_data 
        ctx.(ctx_origin)
        [ 
            FA2Spec.Build_transfer_to 
                p.(token_pooled).(token_address)
                p.(token_pooled).(token_id)
                qty
        ] in
    let act_transfer := 
        act_call (p.(token_pooled).(token_address)) 0 
        (serialize (FA2Spec.Transfer [ transfer_data ])) in
    (* emit a MINT call *)
    let mint_data := FA2Spec.Build_mint_data
        ctx.(ctx_origin)
        st.(stor_pool_token).(token_id)
        qty in 
    let mint_payload := (serialize (FA2Spec.Mint [ mint_data ])) in
    let act_mint := act_call (st.(stor_pool_token).(token_address)) 0 mint_payload in 
    let new_state := {|
        stor_rates := st.(stor_rates) ;
        stor_tokens_held := st' ;
        stor_pool_token := st.(stor_pool_token) ;
        stor_outstanding_tokens := stor_outstanding_tokens' ; 
    |} in
    Ok (new_state, [act_transfer ; act_mint ])
    end.

Definition calc_rx_inv (r_x : N) (q : N) : N := todo.

Definition unpool_entrypoint
    (ctx: ContractCallContext) (st : state) (u : unpool_data) : result := 
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

Definition trade_entrypoint
    (ctx: ContractCallContext) (st : state) (t : trade_data) : result := 
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
Definition receive (_ : Chain) (ctx : ContractCallContext) (st : state) 
    (op_msg : option msg) : result :=
    match op_msg with 
    | Some (pool p) => pool_entrypoint ctx st p
    | Some (unpool u) => unpool_entrypoint ctx st u
    | Some (trade t) => trade_entrypoint ctx st t
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup msg state error := 
    build_contract init receive.


Section StructuredPoolsCorrect.

Context {other_entrypoint : Type}.

Instance msg_spec : @Msg_Spec Base other_entrypoint msg := todo.
Instance setup_spec : Setup_Spec setup := todo.
Instance state_spec : State_Spec state := todo.
Instance error_spec : Error_Spec error := todo.

(* a proof that the Structured Pools implementation is correct *)  

(* the Structured Pools implementation is correct *)

Theorem sp_correct :
    @is_structured_pool Base setup msg state error other_entrypoint 
    setup_serializable entrypoint_serializable
    state_serializable error_serializable
    msg_spec setup_spec state_spec
    calc_rx_inv calc_delta_y calc_rx' C.
Proof.
    unfold is_structured_pool;
    repeat split.
    (* none fails *)
    -   unfold none_fails.
        intros.
        now exists 0.
    (* msg destruct *)
    -   unfold msg_destruct.
        intros.
        destruct m eqn:H_m.
        +   left. exists p.
            admit.
        +   right. left. exists u.
            admit.
        +   right. right. left. exists t.
            admit.
    (* pool entrypoint spec *)
    -   unfold pool_entrypoint_check.
        intros * H_recv_ok.
        admit.
    -   unfold pool_emits_txns.
        admit.
    -   admit.
    -   admit.
    -   unfold pool_rates_unchanged.
        intros * H_recv_ok t.
        admit.
    -   unfold pool_outstanding.
        intros * H_recv_ok.
        admit.
    (* unpool entrypoint spec *)
    -   unfold unpool_entrypoint_check.
        intros * H_recv_ok.
        admit.
    -   unfold unpool_entrypoint_check_2.
        intros * H_recv_ok.
        admit.
    -   unfold unpool_emits_txns.
        intros * H_recv_ok.
        admit.
    -   admit.
    -   admit.
    -   unfold unpool_rates_unchanged.
        intros * H_recv_ok.
        admit.
    -   unfold unpool_outstanding.
        intros * H_recv_ok.
        admit.
    (* trade entrypoint spec *)
    -   unfold trade_entrypoint_check.
        intros * H_recv_ok.
        admit.
    -   unfold trade_entrypoint_check_2.
        intros * H_recv_ok.
        admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
    -   admit.
Admitted.

End StructuredPoolsCorrect.

End StructuredPools.