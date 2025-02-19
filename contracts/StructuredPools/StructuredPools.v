(* A Structured Pool contract implementation

* Specification: https://ieeexplore.ieee.org/abstract/document/10174866
* Paper associated with this: 
    Sorensen, D. (In)Correct Smart Contract Specifications. ICBC 2024.
*)

(* import the specification of a structured pool and an FA2 contract *)
From FinCert.Specifications Require Import StructuredPoolsSpec.
From FinCert.Specifications.FA2Spec Require Import FA2Spec.
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
    (ctx: ContractCallContext) (cstate : state) (msg_payload : pool_data) : result := 
    (* check that the token has an exchange rate *)
    match FMap.find (token_pooled msg_payload) (stor_rates cstate)
    with | None => Err 0 | Some r_x =>
    (* tokens_held goes up appropriately *)
    let token := token_pooled msg_payload in
    let qty := qty_pooled msg_payload in
    let old_bal := get_bal token (stor_tokens_held cstate) in
    let stor_tokens_held' := FMap.add token (old_bal + qty) (stor_tokens_held cstate) in
    (* outstanding tokens change appropriately *)
    let stor_outstanding_tokens' := stor_outstanding_tokens cstate + r_x * qty in
    (* emit a TRANSFER call to the token in storage *)
    let transfer_to := {| 
        to_ := msg_payload.(token_pooled).(token_address) ;
        transfer_token_id := msg_payload.(token_pooled).(token_id) ;
        amount := msg_payload.(qty_pooled) ; |} in 
    let transfer_data := {| 
        from_ := ctx.(ctx_from) ;
        txs := [ transfer_to ] ; |} in
    let transfer_payload := [ transfer_data ] in 
    let transfer_call := act_call
        (* calls the pooled token address *)
        (msg_payload.(token_pooled).(token_address))
        (* with amount 0 *)
        0 
        (* and payload transfer_payload *)
        (serialize (Transfer transfer_payload)) in
    (* emit a MINT call *)
    let r_x := get_rate msg_payload.(token_pooled) (stor_rates cstate) in 
    let mint_data := {|
        mint_owner := ctx.(ctx_from) ;
        mint_token_id := cstate.(stor_pool_token).(token_id) ;
        qty := msg_payload.(qty_pooled) * r_x ; |} in 
    let mint_payload := [ mint_data ] in
    let mint_call := act_call 
        (* calls the pool token contract *)
        ((stor_pool_token cstate).(token_address))
        (* with amount 0 *)
        0
        (* and payload mint_payload *)
        (serialize (FA2Spec.Mint mint_payload)) in 
    (* the state gets renewed *)
    let new_state := {|
        stor_rates := cstate.(stor_rates) ;
        stor_tokens_held := stor_tokens_held' ;
        stor_pool_token := cstate.(stor_pool_token) ;
        stor_outstanding_tokens := stor_outstanding_tokens' ; 
    |} in
    (* entrypoint ends *)
    Ok (new_state, [ transfer_call ; mint_call ])
    end.

Definition calc_rx_inv (r_x : N) (q : N) : N := todo.

Definition unpool_entrypoint
    (ctx: ContractCallContext) (cstate : state) (msg_payload : unpool_data) :
    result := 
    (* checks for an exchange rate *)
    match FMap.find msg_payload.(token_unpooled) (stor_rates cstate)
    with | None => Err 0 | Some r_x =>
    (* tokens_held goes down appropriately *)
    if negb (N.leb
        (qty_unpooled msg_payload)
        (get_rate (token_unpooled msg_payload) (stor_rates cstate) * get_bal (token_unpooled msg_payload) (stor_tokens_held cstate)))
    then Err 0 else
    let token := msg_payload.(token_unpooled) in
    let r_x := get_rate token (stor_rates cstate) in 
    let qty := calc_rx_inv r_x msg_payload.(qty_unpooled) in
    let old_bal := get_bal token (stor_tokens_held cstate) in 
    let new_bal := old_bal - qty in 
    let stor_tokens_held' := FMap.add token new_bal (stor_tokens_held cstate) in 
    (* outstanding tokens change appropriately *)
    let rate_in := get_rate msg_payload.(token_unpooled) (stor_rates cstate) in 
    let qty_unpooled_nat := msg_payload.(qty_unpooled) in 
    let stor_outstanding_tokens' := stor_outstanding_tokens cstate - qty_unpooled_nat in 
    (* emits a BURN call to the pool_token in storage *)
    let burn_data := {|
        retiring_party := ctx.(ctx_from) ;
        retire_token_id := msg_payload.(token_unpooled).(token_id) ;
        retire_amount := msg_payload.(qty_unpooled) ;
    |} in 
    let burn_payload := [ burn_data ] in 
    let burn_call := act_call
        (* calls the pool token address *)
        (stor_pool_token cstate).(token_address)
        (* with amount 0 *)
        0
        (* with payload burn_payload *)
        (serialize (FA2Spec.Retire burn_payload)) in 
    (* emits a TRANSFER call to the token being unpooled *)
    let transfer_to := {|
        to_ :=  ctx.(ctx_from) ;
        transfer_token_id := msg_payload.(token_unpooled).(token_id) ;
        amount := msg_payload.(qty_unpooled) / rate_in ;
    |} in 
    let txs := [ transfer_to ] in 
    let transfer_data := {|
        from_ := ctx.(ctx_contract_address) ;
        txs := txs ;
    |} in 
    let transfer_payload := [ transfer_data ] in
    let transfer_call := act_call 
        (* call to the token address *)
        (msg_payload.(token_unpooled).(token_address))
        (* with amount = 0 *)
        0 
        (* with payload transfer_payload *)
        (serialize (FA2Spec.Transfer transfer_payload)) in 
    (* end txn *)
    let new_state := {|
        stor_rates := cstate.(stor_rates) ;
        stor_tokens_held := stor_tokens_held' ;
        stor_pool_token := cstate.(stor_pool_token) ;
        stor_outstanding_tokens := stor_outstanding_tokens' ; 
    |} in
    Ok (new_state, [ burn_call ; transfer_call ])
    end.

(* lots *)
Definition calc_delta_y (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N) : N := todo.

(* rate_decrease property; rates_balance property; rates_balance_2 *)
Definition calc_rx' (rate_in : N) (rate_out : N) (qty_trade : N) (d : N) (x : N) : N := todo.

Definition trade_entrypoint
    (ctx: ContractCallContext) (cstate : state) (msg_payload : trade_data) : result := 
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

Axiom pool_types : forall p, pool p = StructuredPoolsSpec.pool p.
Axiom unpool_types : forall u, unpool u = StructuredPoolsSpec.unpool u.
Axiom trade_types : forall t, trade t = StructuredPoolsSpec.trade t.
Axiom stor_rates_types : forall cstate, stor_rates cstate = StructuredPoolsSpec.stor_rates cstate.
Axiom stor_pool_token_types : forall cstate, stor_pool_token cstate = StructuredPoolsSpec.stor_pool_token cstate.
Axiom stor_tokens_held_types : forall cstate, stor_tokens_held cstate = StructuredPoolsSpec.stor_tokens_held cstate.
Axiom stor_outstanding_tokens_types : forall cstate, stor_outstanding_tokens cstate = StructuredPoolsSpec.stor_outstanding_tokens cstate.

Lemma fmap_find_add : forall (m : FMap token N) k v, 
    FMap.find k (FMap.add k v m) = Some v.
Proof. auto. Qed.

Lemma fmap_add_neq : forall (m : FMap token N) k1 k2 v, 
    k1 <> k2 -> FMap.find k1 (FMap.add k2 v m) = FMap.find k1 m.
Proof. auto. Qed.

(* the Structured Pools implementation is correct *)

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
            apply pool_types.
        +   right. left. exists u.
            apply unpool_types.
        +   right. right. left. exists t.
            apply trade_types.
    (* pool entrypoint spec *)
    -   unfold pool_entrypoint_check.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        exists r_x.
        now rewrite <- stor_rates_types.
    -   unfold pool_emits_txns.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        exists ({|
            to_ := token_address (token_pooled msg_payload);
            transfer_token_id := token_id (token_pooled msg_payload);
            amount := qty_pooled msg_payload
          |}).
        exists ({|
            from_ := ctx_from ctx;
            txs :=
              [{|
                 to_ := token_address (token_pooled msg_payload);
                 transfer_token_id := token_id (token_pooled msg_payload);
                 amount := qty_pooled msg_payload
               |}]
          |}).
        exists ([{|
            from_ := ctx_from ctx;
            txs :=
              [{|
                 to_ := token_address (token_pooled msg_payload);
                 transfer_token_id := token_id (token_pooled msg_payload);
                 amount := qty_pooled msg_payload
               |}]
          |}]).
        exists ({|
            mint_owner := ctx_from ctx;
            mint_token_id := token_id (stor_pool_token cstate);
            qty :=
              qty_pooled msg_payload *
                get_rate (token_pooled msg_payload) (stor_rates cstate)
          |}).
        exists ([{|
            mint_owner := ctx_from ctx;
            mint_token_id := token_id (stor_pool_token cstate);
            qty := qty_pooled msg_payload *
                get_rate (token_pooled msg_payload) (stor_rates cstate)
          |}]).
        rewrite <- stor_rates_types.
        rewrite <- stor_pool_token_types.
        repeat split; try now cbn.
    -   rename H into H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        unfold get_bal. cbn.
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        intros t H_t_neq.
        cbn.
        pose proof (fmap_add_neq (stor_tokens_held cstate) t (token_pooled msg_payload)
        (get_bal (token_pooled msg_payload) (stor_tokens_held cstate) + qty_pooled msg_payload)
        H_t_neq) as H_unchanged.
        unfold get_bal in *.
        now rewrite H_unchanged.
    -   unfold pool_rates_unchanged.
        intros * H_recv_ok t.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        do 2 rewrite <- stor_rates_types.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        now try inversion H_recv_ok.
    -   unfold pool_outstanding.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        do 2 rewrite <- stor_outstanding_tokens_types.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        cbn.
        rewrite <- stor_rates_types.
        unfold get_rate.
        now replace (FMap.find (token_pooled msg_payload) (stor_rates cstate))
        with (Some r_x) by now rewrite H_rx.
    (* unpool entrypoint spec *)
    -   unfold unpool_entrypoint_check.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- unpool_types in H_recv_ok.
        unfold unpool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        exists r_x.
        now rewrite <- stor_rates_types.
    -   unfold unpool_entrypoint_check_2.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- unpool_types in H_recv_ok.
        unfold unpool_entrypoint in H_recv_ok.
        rewrite <- stor_rates_types.
        rewrite <- stor_tokens_held_types.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N)
        eqn:H_negb;
        try inversion H_recv_ok.
        clear H2 H1 H0 H_recv_ok.
        assert ((qty_unpooled msg_payload <=?
        get_rate (token_unpooled msg_payload) (stor_rates cstate) *
        get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N = true) as H_negb_true.
        {   destruct (qty_unpooled msg_payload <=?
                get_rate (token_unpooled msg_payload) (stor_rates cstate) *
                get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N;
            auto. }
        clear H_negb.
        now apply N.leb_le.
    -   unfold unpool_emits_txns.
        intros * H_recv_ok.
        rewrite <- unpool_types in H_recv_ok.
        cbn in H_recv_ok.
        unfold unpool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        exists ({|
            retiring_party := ctx_from ctx;
            retire_token_id := token_id (token_unpooled msg_payload);
            retire_amount := qty_unpooled msg_payload
          |}).
        exists ([{|
            retiring_party := ctx_from ctx;
            retire_token_id := token_id (token_unpooled msg_payload);
            retire_amount := qty_unpooled msg_payload
          |}]).
        exists ({|
            to_ := ctx_from ctx;
            transfer_token_id := token_id (token_unpooled msg_payload);
            amount :=
              qty_unpooled msg_payload /
              get_rate (token_unpooled msg_payload) (stor_rates cstate)
          |}).
        exists ({|
            from_ := ctx_contract_address ctx;
            txs :=
              [{|
                 to_ := ctx_from ctx;
                 transfer_token_id := token_id (token_unpooled msg_payload);
                 amount :=
                   qty_unpooled msg_payload /
                   get_rate (token_unpooled msg_payload) (stor_rates cstate)
               |}]
          |}).
        exists ([{|
            from_ := ctx_contract_address ctx;
            txs :=
              [{|
                 to_ := ctx_from ctx;
                 transfer_token_id := token_id (token_unpooled msg_payload);
                 amount :=
                   qty_unpooled msg_payload /
                   get_rate (token_unpooled msg_payload) (stor_rates cstate)
               |}]
          |}]).
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N);
        try inversion H_recv_ok.
        rewrite <- stor_rates_types.
        rewrite <- stor_pool_token_types.
        repeat split; try now cbn.
    -   rename H into H_recv_ok.
        rewrite <- unpool_types in H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        rewrite <- stor_rates_types.
        simpl in H_recv_ok.
        unfold unpool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N);
        try inversion H_recv_ok.
        unfold get_bal.
        cbn.
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- unpool_types in H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        unfold unpool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N);
        try inversion H_recv_ok.
        intros t H_t_neq.
        cbn.
        pose proof (fmap_add_neq (stor_tokens_held cstate) t (token_unpooled msg_payload) (get_bal (token_unpooled msg_payload) (stor_tokens_held cstate) -
        calc_rx_inv (get_rate (token_unpooled msg_payload) (stor_rates cstate))
          (qty_unpooled msg_payload)) H_t_neq) as H_unchanged.
        unfold get_bal in *.
        now rewrite H_unchanged.
    -   unfold unpool_rates_unchanged.
        intros * H_recv_ok.
        do 2 rewrite <- stor_rates_types.
        rewrite <- unpool_types in H_recv_ok.
        simpl in H_recv_ok.
        unfold unpool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N);
        now try inversion H_recv_ok.
    -   unfold unpool_outstanding.
        intros * H_recv_ok.
        do 2 rewrite <- stor_outstanding_tokens_types.
        rewrite <- unpool_types in H_recv_ok.
        simpl in H_recv_ok.
        unfold unpool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_unpooled msg_payload) (stor_rates cstate)) 
        as [r_x | r_x] eqn:H_rx;
        try inversion H_recv_ok.
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N);
        now try inversion H_recv_ok.
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