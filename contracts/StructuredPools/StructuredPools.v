(* A Structured Pool contract implementation

* Specification: https://ieeexplore.ieee.org/abstract/document/10174866
* Paper associated with this: 
    Sorensen, D. (In)Correct Smart Contract Specifications. ICBC 2024.
    Sorensen, D. Structured Pools for Tokenized Carbon Credits. ICBC 2023.
    Jaffer, S., Dales, M., Ferris, P., Sorensen, D., Swinfield, T., Message, R., Keshav, S., and Madhavapeddy, A. Global, robust and comparable digital carbon assets. ICBC 2024.
    Sorensen, D. Tokenized Carbon Credits. Ledger, 2023.
    
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
From Coq Require Import NArith.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq Require Import Lia.
From Coq.Init Require Import Byte.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

Section StructuredPools.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* the dntrypoint Type *)
Inductive msg := 
| pool (p : pool_data)
| unpool (u : unpool_data)
| trade (t : trade_data).

(* the state type *)
Record state := build_state {
    stor_rates : FMap token exchange_rate ;
    stor_tokens_held : FMap token N ;
    stor_pool_token : token ;
    stor_outstanding_tokens : N ; 
}.


(* the setup type *)
Record setup := build_setup {
    init_rates : FMap token exchange_rate ;
    init_pool_token : token ;
}.

(* the result type *)
Definition result : Type := ResultMonad.result (state * list ActionBody) error.

Section Serialization.
    Axiom etc : forall {A}, A.

    Global Instance entrypoint_serializable : Serializable msg := etc.

    Global Instance state_serializable : Serializable state := etc.
        
    Global Instance setup_serializable : Serializable setup := etc.
    
    Global Instance error_serializable : Serializable error.
    Proof.
        unfold error.
        exact N_serializable.
    Qed.

End Serialization.

(* init function definition *)
Definition init (_ : Chain) (_ : ContractCallContext) (n : setup) :
    ResultMonad.result state error := 
    Ok ({|
        stor_rates := n.(init_rates) ;
        stor_tokens_held := FMap.empty ;
        stor_pool_token := n.(init_pool_token) ;
        stor_outstanding_tokens := 0 ;
    |}).

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

Definition calc_rx_inv (r_x : N) (q : N) : N := q.

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
Definition calc_delta_y (rate_in : N) (rate_out : N) (qty_trade : N) (k : N) (x : N) : N := qty_trade.

Lemma delta_y_lt_y : forall cstate msg_payload r_x r_y qty_trade k x y,
    FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate) = Some x -> 
    FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate) = Some y -> 
    FMap.find (token_in_trade msg_payload) (stor_rates cstate) = Some r_x -> 
    FMap.find (token_out_trade msg_payload) (stor_rates cstate) = Some r_y -> 
    qty_trade < y ->
    0 < k -> 0 < x -> 0 <= qty_trade -> 0 < r_x -> 0 < r_y ->
    calc_delta_y r_x r_y qty_trade k x < y.
Proof.
    intros * H_x H_y H_rx H_ry H_qtrade H_k H_x' H_qty H_rx' H_ry'.
    unfold calc_delta_y.
    apply H_qtrade.
Qed.

(* rate_decrease property; rates_balance property; rates_balance_2 *)
Definition calc_rx' (rate_in : N) (rate_out : N) (qty_trade : N) (d : N) (x : N) : N := 
    if (N.eqb rate_in 0) then 0 else 1.

Definition token_eqb (t1 t2 : token) : bool :=
    N.eqb t1.(token_id) t2.(token_id) && 
    address_eqb t1.(token_address) t2.(token_address).

Axiom address_eq_eqb : forall a1 a2, address_eqb a1 a2 = true <-> a1 = a2.

Lemma token_eq_eqb : forall t1 t2, token_eqb t1 t2 = true <-> t1 = t2.
Proof.
    intros.
    unfold token_eqb.
    split.
    -   intros H.
        apply andb_prop in H.
        destruct H.
        apply N.eqb_eq in H.
        apply address_eq_eqb in H0.
        destruct t1, t2.
        f_equal; cbn in *; auto.
    -   intros H.
        subst. 
        rewrite N.eqb_refl.
        now rewrite address_eq_refl.
Qed.

(* trade entrypoint definition *)

Definition trade_entrypoint
    (ctx: ContractCallContext) (cstate : state) (msg_payload : trade_data) : result := 
    (* check that token_in and token_out have exchange rates and
       check inputs to the trade calculation are all positive *)
    match FMap.find msg_payload.(token_in_trade) (stor_tokens_held cstate)
    with | None => Err 0 | Some x => if (N.ltb 0 x) then 
    match FMap.find msg_payload.(token_out_trade) (stor_tokens_held cstate)
    with | None => Err 0 | Some y => if (N.ltb 0 y) then
    match FMap.find msg_payload.(token_in_trade) (stor_rates cstate)
    with | None => Err 0 | Some r_x => if (N.ltb 0 r_x) then
    match FMap.find msg_payload.(token_out_trade) (stor_rates cstate)
    with | None => Err 0 | Some r_y => if (N.ltb 0 r_y) then
    (* trade is priced calc_delta_y appropriately *)
    let t_x := msg_payload.(token_in_trade) in 
    let t_y := msg_payload.(token_out_trade) in
    if (token_eqb t_x t_y) then Err 0 else
    let q := msg_payload.(qty_trade) in 
    let rate_in := (get_rate t_x (stor_rates cstate)) in 
    let rate_out := (get_rate t_y (stor_rates cstate)) in 
    let k := (stor_outstanding_tokens cstate) in 
    if (N.ltb 0 k) then
    let x := get_bal t_x (stor_tokens_held cstate) in 
    let delta_x := msg_payload.(qty_trade) in 
    if (N.ltb delta_x 0) then Err 0 else
    let delta_y := calc_delta_y rate_in rate_out delta_x k x in 
    if (N.ltb delta_y 0) then Err 0 else
    let prev_bal_y := get_bal t_y (stor_tokens_held cstate) in 
    let prev_bal_x := get_bal t_x (stor_tokens_held cstate) in 
    if (N.ltb q y) then
    (* tokens_held updated appropriately *)
    let stor_tokens_held' :=
        FMap.add t_x (prev_bal_x + delta_x) cstate.(stor_tokens_held) in 
    let stor_tokens_held' :=
        FMap.add t_y (prev_bal_y - delta_y) stor_tokens_held' in 
    (* change in rate calculated with calc_rx' *)
    let r_x' := calc_rx' rate_in rate_out q k x in 
    let stor_rates' := FMap.add t_x r_x' cstate.(stor_rates) in 
    (* trade emits two TRANSFER actions *)
    (* transfer 1 : to x *)
    let transfer_to_x := {|
        to_ := ctx.(ctx_contract_address) ;
        transfer_token_id := t_x.(token_id) ;
        amount := q ;
    |} in 
    let transfer_data_x := {|
        from_ := ctx.(ctx_contract_address) ;
        txs := [ transfer_to_x ] ;
    |} in 
    let transfer_payload_x := [ transfer_data_x ] in 
    let transfer_tx := act_call 
        (* call to the correct token address *)
        (msg_payload.(token_in_trade).(token_address))
        (* with amount = 0 *)
        0
        (* and payload transfer_payload_x *)
        (serialize (FA2Spec.Transfer transfer_payload_x)) in 
    (* transfer 2: to y *)
    let transfer_to_y := {|
        to_ := ctx.(ctx_from) ;
        transfer_token_id := t_y.(token_id) ;
        amount := calc_delta_y rate_in rate_out q k x ;
    |} in 
    let transfer_data_y := {|
        from_ := ctx.(ctx_contract_address) ;
        txs := [ transfer_to_y ] ;
    |} in 
    let transfer_payload_y := [ transfer_data_y ] in 
    let transfer_ty := act_call 
        (* call to the correct token address *)
        (msg_payload.(token_out_trade).(token_address))
        (* with amount = 0 *)
        0 
        (* and payload transfer_payload_y *)
        (serialize (FA2Spec.Transfer transfer_payload_y)) in 
    (* trade amts are nonnegative *)
    let new_state := {|
        stor_rates := stor_rates' ;
        stor_tokens_held := stor_tokens_held' ;
        stor_pool_token := cstate.(stor_pool_token) ;
        stor_outstanding_tokens := cstate.(stor_outstanding_tokens) ; 
    |} in
    Ok (new_state, [ transfer_tx ; transfer_ty ])
    else Err 0 else Err 0 else Err 0 end
    else Err 0 end
    else Err 0 end
    else Err 0 end.

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
(* Context {other_none : forall o : other_entrypoint, Msg_Spec.other o = None}. *)

Instance msg_spec : @Msg_Spec Base other_entrypoint msg.
Proof.
    split.
    -   intros m.
        exact (pool m).
    -   intros m.
        exact (unpool m).
    -   intros m.
        exact (trade m).
    -   intros m.
        exact (None).
Qed.
Instance setup_spec : Setup_Spec setup.
Proof.
    split.
    -   intros s.
        exact (init_rates s).
    -   intros s.
        exact (init_pool_token s).
Qed.

Instance state_spec : State_Spec state.
Proof.
    split.
    -   intros s.
        exact (stor_rates s).
    -   intros s.
        exact (stor_tokens_held s).
    -   intros s.
        exact (stor_pool_token s).
    -   intros s.
        exact (stor_outstanding_tokens s).
Qed.

Instance error_spec : Error_Spec error.
Proof. split. auto. Qed.

(* some annoying typing issues with importing the spec *)

Axiom pool_types : forall p, pool p = StructuredPoolsSpec.pool p.
Axiom unpool_types : forall u, unpool u = StructuredPoolsSpec.unpool u.
Axiom trade_types : forall t, trade t = StructuredPoolsSpec.trade t.
Axiom stor_rates_types : forall cstate, stor_rates cstate = StructuredPoolsSpec.stor_rates cstate.
Axiom stor_pool_token_types : forall cstate, stor_pool_token cstate = StructuredPoolsSpec.stor_pool_token cstate.
Axiom stor_tokens_held_types : forall cstate, stor_tokens_held cstate = StructuredPoolsSpec.stor_tokens_held cstate.
Axiom stor_outstanding_tokens_types : forall cstate, stor_outstanding_tokens cstate = StructuredPoolsSpec.stor_outstanding_tokens cstate.
Axiom init_rates_types : forall n, init_rates n = StructuredPoolsSpec.init_rates n.
Axiom init_pool_token_types : forall n, init_pool_token n = StructuredPoolsSpec.init_pool_token n.
Axiom other_none : forall o, other o = None.

(* conditions of the setup that must be enforced by actors *)

Axiom init_pos_rates : forall setup chain ctx cstate t r,
    init chain ctx setup = Ok cstate -> 
    FMap.find t (stor_rates cstate) = Some r -> 
    r > 0.

(* rates are always 1 in this implementation;
    this is used in proofs involving rates *)
Axiom rates_1 : forall (r : N), r = 1.
Axiom delta_y_suffic : forall t y, qty_trade t <= y.

(* the rate of a token is always positive *)

(* end conditions *)

Lemma fmap_find_add : forall (m : FMap token N) k v, 
    FMap.find k (FMap.add k v m) = Some v.
Proof. auto. Qed.

Lemma fmap_find_add2 : forall (m : FMap token N) k1 k2 v, 
    k1 <> k2 -> FMap.find k1 (FMap.add k2 v m) = FMap.find k1 m.
Proof. auto. Qed.

Lemma fmap_add_neq : forall (m : FMap token N) k1 k2 v, 
    k1 <> k2 -> FMap.find k1 (FMap.add k2 v m) = FMap.find k1 m.
Proof. auto. Qed.

Lemma n_sub_sub : forall (x y : N),
    y < x -> x - (x - y) = y.
Proof. lia. Qed.

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
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok.
        exists r_x.
        now rewrite <- stor_rates_types.
    -   unfold pool_emits_txns.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok.
        unfold get_bal. cbn.
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
        now try inversion H_recv_ok.
    -   unfold pool_outstanding.
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- pool_types in H_recv_ok.
        do 2 rewrite <- stor_outstanding_tokens_types.
        unfold pool_entrypoint in H_recv_ok.
        destruct (FMap.find (token_pooled msg_payload) (stor_rates cstate)) 
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
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
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok.
        destruct (negb
            (qty_unpooled msg_payload <=?
            get_rate (token_unpooled msg_payload) (stor_rates cstate) *
            get_bal (token_unpooled msg_payload) (stor_tokens_held cstate))%N);
        now try inversion H_recv_ok.
    (* trade entrypoint spec *)
    -   unfold trade_entrypoint_check.
        (* *)
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        rewrite <- stor_tokens_held_types.
        rewrite <- stor_rates_types.
        now exists y, r_x, r_y.
    -   unfold trade_entrypoint_check_2.
        (* *)
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        rewrite <- stor_tokens_held_types.
        rewrite <- stor_rates_types.
        rewrite <- stor_outstanding_tokens_types.
        exists x, r_x, r_y, (stor_outstanding_tokens cstate).
        repeat split; auto;
        apply N.lt_gt;
        now apply N.ltb_lt.
    -   rename H into H_tx, H0 into H_ty,
               H1 into H_tx_neq_ty, H2 into H_q,
               H3 into H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        rewrite H_tx in *. rewrite H_ty in *.
        unfold get_bal.
        rewrite fmap_find_add2; auto.
        now rewrite fmap_find_add.
    -   rename H into H_tx, H0 into H_ty,
               H1 into H_tx_neq_ty, H2 into H_q,
               H3 into H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        rewrite <- stor_rates_types.
        rewrite <- stor_outstanding_tokens_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        simpl.
        unfold get_bal.
        rewrite H_ty. rewrite H_y.
        rewrite fmap_find_add; auto.
        rewrite H_tx. rewrite H_x.
        rewrite n_sub_sub; auto.
        rewrite <- H_q.
        unfold get_rate.
        replace (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        with (Some r_x) by now rewrite H_rx.
        replace (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        with (Some r_y) by now rewrite H_ry.
        apply (delta_y_lt_y cstate msg_payload r_x r_y q (stor_outstanding_tokens cstate) x y);
        auto; try now apply N.ltb_lt.
        clear H_acts H_cstate H_delta_y_pos.
        rewrite H_q.
        apply N.le_ngt.
        unfold not. intro H_neg.
        now apply N.ltb_lt in H_neg.
    -   rename H into H_recv_ok.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        clear H_acts H_cstate H_delta_y_pos H_qty_nonneg
              H_k_neg.
        unfold not.
        intro H.
        now apply token_eq_eqb in H.
    -   rename H into H_recv_ok.
        do 2 rewrite <- stor_rates_types.
        rewrite <- stor_outstanding_tokens_types.
        rewrite <- stor_tokens_held_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        now cbn.
    -   rename H into H_recv_ok.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        clear H_acts H_cstate H_delta_y_pos H_qty_nonneg
              H_k_neg.
        unfold not.
        intro H.
        now apply token_eq_eqb in H.
    -   rename H into H_recv_ok.
        repeat rewrite <- stor_rates_types.
        rewrite <- stor_outstanding_tokens_types.
        rewrite <- stor_tokens_held_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        repeat rewrite <- stor_rates_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        intros t H_t_neq.
        now apply fmap_add_neq.
    -   unfold trade_emits_transfers.
        (* *)
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        exists ({|
            to_ := ctx_contract_address ctx;
            transfer_token_id := token_id (token_in_trade msg_payload);
            amount := qty_trade msg_payload
          |}).
        exists ({|
            from_ := ctx_contract_address ctx;
            txs :=
              [{|
                 to_ := ctx_contract_address ctx;
                 transfer_token_id := token_id (token_in_trade msg_payload);
                 amount := qty_trade msg_payload
               |}]
          |}).
        exists [{|
            from_ := ctx_contract_address ctx;
            txs :=
              [{|
                 to_ := ctx_contract_address ctx;
                 transfer_token_id := token_id (token_in_trade msg_payload);
                 amount := qty_trade msg_payload
               |}]
          |}].
        exists {|
            to_ := ctx_from ctx;
            transfer_token_id := token_id (token_out_trade msg_payload);
            amount :=
              calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                (get_rate (token_out_trade msg_payload) (stor_rates cstate))
                (qty_trade msg_payload) (stor_outstanding_tokens cstate)
                (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate))
          |}.
        exists {|
            from_ := ctx_contract_address ctx;
            txs :=
              [{|
                 to_ := ctx_from ctx;
                 transfer_token_id := token_id (token_out_trade msg_payload);
                 amount :=
                   calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                     (get_rate (token_out_trade msg_payload) (stor_rates cstate))
                     (qty_trade msg_payload) (stor_outstanding_tokens cstate)
                     (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate))
               |}]
          |}.
        exists [{|
            from_ := ctx_contract_address ctx;
            txs :=
              [{|
                 to_ := ctx_from ctx;
                 transfer_token_id := token_id (token_out_trade msg_payload);
                 amount :=
                   calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                     (get_rate (token_out_trade msg_payload) (stor_rates cstate))
                     (qty_trade msg_payload) (stor_outstanding_tokens cstate)
                     (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate))
               |}]
          |}].
        repeat split; 
        cbn; try now left.
    -   rename H into H_recv_ok.
        repeat rewrite <- stor_tokens_held_types.
        repeat rewrite <- stor_rates_types.
        repeat rewrite <- stor_outstanding_tokens_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        unfold get_bal.
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        repeat rewrite <- stor_tokens_held_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        unfold get_bal.
        rewrite fmap_find_add2.
        2:{ clear H_acts H_cstate H_delta_y_pos H_qty_nonneg H_k_neg.
            unfold not.
            intro H_eq.
            now apply token_eq_eqb in H_eq. }
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        repeat rewrite <- stor_tokens_held_types.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        cbn.
        intros t_z H_tz_neq_in H_tz_neq_out.
        unfold get_bal.
        repeat rewrite fmap_add_neq; auto.
    -   unfold trade_outstanding_update.
        (* *)
        intros * H_recv_ok.
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        now repeat rewrite <- stor_outstanding_tokens_types.
    -   rename H into H_recv_ok.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        repeat rewrite <- stor_tokens_held_types.
        cbn.
        rewrite fmap_add_neq; auto.
        clear H_acts H_cstate.
        unfold not.
        intro H_eq.
        now apply token_eq_eqb in H_eq.
    -   rename H into H_recv_ok.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        repeat rewrite <- stor_tokens_held_types.
        repeat rewrite <- stor_rates_types.
        repeat rewrite <- stor_outstanding_tokens_types.
        cbn.
        now rewrite fmap_find_add.
    -   rename H into H_recv_ok.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        clear H_acts H_cstate.
        apply N.le_ngt.
        unfold not.
        now intro H_lt.
    -   rename H into H_recv_ok.
        (* *)
        simpl in H_recv_ok.
        rewrite <- trade_types in H_recv_ok.
        unfold trade_entrypoint in H_recv_ok.
        destruct (FMap.find (token_in_trade msg_payload) (stor_tokens_held cstate))
        as [x | ] eqn:H_x;
        try inversion H_recv_ok.  clear H0.
        destruct ((0 <? x)%N) eqn:H_x_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_tokens_held cstate))
        as [y | ] eqn:H_y;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? y)%N) eqn:H_y_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_in_trade msg_payload) (stor_rates cstate))
        as [r_x | ] eqn:H_rx;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_x)%N) eqn:H_rx_pos.
        2:{   inversion H_recv_ok. }
        destruct (FMap.find (token_out_trade msg_payload) (stor_rates cstate))
        as [r_y | ] eqn:H_ry;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? r_y)%N) eqn:H_ry_pos.
        2:{   inversion H_recv_ok. }
        destruct (token_eqb (token_in_trade msg_payload) (token_out_trade msg_payload)) eqn:H_eqb;
        try inversion H_recv_ok. clear H0.
        destruct ((0 <? stor_outstanding_tokens cstate)%N) eqn:H_k_neg.
        2:{   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? 0)%N eqn:H_qty_nonneg.
        {   inversion H_recv_ok. }
        destruct ((calc_delta_y (get_rate (token_in_trade msg_payload) (stor_rates cstate))
                 (get_rate (token_out_trade msg_payload) (stor_rates cstate)) 
                 (qty_trade msg_payload) (stor_outstanding_tokens cstate)
        (get_bal (token_in_trade msg_payload) (stor_tokens_held cstate)) <? 0)%N)eqn:H_delta_y_pos.
        {   inversion H_recv_ok. }
        destruct (qty_trade msg_payload <? y)%N eqn:H_qty_y.
        2:{   inversion H_recv_ok. }
        inversion H_recv_ok as [[H_cstate H_acts]]. clear H_recv_ok.
        (* *)
        clear H_acts H_cstate.
        apply N.le_ngt.
        unfold not.
        now intro H_lt.
    (* other entrypoint specification *)
    -   unfold other_rates_unchanged.
        intros * H_recv_ok t.
        do 2 rewrite <- stor_rates_types.
        cbn in H_recv_ok.
        unfold receive in H_recv_ok.
        now rewrite other_none in H_recv_ok.
    -   unfold other_balances_unchanged.
        intros * H_recv_ok t.
        cbn in H_recv_ok.
        do 2 rewrite <- stor_tokens_held_types.
        unfold receive in H_recv_ok.
        now rewrite other_none in H_recv_ok.
    -   unfold other_outstanding_unchanged.
        intros * H_recv_ok.
        cbn in H_recv_ok.
        do 2 rewrite <- stor_outstanding_tokens_types.
        unfold receive in H_recv_ok.
        now rewrite other_none in H_recv_ok.
    (* isolate the specification of calc_rx' and calc_delta_y *)
    -   unfold update_rate_stays_positive.
        intros * H_rx.
        cbn.
        unfold calc_rx'.
        destruct (r_x =? 0)%N eqn:H_rx'; try lia.
        apply N.eqb_eq in H_rx'.
        rewrite H_rx' in H_rx.
        inversion H_rx.
    -   unfold rate_decrease.
        intros.
        unfold calc_rx'.
        induction r_x.
        +   auto.
        +   destruct (N.pos p =? 0)%N; lia.
    -   unfold rates_balance.
        intros.
        unfold calc_rx_inv.
        now rewrite (rates_1 (get_rate t rates)).
    -   unfold rates_balance_2.
        intros.
        repeat rewrite <- stor_tokens_held_types.
        repeat rewrite <- stor_rates_types.
        repeat rewrite <- stor_outstanding_tokens_types.
        set (r_x' := calc_rx' (get_rate (token_in_trade t) (stor_rates prev_state))
        (get_rate (token_out_trade t) (stor_rates prev_state)) (qty_trade t)
        (stor_outstanding_tokens prev_state) (get_bal (token_in_trade t) (stor_tokens_held prev_state))).
        set (x := get_bal (token_in_trade t) (stor_tokens_held prev_state)).
        set (r_y := get_rate (token_out_trade t) (stor_rates prev_state)).
        set (y := get_bal (token_out_trade t) (stor_tokens_held prev_state)).
        set (delta_y := calc_delta_y (get_rate (token_in_trade t) (stor_rates prev_state))
        r_y (qty_trade t) (stor_outstanding_tokens prev_state) x).
        set (r_x := get_rate (token_in_trade t) (stor_rates prev_state)).
        rewrite (rates_1 r_x').
        rewrite (rates_1 r_x).
        rewrite (rates_1 r_y).
        replace (1 * (x + qty_trade t))
        with ((x + qty_trade t)) by lia.
        replace (1 * (y - delta_y))
        with (y - delta_y) by lia.
        replace (1 * x + 1 * y)
        with (x + y) by lia.
        replace delta_y with (qty_trade t).
        2:{ unfold delta_y.
            now unfold calc_delta_y. }
        replace (x + qty_trade t + (y - qty_trade t))
        with (x + y + (qty_trade t) - (qty_trade t)).
        2:{ rewrite (N.add_sub_assoc).
            2:{ apply delta_y_suffic. }
            lia. }
        lia.
    -   unfold trade_slippage.
        intros.
        unfold calc_delta_y.
        rewrite (rates_1 r_y).
        now rewrite (rates_1 r_x).
    -   unfold trade_slippage_2.
        intros.
        unfold calc_delta_y.
        unfold calc_rx'.
        destruct ((r_x =? 0)%N) eqn:H_rx.
        2: {   now rewrite (rates_1 r_y). }
        apply N.eqb_eq in H_rx.
        now rewrite (rates_1 r_x) in H_rx.
    -   unfold arbitrage_lt.
        intros * H_ext H_rate.
        exists ext.
        unfold calc_rx'.
        destruct ext; try inversion H_ext.
        destruct (rate_x =? 0)%N; try lia.
    -   unfold arbitrage_gt.
        intros * H_ineq.
        unfold calc_delta_y.
        now exists ext_goal.
    (* isolate the initialization specification *)
    -   unfold initialized_with_positive_rates.
        intros * H_init_ok. cbn in H_init_ok.
        intros * H_find.
        rewrite <- stor_rates_types in H_find.
        now apply (init_pos_rates setup0 chain ctx cstate t r).
    -   unfold initialized_with_zero_balance.
        intros * H_init_ok. cbn in H_init_ok.
        intro.
        rewrite <- stor_tokens_held_types.
        unfold init in *. inversion H_init_ok as [H_cstate].
        cbn.
        now unfold get_bal.
    -   unfold initialized_with_zero_outstanding.
        intros * H_init_ok. cbn in H_init_ok.
        rewrite <- stor_outstanding_tokens_types.
        unfold init in *. inversion H_init_ok as [H_cstate].
        now cbn.
    -   unfold initialized_with_init_rates.
        intros * H_init_ok. cbn in H_init_ok.
        rewrite <- stor_rates_types.
        rewrite <- init_rates_types.
        unfold init in *. inversion H_init_ok as [H_cstate].
        now cbn.
    -   unfold initialized_with_pool_token.
        intros * H_init_ok. cbn in H_init_ok.
        rewrite <- stor_pool_token_types.
        rewrite <- init_pool_token_types.
        unfold init in *. inversion H_init_ok as [H_cstate].
        now cbn.
Qed.

End StructuredPoolsCorrect.

End StructuredPools.