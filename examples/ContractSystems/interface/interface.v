From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ChainedList.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.

From FinCert.Meta Require Import ContractMorphisms.
From FinCert.Meta Require Import ContractSystems.
From FinCert.Meta Require Import Bisimulation.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** An example of a system of contracts, where an backend contract is nested 
    with an interface contract. The tree structure would be something like:
    
        C_interface
             /
         C_backend
    
    Under the condition of a link graph specification, these contracts are 
*)

Section Interface.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* the various contract types *)
Definition setup := unit.
Inductive entrypoint := 
| incr (n : nat).
Record state := build_state { counter : nat }.
Definition error := nat.

(* for the interface *)
Definition setup_i := Address.
Inductive entrypoint_i := 
| incr_i (n : nat).
Record state_i := build_state_i { backend_address : Address }.
Definition error_i := nat.

(* for the backend *)
Definition setup_b := Address.
Inductive entrypoint_b := 
| incr_b (n : nat).
Record state_b := 
    build_state_b { interface_address : Address ; counter_backend : nat }.
Definition error_b := nat.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := 
        Derive Serializable entrypoint_rect<incr>.
    Global Instance entrypoint_i_serializable : Serializable entrypoint_i := 
        Derive Serializable entrypoint_i_rect<incr_i>.
    Global Instance entrypoint_b_serializable : Serializable entrypoint_b := 
        Derive Serializable entrypoint_b_rect<incr_b>.
    Global Instance state_serializable : Serializable state := 
        Derive Serializable state_rect<build_state>.
    Global Instance state_i_serializable : Serializable state_i := 
        Derive Serializable state_i_rect<build_state_i>.
    Global Instance state_b_serializable : Serializable state_b := 
        Derive Serializable state_b_rect<build_state_b>.
End Serialization.


Section Mono.

(* initialize with 0 in storage *)
Definition init 
    (_ : Chain)
    (_ : ContractCallContext)
    (_ : setup) : result state error := 
    Ok (build_state 0).

(* receive *)
Definition receive
    (_ : Chain)
    (_ : ContractCallContext)
    (st : state) 
    (msg : option entrypoint) : result (state * list ActionBody) error :=
    match msg with 
    | Some (incr n) => 
        Ok (build_state (counter st + n), [])
    | None => Err 0%nat
    end.

Definition contract_mono := build_contract init receive.

End Mono.


Section Modular.

Section Interface.

(* initialize with 0 in storage *)
Definition init_i
    (_ : Chain)
    (_ : ContractCallContext)
    (caddr : setup_i) : result state_i error_i := 
    Ok (build_state_i caddr).

(* receive *)
Definition receive_i
    (_ : Chain)
    (_ : ContractCallContext)
    (st : state_i) 
    (msg : option entrypoint_i) : result (state_i * list ActionBody) error_i :=
    match msg with
    | Some (incr_i n) => 
        let act_incr := act_call (backend_address st) 0 (serialize (incr_b n)) in
        Ok (st, [ act_incr ])
    | None => Err 0%nat
    end.

Definition contract_interface := build_contract init_i receive_i.

End Interface.

Section Backend.

(* initialize with 0 in storage *)
Definition init_b
    (_ : Chain)
    (_ : ContractCallContext)
    (caddr : setup_b) : result state_b error_b := 
    Ok (build_state_b caddr 0%nat).

(* receive *)
Definition receive_b
    (_ : Chain)
    (ctx : ContractCallContext)
    (st : state_b) 
    (msg : option entrypoint_b) : result (state_b * list ActionBody) error_b :=
    if address_eqb (ctx_from ctx) (interface_address st) then 
        match msg with 
        | Some (incr_b n) => 
            Ok (build_state_b (interface_address st) (counter_backend st + n), [])
        | None => Err 0%nat
        end
    else Err 0%nat.

Definition contract_backend := build_contract init_b receive_b.

End Backend.

End Modular.

(* the systems in question *)
Definition mono := singleton_sys contract_mono.
Definition modu := nest contract_interface contract_backend.


Section Bisimulation.
Context {interface_caddr backend_caddr : Address}.

Definition permissioned_ctx ctx := {|
    ctx_origin := interface_caddr ;
    ctx_from := interface_caddr ;
    ctx_contract_address := backend_caddr ;
    ctx_contract_balance := ctx_contract_balance ctx ; (* 0? ... *)
    ctx_amount := 0 ;
|}.

Section LinkGraph.

(* The link graph specification for mono *)
Axiom mono_link_graph_clnil : forall st (step : SystemStep mono st st),
    step = clnil.

Axiom mono_link_graph_step : forall st1 st2 (step : SystemStep mono st1 st2),
    exists c ctx n recv_ok,
    let step_mono := build_sys_single_step mono st1 st2
        c
        ctx
        (Some (incr n))
        nil
        recv_ok in 
    step = snoc clnil step_mono.

(* The link graph specification for modu *)
Axiom modu_link_graph_clnil : forall st (step : SystemStep modu st st),
    step = clnil.

Axiom modu_link_graph_step : forall st1 st2 (step : SystemStep modu st1 st2),
    exists c ctx n recvi_ok recvb_ok, 
    let step_interface := build_sys_single_step modu st1 st2 
        c
        ctx
        (Some (inl (incr_i n))) 
        [act_call backend_caddr 0 (serialize (incr_b n))]
        recvi_ok in 
    let step_backend := build_sys_single_step modu st1 st2
        c
        (permissioned_ctx ctx)
        (Some (inr (incr_b n)))
        nil
        recvb_ok in 
    step = snoc (snoc clnil step_interface) step_backend.

End LinkGraph.


(* the morphisms *)
(* mono -> modu *)
Definition stm_mono_mod : SystemTraceMorphism mono modu.
Proof.
    apply (build_st_morph mono modu
        (* the function between state types *)
        (fun st =>
            (build_state_i backend_caddr, build_state_b interface_caddr (counter st)))).
    -   intros st gen_mono.
        unfold is_genesis_sys_state in *.
        destruct gen_mono as [c [ctx [s init_ok]]].
        exists c, ctx, (backend_caddr, interface_caddr).
        unfold sys_init, modu, mono in *.
        cbn in *.
        unfold init in init_ok.
        now inversion init_ok.
    -   intros st1 st2 step.
        induction step; try apply clnil.
        destruct l as [c ctx op_msg nacts recv_ok].
        (* send step to *)
        destruct op_msg.
        2:{ (* none case *)
            now unfold sys_receive in *. }
        destruct e.
        (* send the single step of the monolithic contract to a *pair* of steps
            of the modular contract system *)
        assert (SingleSystemStep modu 
            ({| backend_address := backend_caddr |}, 
                {| interface_address := interface_caddr; counter_backend := counter mid |})
            ({| backend_address := backend_caddr |}, 
                {| interface_address := interface_caddr; counter_backend := counter mid |}))
        as step_interface.
        (* first the call to the interface contract, 
            which results in a call to the backend contract *)
        {   apply (build_sys_single_step modu _ _ c ctx 
                (Some (inl (incr_i n))) [act_call backend_caddr 0 (serialize (incr_b n))]).
            now unfold sys_receive in *. }
        apply (snoc (snoc IHstep step_interface)).
        clear step_interface.
        (* then the call to the backend *)
        apply (build_sys_single_step modu _ _ c (permissioned_ctx ctx)
            (Some (inr (incr_b n))) nil).
        unfold sys_receive, mono, modu in *.
        cbn in *.
        unfold receive_b.
        cbn.
        rewrite (address_eq_refl interface_caddr).
        now inversion recv_ok.
Defined.


(* modu -> mono *)
Definition stm_mod_mono : SystemTraceMorphism modu mono.
Proof.
    apply (build_st_morph modu mono
        (* the function between state types *)
        (fun '(st_i, st_b) => build_state (counter_backend st_b))).
    -   intros st gen_modu.
        unfold is_genesis_sys_state, mono, modu in *.
        destruct gen_modu as [c [ctx [s init_ok]]].
        exists c, ctx, tt.
        destruct st as [st_i st_b].
        destruct s as [s_i s_b].
        cbn in *.
        unfold sys_init, nest, init in *.
        now inversion init_ok.
    -   intros st1 st2.
        assert (forall P : (SystemStep modu st1 st2) -> Type,
        forall c ctx n recvi_ok recvb_ok,
        P (snoc (snoc clnil
            (build_sys_single_step modu st1 st1 c ctx (Some (inl (incr_i n)))
                [act_call backend_caddr 0 (serialize (incr_b n))]
                recvi_ok))
            (build_sys_single_step modu st1 st2 c (permissioned_ctx ctx)
                (Some (inr (incr_b n))) nil
                recvb_ok)) -> 
        forall (step : SystemStep modu st1 st2), P step)
        as H_modu_ind.
        { admit. }
        apply H_modu_ind.
    
        step.
        (* by the link graph, step is either clnil or a nested pair of calls *)
        induction step. 
        +   admit.
        +   

        assert Chain as c. { admit. }
        assert ContractCallContext as ctx. { admit. } 
        assert nat as n. { admit. }
        assert (sys_receive modu c ctx st1 (Some (inl (incr_i n))) = 
        Ok (st1, [act_call backend_caddr 0 (serialize (incr_b n))]))
        as recvi_ok. { admit. }
        assert (sys_receive modu c (permissioned_ctx ctx) st1 (Some (inr (incr_b n))) = Ok (st2, []))
        as recvb_ok. { admit. }
        assert (step =
        snoc
          (snoc clnil
             {|
               sys_step_chain := c;
               sys_step_ctx := ctx;
               sys_step_msg := Some (inl (incr_i n));
               sys_step_nacts := [act_call backend_caddr 0 (serialize (incr_b n))];
               sys_recv_ok_step := recvi_ok
             |})
          {|
            sys_step_chain := c;
            sys_step_ctx := permissioned_ctx ctx;
            sys_step_msg := Some (inr (incr_b n));
            sys_step_nacts := [];
            sys_recv_ok_step := recvb_ok
          |})
        as step_eq. { admit. }
        
        
        assert (exists c ctx n recvi_ok recvb_ok, 
            step = snoc (snoc clnil 
            (build_sys_single_step modu st1 st1
            c
            ctx
            (Some (inl (incr_i n))) 
            [act_call backend_caddr 0 (serialize (incr_b n))]
            recvi_ok)) 
            (build_sys_single_step modu st1 st2
            c
            (permissioned_ctx ctx)
            (Some (inr (incr_b n)))
            nil
            recvb_ok)).
        { admit. }

        apply (snoc IHstep).
        clear IHstep.
        destruct l as [c ctx op_msg nacts recv_ok].
        destruct mid as [st_i_mid st_b_mid].
        destruct to  as [st_i_to  st_b_to].
        +   admit.
Admitted.

(* assuming the semantics of the link graph are 
    satisfied, ...
    
    these systems are bisimilar. *)


End Bisimulation.

End Interface.