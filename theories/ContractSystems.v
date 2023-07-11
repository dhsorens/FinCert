(* Systems of Contracts *)
From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Sets.Ensembles.
From Coq Require Import ZArith.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Permutation.
From Coq Require Import FunctionalExtensionality.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From FinCert.Meta Require Import ContractMorphisms.

Import ListNotations.

(** Notation for a system of contracts, encoded as graphs, inspired by Milner's bigraphs *)

Section ContractSystems.
Context {Base : ChainBase}.

(** First the node type *)
(** The fundamental building block of a system: a contract and its address *)
Section GeneralizedContract.

Record GeneralizedContract
      (Setup Msg State Error : Type)
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error} :=
  build_gc_long {
    gc_caddr : Address ;
    gc_c : Contract Setup Msg State Error ;
  }.

Definition gc_caddr' 
    {Setup Msg State Error : Type}
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    `{Serializable Error}
    (gc : GeneralizedContract Setup Msg State Error) := 
    gc_caddr Setup Msg State Error gc.

Definition gc_c' 
    {Setup Msg State Error : Type}
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    `{Serializable Error}
    (gc : GeneralizedContract Setup Msg State Error) := 
    gc_c Setup Msg State Error gc.

Definition build_gc 
    {Setup Msg State Error : Type}
    `{ser_set : Serializable Setup}
    `{ser_msg : Serializable Msg}
    `{ser_st : Serializable State}
    `{ser_err : Serializable Error}
    (caddr : Address)
    (C : Contract Setup Msg State Error) := 
    build_gc_long Setup Msg State Error ser_set ser_msg ser_st ser_err caddr C.

End GeneralizedContract.


(** The Place Graph *)
Section PlaceGraph.

(* an inductive definition of trees *)
Section NTree.

Inductive ntree (T : Type) : Type :=
| Node : T -> list (ntree T) -> ntree T.

(** Utils *)
Fixpoint replace_at_index {T : Type} (n : nat) (new_elem : T) (l : list T) : list T :=
  match l, n with
  | nil, _ => nil
  | _ :: tl, 0 => new_elem :: tl
  | hd :: tl, S n' => hd :: replace_at_index n' new_elem tl
  end.

(* Update a tree at a given index, which can be at a node or a leaf *)
Fixpoint update_ntree_at_index {T : Type} (tree : ntree T) (value : T) (leaf_index : list nat) : ntree T :=
  match tree, leaf_index with
  | Node _ v children, nil => Node T value children (* Reached the desired leaf *)
  | Node _ v children, i :: is =>
      match List.nth_error children i with
      | Some child => Node T v (replace_at_index i (update_ntree_at_index child value is) children)
      | None => tree (* Invalid leaf index *)
      end
  end.

(* Merge semantics: add a tree to a given leaf *)
Fixpoint add_tree_at_leaf {T} (orig append : ntree T) (leaf_index : list nat) : ntree T :=
    match orig, leaf_index with
    | Node _ v children, nil => orig (* Must add only at a leaf *)
    | Node _ v children, i :: is =>
        match List.nth_error children i with
        | Some child => Node T v (replace_at_index i (add_tree_at_leaf child append is) children)
        | None => orig (* Invalid leaf index *)
        end
    end.

Fixpoint ntree_find_node {T} (leaf_index : list nat) (tree : ntree T) : option T :=
    match tree, leaf_index with 
    | Node _ v children, nil => Some v (* Reached the desired node *)
    | Node _ v children, i :: is =>
        match List.nth_error children i with
        | Some child => ntree_find_node is child (* Iterate *)
        | None => None (* Invalid leaf index *)
        end
    end.

(* Definition empty_ntree {T} := Leaf T. *)

Definition singleton_ntree {T} (t : T) := Node T t nil.

Definition in_ntree {T} (t : T) (tree : ntree T) : Prop := 
    exists leaf_index, ntree_find_node leaf_index tree = Some t.

Definition search_ntree {T} (t : T) (tree : ntree T) : bool.
Admitted.

(* Given an accumulating function and a starting point, iterate over the tree *)
Fixpoint ntree_accum {T} (tree : ntree T) (accum : T -> T -> T) (t : T) : T :=
    match tree with 
    | Node _ v children => 
        List.fold_left 
        (fun (t' : T) (child : ntree T) => accum (ntree_accum child accum t) t')
        children
        (accum v t)
    end.

(** Functoriality *)
Fixpoint ntree_funct {T T'} (f : T -> T') (tree : ntree T) : ntree T' := 
    match tree with 
    | Node _ v children => 
        Node T' (f v) (List.map (fun child => ntree_funct f child) children)
    end.

(* TODO Will need to make own induction principle it looks like 
Lemma ntree_find_funct {T T'} (f : T -> T') (index : list nat) (tree : ntree T) : 
    ntree_find_node index (ntree_funct f tree) = 
    option_map f (ntree_find_node index tree).
Proof.
    destruct tree, index; auto.
    unfold ntree_find_node.
    simpl.
    rewrite nth_error_map.
    induction (nth_error l n); auto.
    cbn.
Admitted.

Lemma ntree_update_funct {T T'} (f : T -> T') index t tree : 
    update_ntree_at_index (ntree_funct f tree) (f t) index = 
    ntree_funct f (update_ntree_at_index tree t index).
Admitted.

Lemma in_ntree_funct {T T'} (f : T -> T') t tree :
    in_ntree t tree -> in_ntree (f t) (ntree_funct f tree).
Proof.
    intro in_tree.
    destruct in_tree as [index is_in].
    unfold in_ntree.
    exists index.
    rewrite ntree_find_funct.
    now rewrite is_in.
Qed.
*)

(** Permutations *)
Inductive NTree_Permutation {T} : ntree T -> ntree T -> Prop := 
| perm_swap v children1 children2 :
    Permutation children1 children2 ->
    NTree_Permutation (Node T v children1) (Node T v children2)
| perm_trans ntree1 ntree2 ntree3 : 
    NTree_Permutation ntree1 ntree2 ->
    NTree_Permutation ntree2 ntree3 ->
    NTree_Permutation ntree1 ntree3.

Lemma ntree_permutation_comm {T} (ntree1 ntree2 : ntree T) : 
    NTree_Permutation ntree1 ntree2 -> 
    NTree_Permutation ntree2 ntree1.
Proof.
    intro perm.
    induction perm.
    -   apply Permutation_sym in H.
        now apply perm_swap.
    -   apply (perm_trans ntree3 ntree2 ntree1 IHperm2 IHperm1).
Qed.

(*
Lemma intree_permutation_in {T}
    t (ntree1 ntree2 : ntree T) :
    NTree_Permutation ntree1 ntree2 ->
    (in_ntree t ntree1 <-> in_ntree t ntree2).
Proof.
    intro perm.
    induction perm; auto;
    split.
    (* -> *)
    -   intro H_in1.
        unfold in_ntree in *.
        destruct H_in1 as [place found].
        destruct place eqn:H_place.
        +   cbn in found.
            inversion found.
            now exists nil.
        +   destruct H eqn:H_perm.
            cbn in found.
            *   destruct n; cbn in found; inversion found.
            *   admit.      
            *   admit.
            *   admit.
    (* <- *)
    -   admit.
Admitted.
*)

End NTree.

End PlaceGraph.

(** A system of contracts is a (list of) place graphs, 
    endowed automatically with the link graph structure *)
Section SystemDefinition.

(* A system of contracts is presented by its place graph;
    it inherits the link graph automatically *)
Definition ContractSystem
    (Setup Msg State : Type)
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State} :=
    ntree (GeneralizedContract Setup Msg State nat).

(* An iterative construction of a system of contracts *)
Section GC_Iter.

Section GC_Sum.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2}.

Definition c_to_c_sum_l (C : Contract Setup1 Msg1 State1 nat) :
    Contract (Setup1 + Setup2) (Msg1 + Msg2) (State1 + State2) nat.
Proof.
    destruct C as [init1 recv1].
    apply build_contract.
    (* init *)
    -   exact (fun c ctx s' =>
            match s' with
            | inl s =>
                match init1 c ctx s with
                | Ok st => Ok (inl st)
                | Err e => Err e
                end
            | inr _ => Err 0
            end).
    (* receive *)
    -   exact (fun c ctx st' op_msg' =>
            match st', op_msg' with 
            | inl st, Some (inl msg) => 
                match recv1 c ctx st (Some msg) with 
                | Ok (new_st, acts) => Ok (inl new_st, acts)
                | Err e => Err e
                end
            | inl st, None => 
                match recv1 c ctx st None with 
                | Ok (new_st, acts) => Ok (inl new_st, acts)
                | Err e => Err e
                end
            | _ , _ => Err 0
            end).
Defined.

Definition gc_to_gc_sum_l (sys : GeneralizedContract Setup1 Msg1 State1 nat) :
    GeneralizedContract (Setup1 + Setup2) (Msg1 + Msg2) (State1 + State2) nat := 
    {| gc_caddr := (gc_caddr' sys) ; 
       gc_c := c_to_c_sum_l (gc_c' sys) ; |}.

Definition c_to_c_sum_r (C : Contract Setup1 Msg1 State1 nat) :
    Contract (Setup2 + Setup1) (Msg2 + Msg1) (State2 + State1) nat.
Proof.
    destruct C as [init1 recv1].
    apply build_contract.
    (* init *)
    -   exact (fun c ctx s' => 
            match s' with 
            | inr s => 
                match init1 c ctx s with 
                | Ok st => Ok (inr st)
                | Err e => Err e
                end
            | inl _ => Err 0
            end).
    (* receive *)
    -   exact (fun c ctx st' op_msg' =>
            match st', op_msg' with 
            | inr st, Some (inr msg) => 
                match recv1 c ctx st (Some msg) with 
                | Ok (new_st, acts) => Ok (inr new_st, acts)
                | Err e => Err e
                end
            | inr st, None => 
                match recv1 c ctx st None with 
                | Ok (new_st, acts) => Ok (inr new_st, acts)
                | Err e => Err e
                end
            | _ , _ => Err 0
            end).
Defined.

Definition gc_to_gc_sum_r (sys : GeneralizedContract Setup1 Msg1 State1 nat) :
    GeneralizedContract (Setup2 + Setup1) (Msg2 + Msg1) (State2 + State1) nat := 
    {| gc_caddr := (gc_caddr' sys) ; 
       gc_c := c_to_c_sum_r (gc_c' sys) ; |}.

End GC_Sum.


Context `{Serializable Setup1} `{Serializable Msg1} 
        `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} 
        `{Serializable State2} `{Serializable Error2}.

Definition singleton_sys 
    `{Serializable Setup} `{Serializable Msg} `{Serializable State}
    (gc : GeneralizedContract Setup Msg State nat) 
    : ContractSystem Setup Msg State := 
    singleton_ntree gc.

Definition build_system_iter
    (sys : ContractSystem Setup1 Msg1 State1)
    (leaf_index : list nat)
    (G2 : GeneralizedContract Setup2 Msg2 State2 nat)
    : ContractSystem (Setup1 + Setup2) (Msg1 + Msg2) (State1 + State2) :=
        add_tree_at_leaf
        (ntree_funct gc_to_gc_sum_l sys)
        (singleton_sys (gc_to_gc_sum_r (build_gc (gc_caddr' G2) (gc_c' G2))))
        leaf_index.

(* For convenience, to nest one contract inside another *)
Definition nest 
    (outer : GeneralizedContract Setup1 Msg1 State1 nat) 
    (inner : GeneralizedContract Setup2 Msg2 State2 nat)
    : ContractSystem (Setup1 + Setup2) (Msg1 + Msg2) (State1 + State2) :=
    build_system_iter
        (singleton_sys outer)
        [0]
        inner.

End GC_Iter.


(** A system is defined by its collective state and interface,
    from which we can get a system `receive` function *)
Section SystemInterface.

(** System state *)
Definition SystemState (State : Type) : Type := ntree (option State).

(** System interface *)
Record SystemMsg (Msg : Type) `{Serializable Msg} := {
    sm_msg : option Msg ;
    sm_place : list nat ; (* the index of *which* contract gets called *)
}.

Definition sm_msg' `{Serializable Msg} (sm : SystemMsg Msg) := sm_msg Msg sm.
Definition sm_place' `{Serializable Msg} (sm : SystemMsg Msg) := sm_place Msg sm.

(* Move from System State to System State *)
Definition sys_receive 
    {Setup Msg State : Type}
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    (sys : ContractSystem Setup Msg State)
    (c : Chain)
    (ctx : ContractCallContext)
    (sys_st : SystemState State) (* state *)
    (sys_msg : SystemMsg Msg) (* message *) :
    result (SystemState State * list ActionBody) nat := 
    match ntree_find_node (sm_place' sys_msg) sys with 
    | Some gc => 
        match ntree_find_node (sm_place' sys_msg) sys_st with 
        | Some st_op => 
            match st_op with 
            | Some st => 
                match receive (gc_c' gc) c ctx st (sm_msg' sys_msg) with 
                | Ok (new_st, new_acts) =>
                    let new_sys_st := 
                    update_ntree_at_index sys_st (Some new_st) (sm_place' sys_msg) in
                    Ok (new_sys_st, new_acts)
                | Err e => Err e
                end
            | None => Err 0
            end
        | None => Err 0
        end
    | None => Err 0
    end.

End SystemInterface.

End SystemDefinition.


(** The Link Graph *)
Section LinkGraph.

(* the system's graph *)
Definition call_to call : option Address := 
    match call with 
    | act_transfer _ _ => None 
    | act_call caddr _ _ => Some caddr 
    | act_deploy _ _ _ => None 
    end.

(* The type of edges *)
(* Edges in the link graph are given by contract calls *)
Record LinkGraphEdges 
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (G1 : GeneralizedContract Setup1 Msg1 State1 Error1)
    (G2 : GeneralizedContract Setup2 Msg2 State2 Error2) : Type := {
    e_chain : Chain ;
    e_ctx : ContractCallContext ;
    e_prvstate : State1 ; (* prev state *)
    e_msg : option Msg1 ; (* msg *)
    e_newstate : State1 ; (* new state *)
    e_nacts : list ActionBody ;
    linking_act : ActionBody ; (* the action that links the two contracts *)
    (* there is some transaction for which G1 calls G2 *)
    e_recv_some : 
        (* this is a successful call *)
        receive (gc_c' G1) e_chain e_ctx e_prvstate e_msg = Ok (e_newstate, e_nacts) /\
        (* which emits the transaction linking_act, *)
        List.In linking_act e_nacts /\
        (* and it is a call to G2 *)
        call_to linking_act = Some (gc_caddr' G2) ;
}.

(* edges can be composed if they are sequential transactions *)
Definition edges_compose 
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
    {G1 : GeneralizedContract Setup1 Msg1 State1 Error1}
    {G2 : GeneralizedContract Setup2 Msg2 State2 Error2}
    {G3 : GeneralizedContract Setup3 Msg3 State3 Error3}
    (e1 : LinkGraphEdges G1 G2) (e2 : LinkGraphEdges G2 G3) : Prop := 
    match linking_act G1 G2 e1 with 
    | act_call _ _ msg => option_map serialize (e_msg G2 G3 e2) = Some msg
    | _ => False
    end.

End LinkGraph.


(** Contract System Utils *)
Section SystemUtils.

(* get a system state from a bstate *)
Definition sys_bstate
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    (bstate : ChainState)
    (sys : ContractSystem Setup Msg State) 
    : SystemState SerializedValue :=
    ntree_funct
    (fun (gc : GeneralizedContract Setup Msg State nat) =>
        env_contract_states bstate (gc_caddr' gc))
    sys.

Definition is_sys_state
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    (bstate : ChainState)
    (sys : ContractSystem Setup Msg State)
    (sys_state : SystemState State) : Prop :=
    forall place gc,
    ntree_find_node place sys = Some gc <->
    exists st_op,
    ntree_find_node place sys_state = Some st_op /\
    env_contract_states bstate (gc_caddr' gc) = option_map serialize st_op.

(* a system is deployed *)
Definition sys_deployed bstate
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    (sys : ContractSystem Setup Msg Setup) : Prop :=
    forall G,
    in_ntree G sys ->
    env_contracts bstate (gc_caddr' G) = Some (gc_c' G : WeakContract).

(* the notion of the initial state of a system *)
Definition is_genesis_state 
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    `{sys_err : Serializable Error}
    (C : Contract Setup Msg State Error) init_cstate : Prop := 
    exists init_chain init_ctx init_setup, 
    init C init_chain init_ctx init_setup = Ok init_cstate.

(* a better version of this perhaps? *)
Definition is_genesis_gstate_sys 
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    (sys : ContractSystem Setup Msg State) gstate : Prop :=
    forall place,
    ((exists G, ntree_find_node place sys = Some G) <->
     (exists st, ntree_find_node place gstate = Some (Some st))) /\
    (forall place G st, 
        ntree_find_node place sys = Some G ->
        ntree_find_node place gstate = Some (Some st) ->
        is_genesis_state (gc_c' G) st).

(* some propositions relating to system morphisms *)
Definition sys_genesis_prop
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    (sys1 : ContractSystem Setup1 Msg1 State1)
    (sys2 : ContractSystem Setup2 Msg2 State2)
    (gstate_morph : SystemState State1 -> SystemState State2) : Prop :=
    forall gstate,
        is_genesis_gstate_sys sys1 gstate ->
        is_genesis_gstate_sys sys2 (gstate_morph gstate).

Definition sys_coherence_prop
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    (sys1 : ContractSystem Setup1 Msg1 State1)
    (sys2 : ContractSystem Setup2 Msg2 State2)
    (gstate_morph : SystemState State1 -> SystemState State2)
    (gmsg_morph : SystemMsg Msg1 -> SystemMsg Msg2)
    (gerror_morph : nat -> nat) : Prop :=
    forall c ctx gst gmsg,
        result_functor (fun '(gst, l) => (gstate_morph gst, l)) gerror_morph
            (sys_receive sys1 c ctx gst gmsg) =
        sys_receive sys2 c ctx (gstate_morph gst) (gmsg_morph gmsg).

End SystemUtils.


(** Morphisms, including isomorphisms, of contract systems *)
Section SystemMorphism.

Section MorphDefn.
Context `{Serializable Setup1}
        `{Serializable Msg1}
        `{Serializable State1}
        `{Serializable Setup2}
        `{Serializable Msg2}
        `{Serializable State2}
        `{Serializable State1Accum}
        `{Serializable State2Accum}.

(* a morphism of systems of contracts *)
Record SystemMorphism
    (sys1 : ContractSystem Setup1 Msg1 State1)
    (sys2 : ContractSystem Setup2 Msg2 State2) := 
    build_sys_morphism {
        (* component morphisms *)
        gstate_morph : SystemState State1 -> SystemState State2 ;
        gmsg_morph : SystemMsg Msg1 -> SystemMsg Msg2 ;
        gerror_morph : nat -> nat ;
        (* init coherence analogue *)
        sys_genesis : forall gstate,
            is_genesis_gstate_sys sys1 gstate ->
            is_genesis_gstate_sys sys2 (gstate_morph gstate) ;
        (* recv coherence analogue *)
        sys_coherence : forall c ctx gst gmsg,
            result_functor (fun '(gst, nacts) => (gstate_morph gst, nacts)) gerror_morph
                (sys_receive sys1 c ctx gst gmsg) =
            sys_receive sys2 c ctx (gstate_morph gst) (gmsg_morph gmsg) ;
}.

End MorphDefn.

Proposition eq_sm
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    (f g : SystemMorphism sys1 sys2) :
    gstate_morph sys1 sys2 f = gstate_morph sys1 sys2 g -> 
    gmsg_morph sys1 sys2 f = gmsg_morph sys1 sys2 g -> 
    gerror_morph sys1 sys2 f = gerror_morph sys1 sys2 g -> 
    f = g.
Proof.
    intros gst_eq gmsg_eq gerr_eq.
    destruct f, g.
    simpl in *.
    subst.
    f_equal; apply proof_irrelevance.
Qed.

Definition compose_sm
    `{ser_setup1 : Serializable Setup1}
    `{ser_msg1 : Serializable Msg1}
    `{ser_state1 : Serializable State1}
    `{ser_setup2 : Serializable Setup2}
    `{ser_msg2 : Serializable Msg2}
    `{ser_state2 : Serializable State2}
    `{ser_setup3 : Serializable Setup3}
    `{ser_msg3 : Serializable Msg3}
    `{ser_state3 : Serializable State3}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    {sys3 : ContractSystem Setup3 Msg3 State3}
    (g : SystemMorphism sys2 sys3) (f : SystemMorphism sys1 sys2) : SystemMorphism sys1 sys3.
Proof.
    destruct g, f.
    apply (build_sys_morphism sys1 sys3
        (compose gstate_morph0 gstate_morph1)
        (compose gmsg_morph0 gmsg_morph1)
        (compose gerror_morph0 gerror_morph1)).
    -   intros * is_gen.
        now apply sys_genesis0, sys_genesis1.
    -   intros.
        cbn.
        rewrite <- (sys_coherence0 c ctx (gstate_morph1 gst) (gmsg_morph1 gmsg)).
        rewrite <- (sys_coherence1 c ctx gst gmsg).
        unfold result_functor.
        now destruct (sys_receive sys1 c ctx gst gmsg).
Defined.

Proposition compose_sm_assoc
    `{ser_setup1 : Serializable Setup1}
    `{ser_msg1 : Serializable Msg1}
    `{ser_state1 : Serializable State1}
    `{ser_setup2 : Serializable Setup2}
    `{ser_msg2 : Serializable Msg2}
    `{ser_state2 : Serializable State2}
    `{ser_setup3 : Serializable Setup3}
    `{ser_msg3 : Serializable Msg3}
    `{ser_state3 : Serializable State3}
    `{ser_setup4 : Serializable Setup4}
    `{ser_msg4 : Serializable Msg4}
    `{ser_state4 : Serializable State4}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    {sys3 : ContractSystem Setup3 Msg3 State3}
    {sys4 : ContractSystem Setup4 Msg4 State4}
    (f : SystemMorphism sys1 sys2)
    (g : SystemMorphism sys2 sys3)
    (h : SystemMorphism sys3 sys4) :
    compose_sm h (compose_sm g f) =
    compose_sm (compose_sm h g) f.
Proof.
    now apply eq_sm; unfold compose_sm; destruct f, g, h.
Qed.

Definition id_sm 
    `{ser_setup : Serializable Setup}
    `{ser_msg : Serializable Msg}
    `{ser_state : Serializable State}
    (sys : ContractSystem Setup Msg State) : 
    SystemMorphism sys sys.
Proof.
    apply (build_sys_morphism sys sys id id id); auto.
    intros.
    unfold result_functor.
    simpl.
    now destruct (sys_receive sys c ctx gst gmsg).
Defined.

Definition is_iso_sm 
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1) :=
    compose_sm g f = id_sm sys1 /\
    compose_sm f g = id_sm sys2.

(** An isomorphism of contract systems *)
Definition sys_isomorphic 
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    (sys1 : ContractSystem Setup1 Msg1 State1)
    (sys2 : ContractSystem Setup2 Msg2 State2) : Prop := 
    exists (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1),
    is_iso_sm f g.

(** E.g. if two systems have isomorphic contracts at every place, 
    then they are isomorhpic systems *)
Section PlaceIsomorphic.

Record gc_iso
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    `{Serializable Error}
    (G1 G2 : GeneralizedContract Setup Msg State Error) := {
    gwc_addr_iso : gc_caddr' G1 = gc_caddr' G2 ;
    gwc_wc_iso : contracts_isomorphic (gc_c' G1) (gc_c' G2) ;
}.

Definition gc_iso_op 
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    `{Serializable Error}
    (g1 g2 : option (GeneralizedContract Setup Msg State Error)) : Prop := 
    match g1 with 
    | Some G1 => 
        match g2 with 
        | Some G2 => gc_iso G1 G2 
        | None => True 
        end 
    | None => 
        match g2 with 
        | Some G2 => False
        | None => True 
        end
    end.

(* the contracts of sys1 and sys2 are isomorphic at every place *)
Definition sys_place_isomorphic 
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    (sys1 : ContractSystem Setup Msg State)
    (sys2 : ContractSystem Setup Msg State) : Prop := 
    forall place,
    gc_iso_op (ntree_find_node place sys1) (ntree_find_node place sys2).

(* CONJECTURE <- ; we definitely want -> *)
Proposition place_iso 
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State} : forall
    (sys1 : ContractSystem Setup Msg State)
    (sys2 : ContractSystem Setup Msg State),
    sys_place_isomorphic sys1 sys2 <->
    sys_isomorphic sys1 sys2.
Admitted.

End PlaceIsomorphic.

(** Also e.g. a permutation of the place graph leads to an isomorphism *)
Section SystemPermutation.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State}.

Proposition sys_permute_iso : forall 
    (sys1 : ContractSystem Setup Msg State)
    (sys2 : ContractSystem Setup Msg State),
    NTree_Permutation sys1 sys2 ->
    sys_isomorphic sys1 sys2.
Admitted.

End SystemPermutation.

End SystemMorphism.


(** Systems of contracts can be equivalent by bisimulation *)
Section ContractSystemEquivalence.

Section Bisimulation.

(** A system's trace *)
Section SystemTrace.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State}.

Record SystemStep_single
    (sys : ContractSystem Setup Msg State)
    (st1 st2 : SystemState State) :=
    build_system_step_single {
        step_chain : Chain ;
        step_ctx : ContractCallContext ;
        step_gmsg : SystemMsg Msg ; 
        step_nacts : list ActionBody ;
        (* receive is called successfully *)
        step_recv_some : 
            sys_receive sys step_chain step_ctx st1 step_gmsg = Ok (st2, step_nacts) ;
}.

(* in a system, a step may be one or multiple steps, chained together *)
Definition SystemStep (sys : ContractSystem Setup Msg State) :=
    ChainedList (SystemState State) (SystemStep_single sys).

Definition SystemTrace (sys : ContractSystem Setup Msg State) :=
    ChainedList (SystemState State) (SystemStep sys).

End SystemTrace.


(** Morphism of system traces *)
Record SystemTraceMorphism
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    (sys1 : ContractSystem Setup1 Msg1 State1)
    (sys2 : ContractSystem Setup2 Msg2 State2) := 
    build_st_morph {
        (* state morphs, parameterized by states *)
        st_gstate_morph : SystemState State1 -> SystemState State2 ;
        (* some sort of init morph? *)
        st_genesis_fixpoint : forall (init_gstate : SystemState State1),
            is_genesis_gstate_sys sys1 init_gstate ->
            is_genesis_gstate_sys sys2 (st_gstate_morph init_gstate) ;
        (* step *)
        sys_step_morph : forall gstate1 gstate2,
            SystemStep sys1 gstate1 gstate2 -> 
            SystemStep sys2 (st_gstate_morph gstate1) (st_gstate_morph gstate2) ;
    }.

(* the identity system trace morphism *)
Definition id_stm 
    `{setup_ser : Serializable Setup}
    `{msg_ser : Serializable Msg}
    `{state_ser : Serializable State}
    (sys : ContractSystem Setup Msg State) : SystemTraceMorphism sys sys.
Proof.
    now apply (build_st_morph 
        Setup setup_ser
        Msg msg_ser
        State state_ser
        Setup setup_ser
        Msg msg_ser
        State state_ser
        sys sys id).
Defined.

(* composition *)
Definition compose_stm 
    `{ser_setup1 : Serializable Setup1}
    `{ser_msg1 : Serializable Msg1}
    `{ser_state1 : Serializable State1}
    `{ser_setup2 : Serializable Setup2}
    `{ser_msg2 : Serializable Msg2}
    `{ser_state2 : Serializable State2}
    `{ser_setup3 : Serializable Setup3}
    `{ser_msg3 : Serializable Msg3}
    `{ser_state3 : Serializable State3}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    {sys3 : ContractSystem Setup3 Msg3 State3}
    (m2 : SystemTraceMorphism sys2 sys3)
    (m1 : SystemTraceMorphism sys1 sys2) :
    SystemTraceMorphism sys1 sys3.
Proof.
    apply (build_st_morph 
        Setup1 ser_setup1
        Msg1 ser_msg1 
        State1 ser_state1
        Setup3 ser_setup3
        Msg3 ser_msg3
        State3 ser_state3
        sys1 sys3 
        (compose (st_gstate_morph sys2 sys3 m2) (st_gstate_morph sys1 sys2 m1))).
    -   intros * gen_state1.
        apply (st_genesis_fixpoint sys2 sys3 m2).
        now apply (st_genesis_fixpoint sys1 sys2 m1).
    -   intros * sys_step.
        apply (sys_step_morph sys2 sys3 m2).
        now apply (sys_step_morph sys1 sys2 m1).
Defined.

(* a strong bisimulation *)
Definition is_iso_stm
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    (m1 : SystemTraceMorphism sys1 sys2) (m2 : SystemTraceMorphism sys2 sys1) :=
    compose_stm m2 m1 = id_stm sys1 /\ 
    compose_stm m1 m2 = id_stm sys2.

Section LiftingTheorem.

(** A morphism of systems lifts to a morphism of System Traces *)
Definition sm_lift_stm
    `{ser_setup1 : Serializable Setup1}
    `{ser_msg1 : Serializable Msg1}
    `{ser_state1 : Serializable State1}
    `{ser_setup2 : Serializable Setup2}
    `{ser_msg2 : Serializable Msg2}
    `{ser_state2 : Serializable State2}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    (f : SystemMorphism sys1 sys2) : SystemTraceMorphism sys1 sys2.
Proof.
    apply (build_st_morph 
        Setup1 ser_setup1
        Msg1 ser_msg1 
        State1 ser_state1
        Setup2 ser_setup2
        Msg2 ser_msg2
        State2 ser_state2
        sys1 sys2 (gstate_morph sys1 sys2 f) (sys_genesis sys1 sys2 f)).
    intros * s_step.
    destruct f as [gstate_mph gmsg_mph gerr_mph sys_gen sys_coh].
    cbn.
    induction s_step.
    -   apply clnil.
    -   assert (SystemStep_single sys2 (gstate_mph mid) (gstate_mph to)) 
        as step_single_sys2.
        {   destruct l as [stp_chain stp_ctx stp_msg stp_nacts stp_recv].
            apply (build_system_step_single sys2 
                (gstate_mph mid) (gstate_mph to)
                stp_chain 
                stp_ctx 
                (gmsg_mph stp_msg)
                stp_nacts).
            rewrite <- sys_coh.
            now rewrite stp_recv. }
        apply (ChainedList.snoc IHs_step step_single_sys2).
Defined.

(* such that id lifts to id, ... *)
Lemma sm_lift_stm_id 
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st : Serializable State}
    {sys : ContractSystem Setup Msg State} : 
    sm_lift_stm (id_sm sys) = id_stm sys.
Proof.
    unfold sm_lift_stm, id_sm, id_stm.
    cbn.
    apply f_equal.
    apply functional_extensionality_dep.
    intro sys_state1.
    apply functional_extensionality_dep.
    intro sys_state2.
    apply functional_extensionality_dep.
    intro sys_step.
    induction sys_step; auto.
    destruct l.
    cbn.
    rewrite IHsys_step.
    do 2 apply f_equal.
    apply proof_irrelevance.
Qed.

(* ... compositions lift to compositions, ... *)
Lemma sm_lift_stm_compose 
    `{ser_setup1 : Serializable Setup1}
    `{ser_msg1 : Serializable Msg1}
    `{ser_state1 : Serializable State1}
    `{ser_setup2 : Serializable Setup2}
    `{ser_msg2 : Serializable Msg2}
    `{ser_state2 : Serializable State2}
    `{ser_setup3 : Serializable Setup3}
    `{ser_msg3 : Serializable Msg3}
    `{ser_state3 : Serializable State3}
    {sys1 : ContractSystem Setup1 Msg1 State1}
    {sys2 : ContractSystem Setup2 Msg2 State2}
    {sys3 : ContractSystem Setup3 Msg3 State3}
    (g : SystemMorphism sys2 sys3)
    (f : SystemMorphism sys1 sys2) : 
    sm_lift_stm (compose_sm g f) = 
    compose_stm (sm_lift_stm g) (sm_lift_stm f).
Proof.
    assert (st_gstate_morph sys1 sys3 (sm_lift_stm (compose_sm g f)) = 
    st_gstate_morph sys1 sys3 (compose_stm (sm_lift_stm g) (sm_lift_stm f)))
    as H_gst_eq.
    { now destruct f, g. }
    destruct f, g.
    unfold compose_stm.
    cbn in *.
    unfold sm_lift_stm.
    apply f_equal.
    apply functional_extensionality_dep.
    intro sys_state1.
    apply functional_extensionality_dep.
    intro sys_state2.
    apply functional_extensionality_dep.
    intro sys_step.
    induction sys_step; auto.
    destruct l.
    cbn.
    rewrite <- IHsys_step.
    cbn.
    do 2 apply f_equal.
    apply proof_irrelevance.
Qed.

(* ... and thus isos lift to isos. *)
Proposition sys_iso_to_st_iso 
    `{Serializable Setup1}
    `{Serializable Msg1}
    `{Serializable State1}
    `{Serializable Setup2}
    `{Serializable Msg2}
    `{Serializable State2}
    {sys1 : ContractSystem Setup1 Msg1 State1} 
    {sys2 : ContractSystem Setup2 Msg2 State2} 
    (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1) : 
    is_iso_sm f g -> is_iso_stm (sm_lift_stm f) (sm_lift_stm g).
Proof.
    intro iso_sm.
    unfold is_iso_sm, is_iso_stm in *.
    destruct iso_sm as [iso_sm_l iso_sm_r].
    split.
    -   rewrite <- sm_lift_stm_compose.
        rewrite iso_sm_l.
        now rewrite sm_lift_stm_id.
    -   rewrite <- sm_lift_stm_compose.
        rewrite iso_sm_r.
        now rewrite sm_lift_stm_id.
Qed.

End LiftingTheorem.

End Bisimulation.

End ContractSystemEquivalence.

End ContractSystems.