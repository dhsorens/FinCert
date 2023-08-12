(** Systems of contracts are encoded using ntrees so that they can be encoded as bigraphs.

A bigraph consists of:
1. a set of nodes,
2. a place graph (an n-tree), which indicates a system's spacial/nesting structure, and 
3. and a link graph, which indicates how the system interacts within itself 
    (i.e., how the processes of the system interact with each other)

Bigraphs are a universal system model, so encoding systems using ntrees can in principle
help us embed a process algebra natively into ConCert.

For now, we use an ntree as a data type in which to encode systems of contracts.

Like contracts, systems have morphisms between them.
*)

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

Section ContractSystems.
Context {Base : ChainBase}.

Section ContractBigraph.

Section LinkGraph.

Section ntree.

Inductive ntree (T : Type) : Type :=
| Node : T -> list (ntree T) -> ntree T.

Definition singleton_ntree {T} (t : T) := Node T t nil.

(* fold/traversal for ntrees *)
Fixpoint ntree_fold_left {A T}
    (f : A -> T -> A)
    (sys : ntree T)
    (a0 : A) : A := 
    match sys with 
    | Node _ t list_child_trees => 
        List.fold_left
            (fun (a0' : A) (sys' : ntree T) =>
                ntree_fold_left f sys' a0')
            list_child_trees
            (f a0 t)
    end.

(* ntree map : the functoriality of ntrees *)
Fixpoint ntree_map {T T'} (f : T -> T') (tree : ntree T) : ntree T' := 
    match tree with
    | Node _ v children => 
        Node T' (f v) (List.map (fun child => ntree_map f child) children)
    end.

Fixpoint replace_at_index {T : Type} (n : nat) (new_elem : T) (l : list T) : list T :=
  match l, n with
  | nil, _ => nil
  | _ :: tl, 0 => new_elem :: tl
  | hd :: tl, S n' => hd :: replace_at_index n' new_elem tl
  end.

Fixpoint add_tree_at_leaf {T} (orig append : ntree T) (leaf_index : list nat) : ntree T :=
    match orig, leaf_index with
    | Node _ v children, nil => Node T v (append :: children)
    | Node _ v children, i :: is =>
        match List.nth_error children i with
        | Some child => Node T v (replace_at_index i (add_tree_at_leaf child append is) children)
        | None => orig
        end
    end.

End ntree.

Definition ContractSystem
    (Setup Msg State Error : Type)
    `{sys_set : Serializable Setup}
    `{sys_msg : Serializable Msg}
    `{sys_st  : Serializable State}
    `{sys_err : Serializable Error} :=
    ntree (Contract Setup Msg State Error).

Section SystemInterface.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}.

(* system init : just initialize the root, since all contract init behaves identically *)
Definition sys_init
    (sys : ContractSystem Setup Msg State Error)
    (c : Chain)
    (ctx : ContractCallContext)
    (s : Setup) : result State Error := 
    match sys with 
    | Node _ root_contract _ => 
        init root_contract c ctx s 
    end.

(* system receive: take the message and state and run through the entire system.
    since systems are iteratively built so that a message not intended for a given contract 
    returns the identity, this targets the contract in question and leaves the rest untouched. *)
Definition sys_receive
    (sys : ContractSystem Setup Msg State Error)
    (c : Chain)
    (ctx : ContractCallContext)
    (st : State)
    (op_msg : option Msg) : result (State * list ActionBody) Error :=
    ntree_fold_left
    (fun (recv_propogate : result (State * list ActionBody) Error)
         (contr : Contract Setup Msg State Error) =>
         match recv_propogate with 
            | Ok (st0, lacts0) => 
                match receive contr c ctx st0 op_msg with 
                | Ok (st1, lacts1) => Ok (st1, lacts0 ++ lacts1)
                | Err e => Err e
                end
            | Err e => Err e
         end)
    sys
    (Ok (st, nil)).

(* thes two functions give us a contract *)
Definition sys_contract (sys : ContractSystem Setup Msg State Error) := 
    build_contract (sys_init sys) (sys_receive sys).

End SystemInterface.


Section IterativeSystemBuild.
(* the definition of a singleton system *)
Definition singleton_sys 
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) 
    : ContractSystem Setup Msg State Error := singleton_ntree C.

Section IterativeSum.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

(* an iterative add to contract systems s.t. type goals are satisfied *)

(* accepts messages on the left *)
Definition c_sum_l
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) :
    Contract (Setup1 * Setup2) (Msg1 + Msg2) (State1 * State2) (Error1 + Error2).
Proof.
    destruct C1 as [init1 recv1].
    destruct C2 as [init2 recv2].
    apply build_contract.
    (* each setup must succeed, providing the new system state *)
    -   apply (fun c ctx s' => 
            let '(s1, s2) := s' in
            match init1 c ctx s1, init2 c ctx s2 with 
            | Ok st1, Ok st2 => Ok (st1, st2)
            | Err e, _ => Err (inl e) (* the left error is first *)
            | _, Err e => Err (inr e) (* followed by the right *)
            end).
    -   apply (fun c ctx st' op_msg => 
            let '(st1, st2) := st' in
            match op_msg with 
            | Some msg => 
                match msg with 
                (* the message was intended for this contract, 
                    so we attempt to udpate the state *)
                | inl msg =>
                    match recv1 c ctx st1 (Some msg) with 
                    | Ok (new_st1, nacts) => Ok ((new_st1, st2), nacts)
                    | Err e => Err (inl e)
                    end
                (* the message was not intended for this contract, so we do nothing *)
                | inr msg => Ok (st', nil)
                end 
            | None => (* if there is no message, we call the contract with None *)
                match recv1 c ctx st1 None with 
                | Ok (new_st1, nacts) => Ok ((new_st1, st2), nacts)
                | Err e => Err (inl e)
                end
            end).
Defined.

(* same as before, but accepts messages on the right now *)
Definition c_sum_r
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) :
    Contract (Setup1 * Setup2) (Msg1 + Msg2) (State1 * State2) (Error1 + Error2).
Proof.
    destruct C1 as [init1 recv1].
    destruct C2 as [init2 recv2].
    apply build_contract.
    (* each setup must succeed, providing the new system state *)
    -   apply (fun c ctx s' =>
            let '(s1, s2) := s' in
            match init1 c ctx s1, init2 c ctx s2 with
            | Ok st1, Ok st2 => Ok (st1, st2)
            | Err e, _ => Err (inl e) (* the left error is first *)
            | _, Err e => Err (inr e) (* followed by the right *)
            end).
    -   apply (fun c ctx st' op_msg =>
            let '(st1, st2) := st' in
            match op_msg with
            | Some msg =>
                match msg with
                (* the message was not intended for this contract, so we do nothing *)
                | inl msg => Ok (st', nil)
                (* the message was intended for this contract,
                    so we attempt to udpate the state *)
                | inr msg =>
                    match recv2 c ctx st2 (Some msg) with
                    | Ok (new_st2, nacts) => Ok ((st1, new_st2), nacts)
                    | Err e => Err (inr e)
                    end
                end
            | None => (* if there is no message, we call the contract with None *)
                match recv2 c ctx st2 None with
                | Ok (new_st2, nacts) => Ok ((st1, new_st2), nacts)
                | Err e => Err (inr e)
                end
            end).
Defined.

End IterativeSum.

Section IterativeChild.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

(* add a contract as a child to a system(/nest contracts) *)
Definition sys_add_child_r
    (sys : ContractSystem Setup1 Msg1 State1 Error1)
    (C : Contract Setup2 Msg2 State2 Error2) :
    ContractSystem (Setup1 * Setup2) (Msg1 + Msg2) (State1 * State2) (Error1 + Error2) := 
    let T := (Contract (Setup1 * Setup2) (Msg1 + Msg2) (State1 * State2) (Error1 + Error2)) in 
    match sys with
    | Node _ root_contract _ =>
        match (ntree_map (fun C1 => c_sum_l C1 C) sys) with
        | Node _ root_contract' children =>
            Node T root_contract' (children ++ [Node T (c_sum_r root_contract C) nil])
        end
    end.

(* nest C1 C2 indicates that C2 is nested within C1 *)
Definition nest 
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) : 
    ContractSystem (Setup1 * Setup2) (Msg1 + Msg2) (State1 * State2) (Error1 + Error2) := 
    let T := (Contract (Setup1 * Setup2) (Msg1 + Msg2) (State1 * State2) (Error1 + Error2)) in 
    Node T (c_sum_l C1 C2) [Node T (c_sum_r C1 C2) nil].

End IterativeChild.

End IterativeSystemBuild.

End LinkGraph.

(** The place graph, a graph structure independent of the link graph on constituent contracts *)
Section PlaceGraph.

(* we leave this for future work *)

End PlaceGraph.

End ContractBigraph.

End ContractSystems.


(* A morphism of systems is the analogue to a morphism of contracts *)
Section SystemMorphisms.
Context {Base : ChainBase}.

(** First, a definition of a System Morphism, which is a function between systems *)
Section SystemMorphismDefinition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

Record SystemMorphism
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :=
    build_system_morphism {
        (* the components of a morphism *)
        sys_setup_morph : Setup1 -> Setup2 ;
        sys_msg_morph   : Msg1   -> Msg2   ;
        sys_state_morph : State1 -> State2 ;
        sys_error_morph : Error1 -> Error2 ;
        (* coherence conditions *)
        sys_init_coherence : forall c ctx s,
            result_functor sys_state_morph sys_error_morph
                (sys_init sys1 c ctx s) =
            sys_init sys2 c ctx (sys_setup_morph s) ;
        sys_recv_coherence : forall c ctx st op_msg,
            result_functor (fun '(st, l) => (sys_state_morph st, l)) sys_error_morph
                (sys_receive sys1 c ctx st op_msg) =
            sys_receive sys2 c ctx (sys_state_morph st) (option_map sys_msg_morph op_msg) ;
}.

(* a system morphism is in one-to-one correspondence with a morphism of contracts,
    when we consider a system as its own contract *)
Definition cm_to_sysm
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2)
    (f : ContractMorphism (sys_contract sys1) (sys_contract sys2)) : SystemMorphism sys1 sys2.
Proof.
    destruct f.
    apply (build_system_morphism sys1 sys2 setup_morph msg_morph state_morph error_morph
        init_coherence recv_coherence).
Defined.

Definition sysm_to_cm
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2)
    (f : SystemMorphism sys1 sys2) : ContractMorphism (sys_contract sys1) (sys_contract sys2).
Proof.
    destruct f as [sys_setup_morph sys_msg_morph sys_state_morph sys_error_morph sys_init_coh sys_recv_coh].
    apply (build_contract_morphism (sys_contract sys1) (sys_contract sys2)
        sys_setup_morph sys_msg_morph sys_state_morph sys_error_morph
        sys_init_coh sys_recv_coh).
Defined.

Lemma cm_sysm_one_to_one
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :
    compose (cm_to_sysm sys1 sys2) (sysm_to_cm sys1 sys2) = id /\
    compose (sysm_to_cm sys1 sys2) (cm_to_sysm sys1 sys2) = id.
Proof.
    split; 
    unfold sysm_to_cm, cm_to_sysm;
    apply functional_extensionality;
    intro;
    now destruct x.
Qed.

End SystemMorphismDefinition.


(* the identity system morphism *)
Section IdentitySystemMorphism.
Context `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}.

Lemma sys_init_coherence_id (sys : ContractSystem Setup Msg State Error) : 
    forall c ctx s,
    result_functor id id (sys_init sys c ctx s) = 
    sys_init sys c ctx s.
Proof. 
    intros.
    unfold result_functor.
    now destruct (sys_init sys c ctx s).
Qed.

Lemma sys_recv_coherence_id (sys : ContractSystem Setup Msg State Error) :
    forall c ctx st op_msg,
    result_functor
        (fun '(st, l) => (id st, l)) id
        (sys_receive sys c ctx st op_msg) =
    sys_receive sys c ctx (id st) (option_map id op_msg).
Proof.
    intros.
    unfold result_functor, option_map.
    cbn.
    destruct op_msg.
    -   now destruct (sys_receive sys c ctx st (Some m)); try destruct t.
    -   now destruct (sys_receive sys c ctx st None); try destruct t.
Qed.

(** The identity morphism *)
Definition id_sm (sys : ContractSystem Setup Msg State Error) : SystemMorphism sys sys := {|
        (* components *)
        sys_setup_morph := id ;
        sys_msg_morph   := id ; 
        sys_state_morph := id ; 
        sys_error_morph := id ; 
        (* coherence conditions *)
        sys_init_coherence := sys_init_coherence_id sys ; 
        sys_recv_coherence := sys_recv_coherence_id sys ;
    |}.

End IdentitySystemMorphism.


(** Equality of contract morphisms *)
Section EqualityOfSystemMorphisms.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {sys1 : ContractSystem Setup1 Msg1 State1 Error1} 
        {sys2 : ContractSystem Setup2 Msg2 State2 Error2}.

Lemma eq_sm : 
    forall (f g : SystemMorphism sys1 sys2),
    (* if the components are equal ... *)
    (sys_setup_morph sys1 sys2 f) = (sys_setup_morph sys1 sys2 g) -> 
    (sys_msg_morph   sys1 sys2 f) = (sys_msg_morph   sys1 sys2 g) -> 
    (sys_state_morph sys1 sys2 f) = (sys_state_morph sys1 sys2 g) -> 
    (sys_error_morph sys1 sys2 f) = (sys_error_morph sys1 sys2 g) -> 
    (* ... then the morphisms are equal *)
    f = g.
Proof.
    intros f g.
    destruct f, g.
    cbn.
    intros msg_eq set_eq st_eq err_eq.
    subst.
    f_equal;
    apply proof_irrelevance.
Qed.

Lemma eq_sm_rev : 
    forall (f g : SystemMorphism sys1 sys2),
    (* if the morphisms are equal ... *)
    f = g ->
    (* ... then the components are equal *)
    (sys_setup_morph sys1 sys2 f) = (sys_setup_morph sys1 sys2 g) /\
    (sys_msg_morph   sys1 sys2 f) = (sys_msg_morph   sys1 sys2 g) /\
    (sys_state_morph sys1 sys2 f) = (sys_state_morph sys1 sys2 g) /\
    (sys_error_morph sys1 sys2 f) = (sys_error_morph sys1 sys2 g).
Proof.
    intros f g fg_eq.
    now inversion fg_eq.
Qed.

Lemma eq_sm_iff :
    forall (f g : SystemMorphism sys1 sys2),
    (* the components are equal ... *)
    (sys_setup_morph sys1 sys2 f) = (sys_setup_morph sys1 sys2 g) /\
    (sys_msg_morph   sys1 sys2 f) = (sys_msg_morph   sys1 sys2 g) /\
    (sys_state_morph sys1 sys2 f) = (sys_state_morph sys1 sys2 g) /\
    (sys_error_morph sys1 sys2 f) = (sys_error_morph sys1 sys2 g) <->
    (* ... iff the morphisms are equal *)
    f = g.
Proof.
    intros.
    split.
    -   intro H_components.
        destruct H_components as [H_set [H_msg [H_st H_err]]].
        now apply eq_sm.
    -   now apply eq_sm_rev.
Qed.

End EqualityOfSystemMorphisms.


(** Composition of system morphisms *)
Section SystemMorphismComposition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        { sys1 : ContractSystem Setup1 Msg1 State1 Error1} 
        { sys2 : ContractSystem Setup2 Msg2 State2 Error2}
        { sys3 : ContractSystem Setup3 Msg3 State3 Error3}.

Lemma sys_compose_init_coh (g : SystemMorphism sys2 sys3) (f : SystemMorphism sys1 sys2) : 
    let sys_setup_morph' := (compose (sys_setup_morph sys2 sys3 g) (sys_setup_morph sys1 sys2 f)) in 
    let sys_state_morph' := (compose (sys_state_morph sys2 sys3 g) (sys_state_morph sys1 sys2 f)) in 
    let sys_error_morph' := (compose (sys_error_morph sys2 sys3 g) (sys_error_morph sys1 sys2 f)) in 
    forall c ctx s, 
        result_functor sys_state_morph' sys_error_morph'
            (sys_init sys1 c ctx s) = 
        sys_init sys3 c ctx (sys_setup_morph' s).
Proof.
    intros.
    unfold sys_setup_morph'.
    cbn.
    rewrite <- (sys_init_coherence sys2 sys3 g).
    rewrite <- (sys_init_coherence sys1 sys2 f).
    unfold result_functor.
    now destruct (sys_init sys1 c ctx s).
Qed.

Lemma sys_compose_recv_coh (g : SystemMorphism sys2 sys3) (f : SystemMorphism sys1 sys2) : 
    let sys_msg_morph'   := (compose (sys_msg_morph   sys2 sys3 g) (sys_msg_morph   sys1 sys2 f)) in 
    let sys_state_morph' := (compose (sys_state_morph sys2 sys3 g) (sys_state_morph sys1 sys2 f)) in 
    let sys_error_morph' := (compose (sys_error_morph sys2 sys3 g) (sys_error_morph sys1 sys2 f)) in 
    forall c ctx st op_msg,
        result_functor
            (fun '(st, l) => (sys_state_morph' st, l)) sys_error_morph'
            (sys_receive sys1 c ctx st op_msg) =
        sys_receive sys3 c ctx (sys_state_morph' st) (option_map sys_msg_morph' op_msg).
Proof.
    intros.
    pose proof (sys_recv_coherence sys2 sys3 g).
    pose proof (sys_recv_coherence sys1 sys2 f).
    unfold sys_state_morph', sys_msg_morph'.
    cbn.
    replace (option_map (compose (sys_msg_morph sys2 sys3 g) (sys_msg_morph sys1 sys2 f)) op_msg)
    with (option_map (sys_msg_morph sys2 sys3 g) (option_map (sys_msg_morph sys1 sys2 f) op_msg)).
    2:{ now destruct op_msg. }
    rewrite <- H11.
    rewrite <- H12.
    unfold result_functor.
    now destruct (sys_receive sys1 c ctx st op_msg).
Qed.

(** Composition *)
Definition compose_sm (g : SystemMorphism sys2 sys3) (f : SystemMorphism sys1 sys2) :
    SystemMorphism sys1 sys3 := {|
    (* the components *)
    sys_setup_morph := compose (sys_setup_morph sys2 sys3 g) (sys_setup_morph sys1 sys2 f) ;
    sys_msg_morph   := compose (sys_msg_morph   sys2 sys3 g) (sys_msg_morph   sys1 sys2 f) ;
    sys_state_morph := compose (sys_state_morph sys2 sys3 g) (sys_state_morph sys1 sys2 f) ;
    sys_error_morph := compose (sys_error_morph sys2 sys3 g) (sys_error_morph sys1 sys2 f) ;
    (* the coherence results *)
    sys_init_coherence := sys_compose_init_coh g f ;
    sys_recv_coherence := sys_compose_recv_coh g f ;
    |}.

End SystemMorphismComposition.


(** Some results about composition *)
Section SystemMorphismCompositionResults.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Setup4} `{Serializable Msg4} `{Serializable State4} `{Serializable Error4}
        {sys1 : ContractSystem Setup1 Msg1 State1 Error1}
        {sys2 : ContractSystem Setup2 Msg2 State2 Error2}
        {sys3 : ContractSystem Setup3 Msg3 State3 Error3}
        {sys4 : ContractSystem Setup4 Msg4 State4 Error4}.

(** Composition with the Identity morphism is trivial *)
Lemma compose_id_sm_left (f : SystemMorphism sys1 sys2) :
    compose_sm (id_sm sys2) f = f.
Proof. now apply eq_sm. Qed.

Lemma compose_id_sm_right (f : SystemMorphism sys1 sys2) :
    compose_sm f (id_sm sys1) = f.
Proof. now apply eq_sm. Qed.

(** Composition is associative *)
Lemma compose_sm_assoc
    (f : SystemMorphism sys1 sys2)
    (g : SystemMorphism sys2 sys3)
    (h : SystemMorphism sys3 sys4) :
    compose_sm h (compose_sm g f) =
    compose_sm (compose_sm h g) f.
Proof. now apply eq_sm. Qed.

End SystemMorphismCompositionResults.


Section SystemIsomorphisms.

(** A bisimulation of contracts, or an isomorphism of contract traces *)
Definition is_iso_sm
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    {sys1 : ContractSystem Setup1 Msg1 State1 Error1}
    {sys2 : ContractSystem Setup2 Msg2 State2 Error2}
    (m1 : SystemMorphism sys1 sys2) (m2 : SystemMorphism sys2 sys1) :=
    compose_sm m2 m1 = id_sm sys1 /\
    compose_sm m1 m2 = id_sm sys2.

(* an isomorphism predicate on contract systems, which is an equivalence relation *)
Definition systems_isomorphic
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :=
    exists (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1),
    is_iso_sm f g.

Lemma iso_sm_reflexive
    `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
    (sys : ContractSystem Setup Msg State Error) :
    systems_isomorphic sys sys.
Proof.
    exists (id_sm sys), (id_sm sys).
    unfold is_iso_sm.
    split;
    apply compose_id_sm_left.
Qed.

Lemma iso_sm_symmetric
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    (sys1 : ContractSystem Setup1 Msg1 State1 Error1)
    (sys2 : ContractSystem Setup2 Msg2 State2 Error2) :
    systems_isomorphic sys1 sys2 ->
    systems_isomorphic sys2 sys1.
Proof.
    intro sys_iso.
    destruct sys_iso as [f [f' [f_id1 f_id2]]].
    unfold systems_isomorphic, is_iso_sm.
    exists f', f.
    split.
    -   apply f_id2.
    -   apply f_id1.
Qed.

Lemma iso_sm_transitive
    `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
    `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
    `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
    {sys1 : ContractSystem Setup1 Msg1 State1 Error1}
    {sys2 : ContractSystem Setup2 Msg2 State2 Error2}
    {sys3 : ContractSystem Setup3 Msg3 State3 Error3} :
    systems_isomorphic sys1 sys2 /\ systems_isomorphic sys2 sys3 ->
    systems_isomorphic sys1 sys3.
Proof.
    intro sys_isos.
    destruct sys_isos as [[f [f' [f_id1 f_id2]]] [g [g' [g_id1 g_id2]]]].
    exists (compose_sm g f), (compose_sm f' g').
    unfold is_iso_sm.
    split.
    -   rewrite <- compose_sm_assoc.
        replace (compose_sm g' (compose_sm g f)) with (compose_sm (compose_sm g' g) f).
        2:{ now rewrite <- compose_sm_assoc. }
        rewrite g_id1.
        rewrite compose_id_sm_left.
        apply f_id1.
    -   rewrite <- compose_sm_assoc.
        replace (compose_sm f (compose_sm f' g')) with (compose_sm (compose_sm f f') g').
        2:{ now rewrite <- compose_sm_assoc. }
        rewrite f_id2.
        rewrite compose_id_sm_left.
        apply g_id2.
Qed.

End SystemIsomorphisms.

End SystemMorphisms.