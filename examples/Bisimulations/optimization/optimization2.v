From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From FinCert.Meta Require Import ContractMorphisms.
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

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** An example of a contract specification via bisimulation.

    In this example 
*)


(* First example *)
Section ContractOptimization.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Axiom todo : forall {A}, A.

Definition error := N.

(*  The reference implementation contract, which serves as a specification
    to a later contract

    This contract manages owners with an array and not a linked list.
    *)
Section ContractDefinition.

    (** contract types aside from the entrypoint type *)
    Record storage_arr := { owners_arr : list N }.
    Definition setup_arr := storage_arr.
    Definition result_arr : Type := result (storage_arr * list ActionBody) error.

    (* entrypoint functions *)
    Record _add_owner_arr := { n_owner : N }.
    Definition add_owner_arr (st : storage_arr) (x : _add_owner_arr) : result_arr :=
        (* check owner isn't in the list (no duplicates allowed) *)
        if List.existsb (N.eqb x.(n_owner)) st.(owners_arr) then Err 0 else
        (* append owner *)
        Ok ({| owners_arr := x.(n_owner) :: st.(owners_arr) |}, []).

    Record _remove_owner_arr := { r_owner : N }.
    Definition remove_owner_arr (st : storage_arr) (x : _remove_owner_arr) : result_arr :=
        let new_owners := List.remove N.eq_dec x.(r_owner) st.(owners_arr) in
        Ok ({| owners_arr := new_owners |}, []).

    Record _swap_owners_arr := { owner_old_arr : N ; owner_new_arr : N }.
    Definition swap_owners_arr (st : storage_arr) (x : _swap_owners_arr) : result_arr :=
        let new_owners := List.map (fun o =>
            if N.eqb o x.(owner_old_arr) then x.(owner_new_arr) else
        if N.eqb o x.(owner_new_arr) then x.(owner_old_arr) else o) st.(owners_arr) in
        Ok ({| owners_arr := new_owners |}, []).

    Record _is_owner_arr := { i_owner : N ; ack_is : Address }.
    Definition is_owner_arr (st : storage_arr) (x : _is_owner_arr) : result_arr := 
        let act := act_call x.(ack_is) 0 (serialize (N.eqb x.(i_owner) 1)) in
        Ok (st, [act]).

    Record _get_owners_arr := { ack_get : Address }.
    Definition get_owners_arr (st : storage_arr) (x : _get_owners_arr) : result_arr :=
        let act := act_call x.(ack_get) 0 (serialize st.(owners_arr)) in
        Ok (st, [act]).

    Inductive entrypoint_arr :=
        | addOwner (x : _add_owner_arr)
        | removeOwner (x : _remove_owner_arr)
        | swapOwners (x : _swap_owners_arr)
        | isOwner (x : _is_owner_arr)
        | getOwners (x : _get_owners_arr).

    (* serialization *)
    Section Serialization.
        Global Instance entrypoint_serializable : Serializable entrypoint_arr := todo.
        (* Derive Serializable entrypoint_rect<addOwner,removeOwner,swapOwners,isOwner,getOwners>. *)
        Global Instance storage_serializable : Serializable storage_arr := todo.
    End Serialization.


    (* init function definition *)
    Definition init_arr (_ : Chain) (_ : ContractCallContext) (init_st : setup_arr) :
        result storage_arr error := 
        Ok (init_st).

    (* receive function definition *)
    Definition receive_arr (_ : Chain) (_ : ContractCallContext) (st : storage_arr) 
        (msg : option entrypoint_arr) : result_arr :=
        match msg with 
        | Some (addOwner x)    => add_owner_arr st x
        | Some (removeOwner x) => remove_owner_arr st x
        | Some (swapOwners x)  => swap_owners_arr st x
        | Some (isOwner x)     => is_owner_arr st x
        | Some (getOwners x)   => get_owners_arr st x
        | None => Err 0
        end.

    Definition C_arr : Contract setup_arr entrypoint_arr storage_arr error := 
        build_contract init_arr receive_arr.

End ContractDefinition.


(* The optimized contract, which is correct (by definition) when it has the same
    input-output behavior of the original contract C_array *)
Definition SENTINEL_OWNERS : N := 0.
Section ContractDefinition. (* linked lists *)
    (** SENTINEL_OWNERS is used to traverse `owners`, so that:
            1. `owners[SENTINEL_OWNERS]` contains the first owner
            2. `owners[last_owner]` points back to SENTINEL_OWNERS
    *)

    (** contract types aside from the entrypoint type *)
    Record storage_ll := { owners_ll : FMap N N ; }. (* an array of event logs *)
    (* Definition sentinel : N := 0. *)

    Definition setup_ll := storage_ll.
    Definition result_ll : Type := result (storage_ll * list ActionBody) error.


    (* error codes *)
    Section ErrorCodes.
        Definition error_LINK_NOT_FOUND : error := 1.

    End ErrorCodes.

    (* some auxiliary functions for linked lists *)
    Section Aux.

    Definition find_prev_owner (owner : N) (owners : FMap N N) : result N error :=
        (* get the keys *)
        let keys := FMap.keys owners in
        (* find the previous owner *)
        let prev_owner := List.fold_right (fun k acc => 
            match (FMap.find k owners) with 
            | Some o => if N.eqb o owner then k else acc
            | None => acc
            end) 0 keys in
        (* check the result *)
        if N.eqb prev_owner 0 then Err error_LINK_NOT_FOUND else
        Ok prev_owner.

    Definition has_prev_owner (owner : N) (owners : FMap N N) : bool := 
        match find_prev_owner owner owners with 
        | Ok _ => true
        | Err _ => false
        end.

    Definition find_owner_result (owner : N) (owners : FMap N N) : result N error :=
        match FMap.find owner owners with
            | Some o => Ok o
            | None => Err error_LINK_NOT_FOUND
        end.
    
    Definition insert_ll (o : N) (accum : FMap N N) : result (FMap N N) error :=
        (* check the owner isn't the sentinel *)
        if N.eqb o SENTINEL_OWNERS then Err 0 else
        (* no duplicates *)
        if has_prev_owner o accum then Err 0 else
        (* owners[owner] = owners[SENTINEL_OWNERS]; *)
        do o' <- find_owner_result SENTINEL_OWNERS accum ;
        let accum' := FMap.add o o' accum in 
        (* owners[SENTINEL_OWNERS] = owner; *)
        Ok (FMap.add SENTINEL_OWNERS o accum').
    
    Definition insert_ll_2 (o : N) (accum : FMap N N) : FMap N N :=
        (* check the owner isn't the sentinel *)
        if N.eqb (o + 1) SENTINEL_OWNERS then accum else
        (* no duplicates *)
        if has_prev_owner (o + 1) accum then accum else
        (* owners[owner] = owners[SENTINEL_OWNERS]; *)
        match FMap.find SENTINEL_OWNERS accum with | None => accum | Some o' =>
        let accum' := FMap.add (o + 1) o' accum in 
        (* owners[SENTINEL_OWNERS] = owner; *)
        FMap.add SENTINEL_OWNERS (o + 1) accum' end.

    End Aux.

    (* entrypoint functions *)
    Record _add_owner_ll := { n_owner_ll : N }.
    Definition add_owner_ll (st : storage_ll) (x : _add_owner_ll) : result_ll :=
        let new_owner := n_owner_ll x in 
        let owners := owners_ll st in
        do owners_ll_new <- insert_ll new_owner owners;
        Ok ({| owners_ll := owners_ll_new |}, []).

    Record _remove_owner_ll := { r_owner_ll : N }.
    Definition remove_owner_ll (st : storage_ll) (x : _remove_owner_ll) : result_ll :=
        let owner := r_owner_ll x in 
        let owners := owners_ll st in
        do prev_owner <- find_prev_owner owner owners ;
        do next_owner <- find_owner_result owner owners ;
        (* check the owner isn't the sentinel (and not zero?) *)
        if N.eqb owner SENTINEL_OWNERS then Err 0 else
        if N.eqb owner 0 then Err 0 else
        (* owners[prevOwner] = owners[owner]; *)
        let owners_ll_new := FMap.add prev_owner next_owner owners in
        (* owners[owner] = address(0); *)
        let owners_ll_new := FMap.remove owner owners_ll_new in
        Ok ({| owners_ll := owners_ll_new |}, []).

    Record _swap_owners_ll := { owner_old_ll : N ; owner_new_ll : N }.
    Definition find_result (owner : N) (owners : FMap N N) : result N error :=
        match FMap.find owner owners with
            | Some o => Ok o
            | None => Err error_LINK_NOT_FOUND
        end.
    Definition swap_owners_ll (st : storage_ll) (x : _swap_owners_ll) : result_ll :=
        let old_owner := owner_old_ll x in 
        let new_owner := owner_new_ll x in 
        let owners := owners_ll st in
        (* owners[newOwner] = owners[oldOwner]; *)
        do old_owner_res <- find_result old_owner owners ;
        let owners_ll_new := FMap.add new_owner old_owner_res owners in
        (* owners[prevOwner] = newOwner; *)
        do prev_owner <- find_prev_owner old_owner owners ;
        let owners_ll_new := FMap.add prev_owner new_owner owners_ll_new in
        (* owners[oldOwner] = address(0); *)
        let owners_ll_new := FMap.remove old_owner owners_ll_new in
        Ok ({| owners_ll := owners_ll_new |}, []).

    Record _is_owner_ll := { i_owner_ll : N ; ack_is_ll : Address }.
    Definition is_owner_ll (st : storage_ll) (x : _is_owner_ll) : result_ll := 
        (* check mapping is nonzero *)
        todo.

    Record _get_owners_ll := { ack_get_ll : Address }.
    Definition get_owners_ll (st : storage_ll) (x : _get_owners_ll) : result_ll :=
        (* make a list probably, return it to ack *)
        todo.

    Inductive entrypoint_ll :=
        | addOwner_ll (x : _add_owner_ll)
        | removeOwner_ll (x : _remove_owner_ll)
        | swapOwners_ll (x : _swap_owners_ll)
        | isOwner_ll (x : _is_owner_ll)
        | getOwners_ll (x : _get_owners_ll).

    (* serialization *)
    Section Serialization.
        Global Instance entrypoint_ll_serializable : Serializable entrypoint_ll := todo.
        (* Derive Serializable entrypoint_rect<addOwner,removeOwner,swapOwners,isOwner,getOwners>. *)
        Global Instance storage_ll_serializable : Serializable storage_ll := todo.
    End Serialization.


    (* init function definition *)
    Definition init_ll (_ : Chain) (_ : ContractCallContext) (init_st : setup_ll) :
        result storage_ll error := 
        Ok (init_st).

    (* receive function definition *)
    Definition receive_ll (_ : Chain) (_ : ContractCallContext) (st : storage_ll) 
        (msg : option entrypoint_ll) : result_ll :=
        match msg with 
        | Some (addOwner_ll x)    => add_owner_ll st x
        | Some (removeOwner_ll x) => remove_owner_ll st x
        | Some (swapOwners_ll x)  => swap_owners_ll st x
        | Some (isOwner_ll x)     => is_owner_ll st x
        | Some (getOwners_ll x)   => get_owners_ll st x
        | None => Err 0
        end.

    Definition C_ll : Contract setup_ll entrypoint_ll storage_ll error := 
        build_contract init_ll receive_ll.

End ContractDefinition.



(* The formal specification *)
Section Specification.

(** First, a formal specification of the reference contract *)

(* No duplicate owners *)
(* 0 and sentinel (?) are never owners *)
(* functional specifications of each *)


(** the isomorphism *)
Section Isomorphism.

Section Aux.

(* Definition insert_ll () *)
Definition empty_map : FMap N N := FMap.empty.
Definition sentinal_init : FMap N N := FMap.add SENTINEL_OWNERS SENTINEL_OWNERS empty_map.

(* auxiliary functions for linked lists *)

Fixpoint has_duplicate (l : list N) : bool :=
  match l with
  | [] => false
  | x :: xs => if existsb (N.eqb x) xs then true else has_duplicate xs
  end.

(* to use, accum must initialize as sentinal_init *)
Fixpoint array_to_linked_list_rec (l : list N) (accum : FMap N N) : result (FMap N N) error := 
    match l with 
    | [] => Ok accum
    | a_hd :: a_tl => 
        do accum' <- insert_ll a_hd accum ;
        array_to_linked_list_rec a_tl accum'
    end.

Fixpoint array_to_linked_list_rec2 (l : list N) (accum : FMap N N) : FMap N N := 
    match l with 
    | [] => accum
    | a_hd :: a_tl => 
        array_to_linked_list_rec2 a_tl (insert_ll_2 a_hd accum)
    end.

Definition fixed_point_to_array (l : FMap N N) (accum : list N) : list N := 
    let keys := FMap.keys l in
    (* start with sentinel *)
    (* iterate through the keys *)
    (* decrease as you go *)
    todo.

Definition find_owner_null (o : N) (owners : FMap N N) : N := 
    match FMap.find o owners with | Some o' => o' | None => 0 end.    
Definition ll_pair_swap (res : result_ll) : result_ll := 
    match res with 
    | Ok (st, acts) =>
        let owners := owners_ll st in 
        let owner1 := find_owner_null SENTINEL_OWNERS owners in
        let owner2 := find_owner_null owner1 owners in 
        let owner3 := find_owner_null owner2 owners in
        let owners' := FMap.add SENTINEL_OWNERS owner2 owners in 
        let owners' := FMap.add owner2 owner1 owners' in 
        let owners' := FMap.add owner1 owner3 owners' in 
        Ok ({| owners_ll := owners' |}, acts)
    | Err e => Err e
    end.

Definition add_owner_ll_res (r : result_ll) (x : _add_owner_ll) : result_ll :=
    match r with 
    | Ok (st, acts) =>
        let new_owner := n_owner_ll x in 
        let owners := owners_ll st in
        do owners_ll_new <- insert_ll new_owner owners;
        Ok ({| owners_ll := owners_ll_new |}, acts)
    | Err e => Err e 
    end.


End Aux.

(** m : C_arr -> C_ll *)
Definition msg_morph (e : entrypoint_arr) : entrypoint_ll := 
    match e with
    | addOwner x => addOwner_ll {| n_owner_ll := x.(n_owner) + 1 |}
    | removeOwner x => removeOwner_ll {| r_owner_ll := x.(r_owner) |}
    | swapOwners x => swapOwners_ll {| owner_old_ll := x.(owner_old_arr) ; owner_new_ll := x.(owner_new_arr) |}
    | isOwner x => isOwner_ll {| i_owner_ll := x.(i_owner) ; ack_is_ll := x.(ack_is) |}
    | getOwners x => getOwners_ll {| ack_get_ll := x.(ack_get) |}
    end.

Definition state_morph (st : storage_arr) : storage_ll :=
    {| owners_ll :=
        array_to_linked_list_rec2 st.(owners_arr) sentinal_init |}.

Definition setup_morph := state_morph.
Definition error_morph : error -> error := id.

Lemma init_coherence : init_coherence_prop C_arr C_ll setup_morph state_morph error_morph.
Proof. now unfold init_coherence_prop. Qed.

Lemma recv_coherence : recv_coherence_prop C_arr C_ll msg_morph state_morph error_morph.
Proof.
    unfold recv_coherence_prop.
    intros.
    simpl.
    unfold result_functor, receive, receive'.
    destruct op_msg; auto.
    destruct e.
    (* add_owner_arr -> add_owner_ll *)
    -   simpl.
        destruct st, x.
        induction owners_arr0.
        (* base case: owners_arr is empty *)
        +   unfold add_owner_arr, state_morph. cbn.
            assert (insert_ll (n_owner0 + 1) (FMap.add 0 SENTINEL_OWNERS empty_map)
                = Ok (insert_ll_2 n_owner0 (FMap.add 0 SENTINEL_OWNERS empty_map)))
            as H_insert.
            {   unfold insert_ll, insert_ll_2.
                assert ((n_owner0 + 1 =? SENTINEL_OWNERS)%N = false) as H_not_sentinel.
                { unfold SENTINEL_OWNERS. now induction n_owner0. }
                rewrite H_not_sentinel. clear H_not_sentinel.
                assert (has_prev_owner (n_owner0 + 1) (FMap.add 0 SENTINEL_OWNERS empty_map) = false)
                as H_no_prev_owner.
                { admit. } (* probably has to be proved elsewhere, assumed as an invariant *)
                rewrite H_no_prev_owner. clear H_no_prev_owner.
                unfold find_owner_result.
                assert (FMap.find SENTINEL_OWNERS (FMap.add 0 SENTINEL_OWNERS empty_map) = Some 0)
                as H_sentinel_find.
                {   now unfold SENTINEL_OWNERS. }
                now rewrite H_sentinel_find. }
            now rewrite H_insert.
        (* inductive step: owners_arr is not empty *)
        +   replace ({| n_owner_ll := n_owner {| n_owner := n_owner0 |} + 1 |}) 
            with ({| n_owner_ll := n_owner0 + 1 |}) in *; auto.
            assert (add_owner_ll (state_morph {| owners_arr := a :: owners_arr0 |})
            {| n_owner_ll := n_owner0 + 1 |} = 
            ll_pair_swap (add_owner_ll_res
                (add_owner_ll (state_morph {| owners_arr := owners_arr0 |})
                    {| n_owner_ll := n_owner0 + 1 |})
                {| n_owner_ll := a |}))
            as H_apply_induction.
            {   unfold add_owner_ll_res, add_owner_ll, state_morph, ll_pair_swap.
                cbn. (* good place to start might be *)
                admit. (* TODO unfold the computation .. add_owner_ll_res might be wrong*) }
            rewrite H_apply_induction.
            admit. (* TODO unfold the computation *)
    (* remove_owner_arr -> remove_owner_ll *)
    -   cbn.
        
        admit.
    (* swap_owners_arr -> swap_owners_ll *)
    -   cbn.
        
        admit.
    (* is_owner_arr -> is_owner_ll *)
    -   cbn. admit.
    (* get_owners_arr -> get_owners_ll *)
    -   cbn. admit.
Admitted.

Definition f : ContractMorphism C C' := 
    build_contract_morphism C C' setup_morph msg_morph state_morph error_morph 
        init_coherence recv_coherence.

(* a morphism C' -> C *)
Definition msg_morph' (e : entrypoint') : entrypoint := 
    match e with | incr' _ => incr tt end.
Definition setup_morph' : setup' -> setup := id.
Definition state_morph' (st : storage') : storage := 
        {| n_1 := st.(n) ; extra_data := tt ; |}.
Definition error_morph' : error' -> error := id.

Lemma init_coherence' : init_coherence_prop C' C setup_morph' state_morph' error_morph'.
Proof. now unfold init_coherence_prop. Qed.

Lemma recv_coherence' : recv_coherence_prop C' C msg_morph' state_morph' error_morph'.
Proof.
    unfold recv_coherence_prop.
    intros.
    simpl.
    unfold result_functor, receive, receive'.
    destruct op_msg; auto.
    now destruct e.
Qed.

Definition g : ContractMorphism C' C := 
    build_contract_morphism C' C setup_morph' msg_morph' state_morph' error_morph' 
        init_coherence' recv_coherence'.


(* f and g are isomorphisms *)
Theorem c_c'_equivalent : is_iso_cm f g.
Proof.
    unfold is_iso_cm, compose_cm, id_cm.
    split; apply eq_cm; cbn;
    unfold setup_morph, setup_morph', msg_morph, msg_morph', state_morph, state_morph',
        error_morph, error_morph';
    auto;
    apply functional_extensionality;
    intros.
    -   now destruct x, u.
    -   now destruct x, extra_data0.
    -   now destruct x, u.
Qed.

End Isomorphism.

(** porting the specification over the isomorphism *)
Section Porting.

(* the specification of the reference contract *)

End Porting.

End Specification.

End ContractOptimization.