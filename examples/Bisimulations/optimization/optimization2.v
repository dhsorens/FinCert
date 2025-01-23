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
From Coq Require Import Lia.
From Coq.Init Require Import Byte.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** An example of a contract specification via bisimulation.

    TODO paragraph on linked lists and arrays
*)


(* First example *)
Section ContractOptimization.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Axiom todo : forall {A}, A.

Inductive entrypoint :=
    | addOwner (a : N) (* to add a as an owner ID *)
    | removeOwner (a : N) (* to remove a as an owner ID *)
    | swapOwners (a_fst a_snd : N). (* to swap a_fst for a_snd as owners *)

Definition setup := unit.

(* our contracts have separate storage types *)
Definition owners_arr := list N.
Definition owners_ll := FMap N N.

Section StateAux.
    Definition SENTINEL_OWNERS := 0.
    Definition empty_array : list N := [].
    Definition empty_linked_list : FMap N N := FMap.add SENTINEL_OWNERS SENTINEL_OWNERS FMap.empty.
End StateAux.

Definition error := N.

Section ErrorCodes.
    Definition error_NO_ENTRYPOINT : error := 0.
    Definition error_LINK_NOT_FOUND : error := 1.
End ErrorCodes.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint :=
    Derive Serializable entrypoint_rect<addOwner,removeOwner,swapOwners>.
    Global Instance arr_serializable : Serializable owners_arr := todo.
    Global Instance ll_serializable : Serializable owners_ll := todo.
End Serialization.

(* the contract that uses an array, owners_arr *)
Section ContractUsingArray.
    Definition result_arr := result (owners_arr * list ActionBody) error.

    Definition add_owner_arr (a : N) (st : owners_arr) : result_arr :=
        Ok (a :: st, []).
    
    Definition remove_owner_arr (a : N) (st : owners_arr) : result_arr :=
        Ok (List.remove N.eq_dec a st, []).

    Definition swap_owners_arr (a_fst a_snd : N) (st : owners_arr) : result_arr :=
        let owners_arr' :=
            List.map (fun o => if N.eqb o a_fst then a_snd else o) st in
        Ok (owners_arr', []).

    (* contract definition *)
    Definition init_arr (_ : Chain) (_ : ContractCallContext) (_ : setup) :
        result owners_arr error := 
        Ok empty_array.

    Definition receive_arr (_ : Chain) (_ : ContractCallContext)
        (st : owners_arr)  (msg : option entrypoint) : result_arr :=
        match msg with 
        | Some (addOwner a) => add_owner_arr a st
        | Some (removeOwner a) => remove_owner_arr a st
        | Some (swapOwners a_fst a_snd)  => swap_owners_arr a_fst a_snd st
        | None => Err error_NO_ENTRYPOINT
        end.
    
    (* contract definition *)
    Definition C_arr : Contract setup entrypoint owners_arr error :=
        build_contract init_arr receive_arr.

End ContractUsingArray.

(* the contract that uses linked lists, owners_ll *)
Section ContractUsingLinkedList.
    Section Aux.
        Definition find_prev_a (a : N) (st : owners_ll) : N := todo.
        Definition find_next_a (a : N) (st : owners_ll) : N := todo.
    End Aux.

    Definition result_ll := result (owners_ll * list ActionBody) error.

    Definition add_owner_ll (a : N) (st : owners_ll) : result_ll :=
        Ok (FMap.add SENTINEL_OWNERS a (FMap.add a (find_next_a a st) st), []).
        (* match FMap.find SENTINEL_OWNERS st with
        | None => Err error_LINK_NOT_FOUND
        | Some a' => Ok (FMap.add SENTINEL_OWNERS a (FMap.add a a' st), [])
        end. *)

    Definition remove_owner_ll (a : N) (st : owners_ll) : result_ll :=
        match FMap.find a st with
        | None => Ok (st, []) (* returns st if a not in *)
        | Some a_next => (* otherwise, it finds the prev owner and updates *)
            let a_prev := find_prev_a a st in
            Ok (FMap.add a_prev a_next (FMap.remove a st), [])
        end.

    Definition swap_owners_ll (a_fst a_snd : N) (st : owners_ll) : result_ll :=
        match FMap.find a_fst st with 
        | None => Ok (st, [])  (* returns st if a_fst not in *)
        | Some a_next =>
            let a_prev := find_prev_a a_fst st in
            Ok (FMap.add a_prev a_snd (FMap.add a_snd a_next (FMap.remove a_fst st)), [])
        end.

    (* contract definition *)
    Definition init_ll (_ : Chain) (_ : ContractCallContext) (_ : setup) :
        result owners_ll error := 
        Ok empty_linked_list.

    Definition receive_ll (_ : Chain) (_ : ContractCallContext)
        (st : owners_ll)  (msg : option entrypoint) : result_ll :=
        match msg with 
        | Some (addOwner a) => add_owner_ll a st
        | Some (removeOwner a) => remove_owner_ll a st
        | Some (swapOwners a_fst a_snd)  => swap_owners_ll a_fst a_snd st
        | None => Err error_NO_ENTRYPOINT
        end.
    
    (* contract definition *)
    Definition C_ll : Contract setup entrypoint owners_ll error :=
        build_contract init_ll receive_ll.

End ContractUsingLinkedList.

Section Isomorphism.
    Section Aux.
        
        Fixpoint arr_to_ll_rec (st : owners_arr) (acc : owners_ll) : owners_ll :=
            match st with
            | [] => acc
            | a :: st' =>
                let a' := find_next_a SENTINEL_OWNERS acc in 
                arr_to_ll_rec st' (FMap.add SENTINEL_OWNERS a (FMap.add a a' acc))
                (* match FMap.find SENTINEL_OWNERS acc with 
                | Some a' => arr_to_ll_rec st' (FMap.add a a' acc)
                | None => acc (* unreachable state TODO *)
                end *)
            end.

        Definition arr_to_ll (st : owners_arr) : owners_ll := arr_to_ll_rec st empty_linked_list.
            

        Definition ll_to_arr (st : owners_ll) : owners_arr := todo.

        (* some coherence lemmas *)


    End Aux.

    (* msg, setup, and error morphisms are all identity *)
    Definition msg_morph : entrypoint -> entrypoint := id.
    Definition setup_morph : setup -> setup := id.
    Definition error_morph : error -> error := id.

    (* storage morphisms *)
    Definition state_morph : owners_arr -> owners_ll := arr_to_ll.
    Definition state_morph_inv : owners_ll -> owners_arr := ll_to_arr.

    Section Lemmata.
        (* some coherence lemmas for init *)
        Lemma empty_coh : state_morph empty_array = empty_linked_list.
        Admitted.
        
        Lemma empty_coh_rev : state_morph_inv empty_linked_list = empty_array.
        Admitted.

        (* some coherence lemmas for recv *)
        Lemma add_owner_coh : forall a st st' acts,
            add_owner_arr a st = Ok (st', acts) ->
            add_owner_ll a (state_morph st) = Ok (state_morph st', acts).
        Admitted.

        Lemma add_owner_coh' : forall a st e,
            add_owner_arr a st = Err e ->
            add_owner_ll a (state_morph st) = Err e.
        Admitted.

        Lemma remove_owner_coh : forall a st st' acts,
            remove_owner_arr a st = Ok (st', acts) ->
            remove_owner_ll a (state_morph st) = Ok (state_morph st', acts).
        Admitted.

        Lemma remove_owner_coh' : forall a st e,
            remove_owner_arr a st = Err e ->
            remove_owner_ll a (state_morph st) = Err e.
        Admitted.

        Lemma swap_owners_coh : forall a_fst a_snd st st' acts,
            swap_owners_arr a_fst a_snd st = Ok (st', acts) ->
            swap_owners_ll a_fst a_snd (state_morph st) = Ok (state_morph st', acts).
        Admitted.

        Lemma swap_owners_coh' : forall a_fst a_snd st e,
            swap_owners_arr a_fst a_snd st = Err e ->
            swap_owners_ll a_fst a_snd (state_morph st) = Err e.
        Admitted.

        Lemma add_owner_coh_inv : forall a st st' acts,
            add_owner_ll a st = Ok (st', acts) ->
            add_owner_arr a (state_morph_inv st) = Ok (state_morph_inv st', acts).
        Admitted.

        Lemma add_owner_coh'_inv : forall a st e,
            add_owner_ll a st = Err e ->
            add_owner_arr a (state_morph_inv st) = Err e.
        Admitted.

        Lemma remove_owner_coh_inv : forall a st st' acts,
            remove_owner_ll a st = Ok (st', acts) ->
            remove_owner_arr a (state_morph_inv st) = Ok (state_morph_inv st', acts).
        Admitted.

        Lemma remove_owner_coh'_inv : forall a st e,
            remove_owner_ll a st = Err e ->
            remove_owner_arr a (state_morph_inv st) = Err e.
        Admitted.

        Lemma swap_owners_coh_inv : forall a_fst a_snd st st' acts,
            swap_owners_ll a_fst a_snd st = Ok (st', acts) ->
            swap_owners_arr a_fst a_snd (state_morph_inv st) = Ok (state_morph_inv st', acts).
        Admitted.

        Lemma swap_owners_coh'_inv : forall a_fst a_snd st e,
            swap_owners_ll a_fst a_snd st = Err e ->
            swap_owners_arr a_fst a_snd (state_morph_inv st) = Err e.
        Admitted.

        (*  *)
        Lemma state_morph_iso : forall st, state_morph (state_morph_inv st) = st.
        Admitted.

        Lemma state_morph_iso_inv : forall st, state_morph_inv (state_morph st) = st.
        Admitted.

    End Lemmata.

    (*  *)
    Lemma init_coherence : init_coherence_prop C_arr C_ll setup_morph state_morph error_morph.
    Proof. now unfold init_coherence_prop, result_functor. Qed.

    Lemma recv_coherence : recv_coherence_prop C_arr C_ll msg_morph state_morph error_morph.
    Proof.
        unfold recv_coherence_prop.
        intros.
        simpl.
        unfold result_functor, receive_arr, receive_ll.
        destruct op_msg; auto.
        destruct e.
        -   destruct (add_owner_arr a st) eqn:H_res.
            +   destruct t as [st' acts].
                now apply add_owner_coh in H_res.
            +   now apply add_owner_coh' in H_res.
        -   destruct (remove_owner_arr a st) eqn:H_res.
            +   destruct t as [st' acts].
                now apply remove_owner_coh in H_res.
            +   now apply remove_owner_coh' in H_res.
        -   destruct (swap_owners_arr a_fst a_snd st) eqn:H_res.
            +   destruct t as [st' acts].
                now apply swap_owners_coh in H_res.
            +   now apply swap_owners_coh' in H_res.
    Qed.

    (* the contract morphism f : C_arr -> C_ll *)
    Definition f : ContractMorphism C_arr C_ll :=
        build_contract_morphism C_arr C_ll
            setup_morph msg_morph state_morph error_morph init_coherence recv_coherence.


    (*  *)
    Lemma init_coherence_inv : init_coherence_prop C_ll C_arr
        setup_morph state_morph_inv error_morph.
    Proof.
        unfold init_coherence_prop, result_functor.
        intros.
        simpl.
        unfold init_arr.
        now rewrite empty_coh_rev.
    Qed.

    Lemma recv_coherence_inv : recv_coherence_prop C_ll C_arr
        msg_morph state_morph_inv error_morph.
    Proof.
        unfold recv_coherence_prop.
        intros.
        simpl.
        unfold result_functor, receive_ll, receive_arr.
        destruct op_msg; auto.
        destruct e.
        -   destruct (add_owner_ll a st) eqn:H_res.
            +   destruct t as [st' acts].
                now apply add_owner_coh_inv in H_res.
            +   now apply add_owner_coh'_inv in H_res.
        -   destruct (remove_owner_ll a st) eqn:H_res.
            +   destruct t as [st' acts].
                now apply remove_owner_coh_inv in H_res.
            +   now apply remove_owner_coh'_inv in H_res.
        -   destruct (swap_owners_ll a_fst a_snd st) eqn:H_res.
            +   destruct t as [st' acts].
                now apply swap_owners_coh_inv in H_res.
            +   now apply swap_owners_coh'_inv in H_res.
    Qed.

    (* the contract morphism f_inv : C_ll -> C_arr *)
    Definition f_inv : ContractMorphism C_ll C_arr :=
        build_contract_morphism C_ll C_arr
            setup_morph msg_morph state_morph_inv error_morph
            init_coherence_inv recv_coherence_inv.


    (* f and f_inv are indeed inverses *)
    Theorem iso_ll_arr : is_iso_cm f f_inv.
    Proof.
        unfold is_iso_cm.
        split;
        apply eq_cm; cbn;
        apply functional_extensionality;
        intros;
        unfold Basics.compose;
        auto.
        -   now rewrite state_morph_iso_inv.
        -   now rewrite state_morph_iso.
    Qed.

    Theorem iso_arr_all : is_iso_cm f_inv f.
    Proof. apply iso_cm_symmetric. apply iso_ll_arr. Qed.

    Theorem contracts_isomorphic : contracts_isomorphic C_arr C_ll.
    Proof. exists f, f_inv. apply iso_ll_arr. Qed.

End Isomorphism.

End ContractOptimization.