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
        if in_dec N.eq_dec a st then Err error_LINK_NOT_FOUND else
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

    Section Aux.
        Lemma add_owner_arr_no_acts : forall a st st' acts,
            add_owner_arr a st = Ok (st', acts) -> acts = [].
        Proof.
            intros * H_add.
            unfold add_owner_arr in H_add.
            destruct (in_dec N.eq_dec a st) in H_add; try inversion H_add.
            now inversion H_add.
        Qed.

        Lemma swap_owner_arr_no_acts : forall a_fst a_snd st st' acts,
            swap_owners_arr a_fst a_snd st = Ok (st', acts) -> acts = [].
        Proof.
            intros * H_swap.
            unfold swap_owners_arr in H_swap.
            inversion H_swap as [[H_swap0 H_swap1]].
            now subst.
        Qed.

        Lemma swap_always_succeeds : forall a_fst a_snd st,
            exists st', swap_owners_arr a_fst a_snd st = Ok (st', []).
        Proof.
            intros.
            exists (List.map (fun o => if N.eqb o a_fst then a_snd else o) st).
            now simpl.
        Qed.
        
    End Aux.

End ContractUsingArray.

(* the contract that uses linked lists, owners_ll *)
Section ContractUsingLinkedList.
    
    Definition result_ll := result (owners_ll * list ActionBody) error.

    Section Aux.
        Definition find_next_a (a : N) (st : owners_ll) : result N error := todo.
        Definition find_prev_a (a : N) (st : owners_ll) : result N error := todo.

        (* invariant on C_ll *)
        Lemma find_prev_invar : forall a a_next st, 
            find_next_a a st = Ok a_next -> 
            exists a_prev,
                find_prev_a a st = Ok a_prev /\
                find_next_a a_prev st = Ok a.
        Admitted.
        
        Lemma find_next_invar : forall st,
            exists a, find_next_a SENTINEL_OWNERS st = Ok a.
        Admitted.

        Definition find_next_sentinel (st : owners_ll) : N := todo.

        Lemma find_next_prev : forall a a_next st,
            find_next_a a st = Ok a_next ->
            Ok a = find_prev_a a_next st.
        Admitted.

        Lemma find_prev_next : forall a a_prev st,
            find_prev_a a st = Ok a_prev ->
            Ok a = find_next_a a_prev st.
        Admitted.

        Lemma find_prev_next' : forall a a_next st,
            find_next_a a st = Ok a_next -> 
            exists a_prev, find_prev_a a st = Ok a_prev.
        Admitted.

        Definition ll_insert (a : N) (st : owners_ll) : owners_ll :=
            let a' := find_next_sentinel st in 
            FMap.add SENTINEL_OWNERS a (FMap.add a a' st).
        
        Definition ll_remove (a : N) (st : owners_ll) : result owners_ll error :=
            match FMap.find a st with
            | None => Ok st (* returns st if a not in *)
            | Some a_next => (* otherwise, it finds the prev owner and updates *)
                do a_prev <- find_prev_a a st;
                Ok (FMap.add a_prev a_next (FMap.remove a st))
            end.

        Definition ll_is_in (a : N) (st : owners_ll) : bool := 
            match FMap.find a st with | None => false | Some _ => true end.
        
        

        (* takes a linked list and removes the first element, if there is one *)
        Definition ll_decrement (st : owners_ll) : owners_ll := todo.

    End Aux.

    Definition add_owner_ll (a : N) (st : owners_ll) : result_ll :=
        if ll_is_in a st then Err error_LINK_NOT_FOUND (* no duplicates *)
        else Ok (ll_insert a st, []). (* always succeeds *)

    Definition remove_owner_ll (a : N) (st : owners_ll) : result_ll :=
        do st' <- ll_remove a st;
        Ok (st', []).

    Definition swap_owners_ll (a_fst a_snd : N) (st : owners_ll) : result_ll :=
        match FMap.find a_fst st with 
        | None => Ok (st, [])  (* returns st if a_fst not in *)
        | Some a_next =>
            do a_prev <- find_prev_a a_fst st;
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
                (* arr_to_ll_rec st' (FMap.add SENTINEL_OWNERS a (FMap.add a a' acc)) *)
                match FMap.find SENTINEL_OWNERS acc with 
                | Some a' => arr_to_ll_rec st' (FMap.add a a' acc)
                | None => acc (* unreachable state TODO *)
                end
            end.

        Definition arr_to_ll (st : owners_arr) : owners_ll :=
            arr_to_ll_rec (List.rev st) empty_linked_list.


        Definition ll_to_arr_rec (st : owners_ll) (acc : owners_arr) : owners_arr :=
            match FMap.find SENTINEL_OWNERS st with
            | None => acc
            | Some a => 
                match a with 
                | 0 => acc 
                | x => todo (* ll_to_arr_rec (ll_decrement st) (a :: acc) *)
                end
            end.
        
        Definition ll_to_arr (st : owners_ll) : owners_arr :=
            ll_to_arr_rec st empty_array.


        (* some coherence lemmas *)
        Lemma arr_to_ll_rev : forall st, ll_to_arr (arr_to_ll st) = st.
        Admitted.

        Lemma ll_to_arr_rev : forall st,
            cstate_reachable C_ll st ->
            arr_to_ll (ll_to_arr st) = st.
        Admitted.

        Lemma arr_to_ll_insert : forall a st,
            ll_insert a (arr_to_ll st) = arr_to_ll (a :: st).
        Admitted.

        Lemma arr_to_ll_insert_inv : forall a st,
            a :: ll_to_arr st = ll_to_arr (ll_insert a st).
        Admitted.

        Lemma arr_to_ll_remove : forall a st,
            ll_remove a (arr_to_ll st) = 
            Ok (arr_to_ll (List.remove N.eq_dec a st)).
        Admitted.

        Lemma ll_remove_lem : forall a st, 
            exists x, ll_remove a st = Ok x.
        Proof.
            intros.
            destruct (ll_remove a st) eqn:H_remove.
            -   unfold ll_remove in H_remove.
                destruct (FMap.find a st) eqn:H_found; simpl in *.
                +   destruct (find_prev_a a st).
                    *   now exists (FMap.add t0 n (FMap.remove a st)).
                    *   inversion H_remove.
                +   now exists st.
            -   unfold ll_remove in H_remove.
                destruct (FMap.find a st) eqn:H_found; simpl in *.
                +   destruct (find_prev_a a st).
                    *   inversion H_remove.
                    *   admit.
                +   inversion H_remove.
        Admitted.

        Lemma arr_to_ll_swap : forall a_prev a_snd a_fst n st,
            FMap.add a_prev a_snd (FMap.add a_snd n (FMap.remove a_fst (arr_to_ll st))) =
            arr_to_ll (map (fun o : N => if (o =? a_fst)%N then a_snd else o) st).
        Admitted.

        Lemma ll_fst_found_snd_found : forall a_fst st n,
            FMap.find a_fst (arr_to_ll st) = Some n -> 
            exists t, find_prev_a a_fst (arr_to_ll st) = Ok t.
        Admitted.

        (* TODO split into an invariant *)
        Theorem arr_to_ll_no_duplicates : forall a st st' acts,
            add_owner_arr a st = Ok (st', acts) -> 
            (ll_is_in a (arr_to_ll st) = false).
        Admitted.

        Lemma ll_to_arr_found : forall a st,
            ll_is_in a st = true -> 
            exists i, in_dec N.eq_dec a (ll_to_arr st) = left i.
        Admitted.

        Lemma is_in_find_dec : forall a st i,
            (in_dec N.eq_dec a st = left i) <->
            (FMap.find a (arr_to_ll st) <> None).
        Admitted.

        Lemma is_in_find_dec_inv : forall a st i,
            (in_dec N.eq_dec a (ll_to_arr st) = left i) <->
            (FMap.find a st <> None).
        Admitted.

        Lemma swap_idempotent : forall a_fst a_snd st st' acts,
            swap_owners_arr a_fst a_snd st = Ok (st', acts) ->
            FMap.find a_fst (arr_to_ll st) = None ->
            st = st'.
        Admitted.

        Lemma add_owner_ll_no_acts : forall a st st' acts,
            add_owner_ll a st = Ok (st', acts) -> acts = [].
        Proof.
            intros * H_add.
            unfold add_owner_ll in H_add.
            destruct (ll_is_in a st) in H_add; try inversion H_add.
            now inversion H_add.
        Qed.

        Lemma swap_owner_ll_no_acts : forall a_fst a_snd st st' acts,
            swap_owners_ll a_fst a_snd st = Ok (st', acts) -> acts = [].
        Proof.
            intros * H_swap.
            unfold swap_owners_ll in H_swap.
            destruct (FMap.find a_fst st) in H_swap; try inversion H_swap; auto.
            destruct (find_prev_a a_fst st) in H0; now try inversion H0.
        Qed.

    End Aux.

    (* msg, setup, and error morphisms are all identity *)
    Definition msg_morph : entrypoint -> entrypoint := id.
    Definition setup_morph : setup -> setup := id.
    Definition error_morph : error -> error := id.

    (* storage morphisms *)
    Definition state_morph : owners_arr -> owners_ll := arr_to_ll.
    Definition state_morph_inv : owners_ll -> owners_arr := ll_to_arr.

    Section Lemmata.
        Section Aux.
            Lemma pair_lem { A B : Type } : forall (a a' : A) (b b' : B),
                a = a' /\ b = b' -> (a, b) = (a', b').
            Proof. intros. destruct H. now subst. Qed.
        End Aux.

        (* some coherence lemmas for init *)
        Lemma empty_coh : state_morph empty_array = empty_linked_list.
        Proof.
            unfold state_morph, empty_array, empty_linked_list.
            unfold arr_to_ll.
            simpl.
            now unfold empty_linked_list.
        Qed.
        
        Lemma empty_coh_rev : state_morph_inv empty_linked_list = empty_array.
        Proof.
            unfold state_morph_inv, empty_array, empty_linked_list.
            unfold ll_to_arr, ll_to_arr_rec, SENTINEL_OWNERS.
            replace (FMap.find 0 (FMap.add 0 0 FMap.empty))
            with (Some 0) by auto.
            now unfold empty_array.
        Qed.

        (* some coherence lemmas for recv *)
        Lemma add_owner_coh : forall a st st' acts,
            add_owner_arr a st = Ok (st', acts) ->
            add_owner_ll a (state_morph st) = Ok (state_morph st', acts).
        Proof.
            intros * H_in.
            unfold add_owner_arr, add_owner_ll, state_morph in *.
            replace (ll_is_in a (arr_to_ll st)) with false
            by (apply arr_to_ll_no_duplicates in H_in; now symmetry).
            apply f_equal.
            apply pair_lem.
            split.
            -   destruct (in_dec N.eq_dec a st) in H_in; try inversion H_in.
                unfold ll_insert.
                apply arr_to_ll_insert.
            -   symmetry.
                now apply (add_owner_arr_no_acts a st st' acts).
        Qed.

        Lemma add_owner_coh' : forall a st e,
            add_owner_arr a st = Err e ->
            add_owner_ll a (state_morph st) = Err e.
        Proof.
            intros * H_in.
            unfold add_owner_arr, add_owner_ll, state_morph in *.
            replace (ll_is_in a (arr_to_ll st)) with true.
            -   destruct (in_dec N.eq_dec a st) in H_in; now try inversion H_in.
            -   unfold ll_is_in.
                destruct (FMap.find a (arr_to_ll st)) eqn:H_found; auto.
                pose proof is_in_find_dec as H_is_in.
                destruct (in_dec N.eq_dec a st) eqn:H_found'; try inversion H_in.
                apply H_is_in in H_found'.
                rewrite H_found in H_found'.
                contradiction.
        Qed.

        Lemma remove_owner_coh : forall a st st' acts,
            remove_owner_arr a st = Ok (st', acts) ->
            remove_owner_ll a (state_morph st) = Ok (state_morph st', acts).
        Proof.
            intros * H_remove.
            unfold remove_owner_arr, remove_owner_ll, state_morph in *.
            simpl.
            inversion H_remove as [[H_r0 H_r1]].
            destruct (ll_remove a (arr_to_ll st)) eqn:H_remove'.
            -   f_equal.
                apply pair_lem.
                split; auto.
                now rewrite arr_to_ll_remove in H_remove'.
            -   pose proof (ll_remove_lem a (arr_to_ll st)).
                destruct H as [x H].
                rewrite H in H_remove'.
                now inversion H_remove'.
        Qed.

        Lemma remove_owner_coh' : forall a st e,
            remove_owner_arr a st = Err e ->
            remove_owner_ll a (state_morph st) = Err e.
        Proof.
            intros * H_remove.
            unfold remove_owner_arr, remove_owner_ll, state_morph in *.
            simpl.
            destruct (ll_remove a (arr_to_ll st)) eqn:H_remove'.
            -   destruct (FMap.find a (arr_to_ll st)) eqn:H_find.
                +   now inversion H_remove.
                +   now inversion H_remove.
            -   now inversion H_remove.
        Qed.

        Lemma swap_owners_coh : forall a_fst a_snd st st' acts,
            swap_owners_arr a_fst a_snd st = Ok (st', acts) ->
            swap_owners_ll a_fst a_snd (state_morph st) = Ok (state_morph st', acts).
        Proof.
            intros * H_swap.
            apply swap_owner_arr_no_acts in H_swap as H_acts.
            rewrite H_acts in *.
            unfold swap_owners_ll.
            destruct (FMap.find a_fst (state_morph st)) eqn:H_fst_found.
            (* case where a_fst is there *)
            -   simpl.
                unfold state_morph in *.
                apply ll_fst_found_snd_found in H_fst_found as H_prev_found.
                destruct H_prev_found as [a_prev H_prev_found].
                rewrite H_prev_found.
                f_equal.
                apply pair_lem.
                split.
                2:{ pose proof (add_owner_arr_no_acts).
                    now apply swap_owner_arr_no_acts in H_swap. }
                unfold swap_owners_arr in H_swap.
                inversion H_swap as [H_res].
                now apply arr_to_ll_swap.
            (* case where a_fst is not there *)
            -   unfold state_morph in *.
                apply swap_idempotent in H_swap; auto.
                now rewrite H_swap.
        Qed.

        Lemma swap_owners_coh' : forall a_fst a_snd st e,
            swap_owners_arr a_fst a_snd st = Err e ->
            swap_owners_ll a_fst a_snd (state_morph st) = Err e.
        Proof.
            intros * H_swap.
            pose proof (swap_always_succeeds a_fst a_snd st) as H_success.
            destruct H_success as [st' H_success].
            rewrite H_success in H_swap.
            inversion H_swap.
        Qed.

        Lemma add_owner_coh_inv : forall a st st' acts,
            add_owner_ll a st = Ok (st', acts) ->
            add_owner_arr a (state_morph_inv st) = Ok (state_morph_inv st', acts).
        Proof.
            intros * H_in.
            apply add_owner_ll_no_acts in H_in as H_acts.
            rewrite H_acts in *. clear H_acts.
            unfold add_owner_arr, add_owner_ll, state_morph_inv in *.
            destruct (ll_is_in a st) eqn:H_found.
            inversion H_in.
            unfold ll_is_in in H_found.
            destruct (FMap.find a st) eqn:H_found'; try inversion H_found.
            destruct (in_dec N.eq_dec a (ll_to_arr st)) eqn:H_in'.
            {   apply is_in_find_dec_inv in H_in'.
                now rewrite H_found' in H_in'. }
            f_equal.
            apply pair_lem.
            split; auto.
            inversion H_in as [H_insert_st].
            now apply arr_to_ll_insert_inv.
        Qed.

        Lemma add_owner_coh'_inv : forall a st e,
            add_owner_ll a st = Err e ->
            add_owner_arr a (state_morph_inv st) = Err e.
        Proof.
            intros * H_in.
            unfold add_owner_arr, add_owner_ll, state_morph_inv in *.
            destruct (ll_is_in a st) eqn:H_found; try inversion H_in.
            rewrite H0. clear H0.
            apply ll_to_arr_found in H_found.
            destruct H_found as [i H_found].
            now rewrite H_found.
        Qed.

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

        (* this is true under invariants *)
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

    Theorem bisim_arr_ll : contracts_isomorphic C_arr C_ll.
    Proof. exists f, f_inv. apply iso_ll_arr. Qed.

End Isomorphism.


Section Specification.

    Definition no_duplciates_arr (st : owners_arr) : Prop := NoDup st.

    Definition no_duplciates_ll (st : owners_ll) : Prop :=
        todo. (* you can cycle through the list and return to SENTINEL *)

    (* proved by contract induction *)
    Theorem no_duplciates (cstate : owners_arr) :
        cstate_reachable C_arr cstate -> no_duplciates_arr cstate.
    Admitted.

    (* proved by morphism induction *)
    Theorem no_duplciates' (cstate : owners_ll) : 
        cstate_reachable C_ll cstate -> no_duplciates_ll cstate.
    Admitted.

End Specification.

End ContractOptimization.