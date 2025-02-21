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
Require Import Coq.Logic.Classical_Prop.
From Coq.Init Require Import Byte.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** An example of a contract specification via bisimulation.

    A common optimization in EVM smart contract development is to use linked lists as a data structure to model an array. This is slightly more efficient than using an array, as it allows for constant-time removal of elements. However, linked lists are more complex to reason about, and it is easy to introduce bugs when using them.
    
    In this example, we show how to use bisimulation to prove that two contracts, one using an array and the other using a linked list, are equivalent. We show that the two contracts are bisimilar, meaning that they are equivalent in terms of their observable behavior. We define a contract morphism that maps the array contract to the linked list contract, and we prove that the two contracts are bisimilar with respect to this morphism.

    We then show how a property, like proving the invariant that the contracts have no duplicate owners in storage, can be ported over the bisimulation. We show that the property holds for the linked list contract if it holds for the array contract. This allows us to reason about the array contract using the simpler linked list contract.

    In the example we prove most things, and assume some basic facts about linked lists and arrays to simplify the example.

    [1] Itzhaky, Banerjee, Immerman, Nanevski, and Sagiv.
        Effectively-propositional reasoning about reachability in linked data structures.
        Computer Aided Verification, 2013.
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
        if in_dec N.eq_dec a_snd st then Ok (st, []) else
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
            destruct (in_dec N.eq_dec a_snd st) in H_swap;
            now inversion H_swap.
        Qed.

        Lemma swap_always_succeeds : forall a_fst a_snd st,
            exists st', swap_owners_arr a_fst a_snd st = Ok (st', []).
        Proof.
            intros.
            destruct (in_dec N.eq_dec a_snd st) eqn:H_snd_in.
            -   exists st.
                unfold swap_owners_arr.
                now rewrite H_snd_in.
            -   exists (List.map (fun o => if N.eqb o a_fst then a_snd else o) st).
                unfold swap_owners_arr.
                now rewrite H_snd_in.
        Qed.
        
    End Aux.

End ContractUsingArray.

(* the contract that uses linked lists, owners_ll *)
Section ContractUsingLinkedList.
    
    Definition result_ll := result (owners_ll * list ActionBody) error.

    Section Aux.
        Definition find_next_a (a : N) (st : owners_ll) : result N error := 
            match FMap.find a st with 
            | None => Err error_LINK_NOT_FOUND
            | Some a' => Ok a'
            end.

        (* assume a function that can find the previous element in a linked list *)
        Axiom find_prev_a : forall (a : N) (st : owners_ll), result N error.
        (* such that this invariant holds *)
        Axiom find_prev_invar : forall a a_next (st : owners_ll), 
            FMap.find a st = Some a_next -> 
            exists a_prev,
                FMap.find a_prev st = Some a /\
                find_prev_a a st = Ok a_prev.
        
        Definition find_next_sentinel (st : owners_ll) : N := 
            match FMap.find SENTINEL_OWNERS st with
            | None => SENTINEL_OWNERS | Some a => a
            end.

        Axiom find_next_sentinal_invar : forall st,
            exists a, find_next_sentinel st = a.

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
        match FMap.find a_snd st with | Some _ => Ok (st, []) | None => 
            match FMap.find a_fst st with 
            | None => Ok (st, [])  (* returns st if a_fst not in *)
            | Some a_next =>
                do a_prev <- find_prev_a a_fst st;
                Ok (FMap.add a_prev a_snd (FMap.add a_snd a_next (FMap.remove a_fst st)), [])
            end
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
    (* some assumptions, functions, and lemmas *)
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

        Axiom ll_to_arr_cons : forall a st,
            ll_to_arr (arr_to_ll (a :: st)) = a :: ll_to_arr (arr_to_ll (st)).

        Lemma arr_to_ll_rev : forall st, ll_to_arr (arr_to_ll st) = st.
        Proof.
            intro.
            induction st.
            -   now unfold arr_to_ll, ll_to_arr.
            -   rewrite ll_to_arr_cons.
                now rewrite IHst.
        Qed.

        (* we assume this as an invariant;
            this holds on all reachable states but for the purpose of 
            the isomorphism we assume it hold for all states *)
        Axiom ll_to_arr_rev : forall st,
            (* cstate_reachable C_ll st -> *)
            arr_to_ll (ll_to_arr st) = st.
        
        Axiom arr_to_ll_insert : forall a st,
            ll_insert a (arr_to_ll st) = arr_to_ll (a :: st).
        
        Axiom arr_to_ll_insert_inv : forall a st,
            a :: ll_to_arr st = ll_to_arr (ll_insert a st).
        
        Lemma ll_remove_lem : forall a st, 
            exists x, ll_remove a st = Ok x.
        Proof.
            intros.
            unfold ll_remove.
            destruct (FMap.find a st) eqn:H_find.
            -   simpl.
                pose proof (find_prev_invar a n st H_find) as H_prev.
                destruct H_prev as [a_prev [_ H_prev']].
                rewrite H_prev'.
                now exists (FMap.add a_prev n (FMap.remove a st)).
            -   now exists st.
        Qed.

        Lemma ll_remove_failure : forall a st e,
            remove_owner_ll a st = Err e -> False.
        Proof.
            intros * H_remove.
            pose proof (ll_remove_lem a st) as H.
            destruct H as [x H].
            unfold remove_owner_ll in H_remove.
            simpl in H_remove.
            rewrite H in H_remove.
            inversion H_remove.
        Qed.

        Axiom arr_to_ll_remove : forall a st,
            ll_remove a (arr_to_ll st) = 
            Ok (arr_to_ll (List.remove N.eq_dec a st)).

        Lemma ll_swap_failure : forall a_fst a_snd st e, 
            swap_owners_ll a_fst a_snd st = Err e -> False.
        Proof.
            intros * H.
            unfold swap_owners_ll in H.
            destruct (FMap.find a_snd st) eqn:H_snd_in in H; try now inversion H.
            destruct (FMap.find a_fst st) eqn:H_fst_in in H; try now inversion H.
            simpl in H.
            pose proof (find_prev_invar a_fst n st H_fst_in) as H_prev_invar.
            destruct H_prev_invar as [a_prev [H_prev_invar H_prev_invar']].
            rewrite H_prev_invar' in H.
            inversion H.
        Qed.

        Axiom ll_remove_coh_lem : forall a a_prev a_next st,
            FMap.find a st = Some a_next ->
            find_prev_a a st = Ok a_prev ->
            remove N.eq_dec a (ll_to_arr st) =
            ll_to_arr (FMap.add a_prev a_next (FMap.remove a st)).

        Axiom arr_to_ll_swap : forall a_prev a_snd a_fst n st,
            FMap.add a_prev a_snd (FMap.add a_snd n (FMap.remove a_fst (arr_to_ll st))) =
            arr_to_ll (map (fun o : N => if (o =? a_fst)%N then a_snd else o) st).

        Axiom ll_to_arr_swap : forall a_fst a_snd a_prev a_next st,
            FMap.find a_fst st = Some a_next ->
            map (fun o : N => if (o =? a_fst)%N then a_snd else o) (ll_to_arr st) =
            ll_to_arr (FMap.add a_prev a_snd (FMap.add a_snd a_next (FMap.remove a_fst st))).
        
        Lemma ll_fst_found_snd_found : forall a_fst st n,
            FMap.find a_fst (arr_to_ll st) = Some n -> 
            exists t, find_prev_a a_fst (arr_to_ll st) = Ok t.
        Proof.
            intros * H_fst_in.
            pose proof (find_prev_invar a_fst n (arr_to_ll st) H_fst_in) as H_prev.
            destruct H_prev as [a_prev [H_prev H_prev']].
            now exists a_prev.
        Qed.

        Lemma ll_fst_found_snd_found' : forall a_fst st n, 
            FMap.find a_fst st = Some n -> 
            exists t, find_prev_a a_fst st = Ok t.
        Proof.
            intros * H_fst_in.
            pose proof (find_prev_invar a_fst n st H_fst_in) as H_prev.
            destruct H_prev as [a_prev [H_prev H_prev']].
            now exists a_prev.
        Qed.

        Axiom ll_to_arr_found : forall a st,
            ll_is_in a st = true -> 
            exists i, in_dec N.eq_dec a (ll_to_arr st) = left i.

        Axiom arr_to_ll_found : forall a st n,
            in_dec N.eq_dec a st = right n -> 
            ll_is_in a (arr_to_ll st) = false.

        Theorem arr_to_ll_no_duplicates : forall a st st' acts,
            add_owner_arr a st = Ok (st', acts) -> 
            (ll_is_in a (arr_to_ll st) = false).
        Proof.
            intros * H_add.
            unfold add_owner_arr in H_add.
            destruct (in_dec N.eq_dec a st) eqn:H_eq_dec in H_add;
            try inversion H_add.
            apply (arr_to_ll_found a st n H_eq_dec).
        Qed.

        Axiom in_arr_ll : forall a st,
            FMap.find a (arr_to_ll st) = None ->
            ~ In a st.
        
        Lemma is_in_find_dec : forall a st i,
            (in_dec N.eq_dec a st = left i) ->
            (FMap.find a (arr_to_ll st) <> None).
        Proof.
            intros a st i.
            intro H_in_dec.
            pose proof (in_arr_ll a st).
            unfold not.
            intro H_not_in.
            apply H in H_not_in.
            contradiction.
        Qed.

        Axiom in_arr_ll' : forall a st, 
            FMap.find a st = None ->
            ~ In a (ll_to_arr st).

        Lemma is_in_find_dec_inv : forall a st i,
            (in_dec N.eq_dec a (ll_to_arr st) = left i) ->
            (FMap.find a st <> None).
        Proof.
            intros a st i.
            intro H_in_dec.
            pose proof (in_arr_ll' a st).
            unfold not.
            intro H_not_in.
            apply H in H_not_in.
            contradiction.
        Qed.

        Lemma swap_idempotent : forall a_fst a_snd st,
            FMap.find a_fst (arr_to_ll st) = None ->
            (map (fun o : N => if (o =? a_fst)%N then a_snd else o) st) = st.
        Proof.
            intros * H_in.
            apply in_arr_ll in H_in.
            induction st.
            -   now unfold map.
            -   unfold not, In in H_in.
                apply not_or_and in H_in.
                destruct H_in as [H_a_fst H_in].
                unfold not, In in IHst.
                apply IHst in H_in.
                clear IHst.
                simpl.
                rewrite H_in.
                replace (if (a =? a_fst)%N then a_snd else a)
                with a; auto.
                destruct (a =? a_fst)%N eqn:H_eq; auto.
                apply N.eqb_eq in H_eq.
                contradiction.
        Qed.

        Lemma swap_idempotent' : forall a_fst a_snd st,
            FMap.find a_fst st = None ->
            map (fun o : N => if (o =? a_fst)%N then a_snd else o)
                (ll_to_arr st) = 
            (ll_to_arr st).
        Proof.
            intros * H_in.
            rewrite <- (ll_to_arr_rev st) in H_in.
            now apply (swap_idempotent a_fst a_snd (ll_to_arr st)).
        Qed.

        Lemma remove_not_in : forall (a : N) (l : list N),
            ~ In a l -> remove N.eq_dec a l = l.
        Proof.
        intros a l H.
        induction l as [| h t IH].
        - (* Base case: l is empty *)
            simpl. reflexivity.
        - (* Inductive case: l is h :: t *)
            simpl.
            destruct (N.eq_dec a h) as [H_eq | H_neq].
            + (* Case: a = h *)
            exfalso. apply H. left. symmetry. assumption.
            + (* Case: a <> h *)
            simpl. f_equal. apply IH.
            unfold not. intros H_in. apply H. right. assumption.
        Qed.

        Lemma remove_not_found : forall a st,
            FMap.find a st = None -> 
            remove N.eq_dec a (ll_to_arr st) = ll_to_arr st.
        Proof.
            intros * H_none.
            pose proof (in_arr_ll' a st H_none).
            now apply remove_not_in.
        Qed.

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
            destruct (FMap.find a_snd st) in H_swap; try now inversion H_swap.
            destruct (FMap.find a_fst st) in H_swap; try inversion H_swap; auto.
            destruct (find_prev_a a_fst st) in H0; now try inversion H0.
        Qed.

        Lemma empty_arr_transform : ll_to_arr (arr_to_ll []) = [].
        Proof. now unfold arr_to_ll, ll_to_arr. Qed.

        (* some final assumed invariants/conditions *)
        Axiom nodup_state_morph_some'_aux : forall a_snd st n,
            FMap.find a_snd st = Some n -> 
            In a_snd (ll_to_arr st).

        Axiom nodup_state_morph_none'_aux : forall a_snd st,
            FMap.find a_snd st = None -> 
            ~ In a_snd (ll_to_arr st).

        Axiom nodup_state_morph_some_aux : forall a_snd st,
            In a_snd st -> 
            exists x, FMap.find a_snd (arr_to_ll st) = Some x.

        Axiom nodup_state_morph_none_aux : forall a_snd st,
            ~ In a_snd st -> 
            FMap.find a_snd (arr_to_ll st) = None.
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

        Lemma nodup_state_morph_some : forall st a_snd i, 
            in_dec N.eq_dec a_snd st = left i -> 
            exists x, FMap.find a_snd (arr_to_ll st) = Some x.
        Proof.
            intros * H_dup.
            destruct (FMap.find a_snd (arr_to_ll st)) eqn:H_found;
            try now exists n.
            pose proof (nodup_state_morph_some_aux a_snd st i) as H_in.
            now destruct H_in as [x H_in].
        Qed.

        Lemma nodup_state_morph_none : forall st a_snd n, 
            in_dec N.eq_dec a_snd st = right n -> 
            FMap.find a_snd (arr_to_ll st) = None.
        Proof.
            intros * H_dup.
            destruct (FMap.find a_snd (arr_to_ll st)) eqn:H_found; auto.
            now pose proof (nodup_state_morph_none_aux a_snd st n).
        Qed.

        Lemma swap_owners_coh : forall a_fst a_snd st st' acts,
            swap_owners_arr a_fst a_snd st = Ok (st', acts) ->
            swap_owners_ll a_fst a_snd (state_morph st) = Ok (state_morph st', acts).
        Proof.
            intros * H_swap.
            apply swap_owner_arr_no_acts in H_swap as H_acts.
            rewrite H_acts in *. clear H_acts.
            unfold swap_owners_arr, swap_owners_ll in *.
            unfold state_morph.
            destruct (in_dec N.eq_dec a_snd st) eqn:H_dup.
            -   apply nodup_state_morph_some in H_dup.
                destruct H_dup as [x H_dup].
                rewrite H_dup.
                now inversion H_swap.
            -   apply nodup_state_morph_none in H_dup.
                rewrite H_dup.
                destruct (FMap.find a_fst (arr_to_ll st)) eqn:H_fst_found.
                (* case where a_fst is there *)
                +   simpl.
                    apply ll_fst_found_snd_found in H_fst_found as H_prev_found.
                    destruct H_prev_found as [a_prev H_prev_found].
                    rewrite H_prev_found.
                    f_equal.
                    apply pair_lem.
                    split; auto.
                    inversion H_swap as [H_res].
                    now apply arr_to_ll_swap.
                (* case where a_fst is not there *)
                +   inversion H_swap as [H_swap'].
                    now rewrite swap_idempotent.
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
        Proof.
            intros * H_remove.
            unfold remove_owner_ll, remove_owner_arr, state_morph_inv in *.
            simpl in *.
            destruct (ll_remove a st) eqn:H_remove_eq in H_remove; try inversion H_remove.
            f_equal.
            apply pair_lem. split; auto.
            unfold ll_remove in H_remove_eq.
            clear H1 H_remove.
            rewrite H0 in *.
            clear H0.
            destruct (FMap.find a st) eqn:H_a_in_st.
            (* a is in st *)
            -   rename n into a_next.
                simpl in *.
                pose proof (ll_fst_found_snd_found' a st a_next H_a_in_st) as H_found_prev.
                destruct H_found_prev as [a_prev H_found_prev].
                rewrite H_found_prev in H_remove_eq.
                inversion H_remove_eq as [H_remove_eq'].
                clear H_remove_eq. rename H_remove_eq' into H_remove_eq.
                now apply ll_remove_coh_lem.
            (* a is not in st *)
            -   inversion H_remove_eq as [H_remove_eq']. clear H_remove_eq.
                rewrite <- H_remove_eq'.
                now apply remove_not_found.
        Qed.

        Lemma remove_owner_coh'_inv : forall a st e,
            remove_owner_ll a st = Err e ->
            remove_owner_arr a (state_morph_inv st) = Err e.
        Proof.
            intros * H_remove.
            now apply ll_remove_failure in H_remove.
        Qed.

        Lemma nodup_state_morph_some' : forall st a_snd n, 
            FMap.find a_snd st = Some n ->
            exists i, in_dec N.eq_dec a_snd (ll_to_arr st) = left i.
        Proof.
            intros * H_snd_in.
            destruct (in_dec N.eq_dec a_snd (ll_to_arr st)) eqn:H_dec;
            try now exists i.
            now apply (nodup_state_morph_some'_aux) in H_snd_in.
        Qed.

        Lemma nodup_state_morph_none' : forall st a_snd, 
            FMap.find a_snd st = None ->
            exists n, in_dec N.eq_dec a_snd (ll_to_arr st) = right n.
        Proof.
            intros * H_snd_out.
            destruct (in_dec N.eq_dec a_snd (ll_to_arr st)) eqn:H_dec;
            try now exists n.
            now apply (nodup_state_morph_none'_aux a_snd st) in H_snd_out.
        Qed.

        Lemma swap_owners_coh_inv : forall a_fst a_snd st st' acts,
            swap_owners_ll a_fst a_snd st = Ok (st', acts) ->
            swap_owners_arr a_fst a_snd (state_morph_inv st) = Ok (state_morph_inv st', acts).
        Proof.
            intros * H_swap.
            unfold swap_owners_ll, swap_owners_arr, state_morph_inv in *.
            destruct (FMap.find a_snd st) eqn:H_snd_in.
            +   pose proof (nodup_state_morph_some' st a_snd n H_snd_in) as H_left.
                destruct H_left as [i H_left].
                rewrite H_left.
                now inversion H_swap.
            +   pose proof (nodup_state_morph_none' st a_snd H_snd_in) as H_right.
                destruct H_right as [n H_right].
                rewrite H_right.
                destruct (FMap.find a_fst st) eqn:H_found.
                rename n into a_next.
                (* a_fst is owner *)
                -   simpl in *.
                    apply ll_fst_found_snd_found' in H_found as H_found'.
                    destruct H_found' as [a_prev H_found'].
                    rewrite H_found' in H_swap.
                    inversion H_swap.
                    clear H0 H1.
                    f_equal. apply pair_lem. split; auto.
                    now apply ll_to_arr_swap.
                (* a_fst is not owner *)
                -   inversion H_swap.
                    rewrite <- H0.
                    clear H0 H1 H_swap.
                    now rewrite swap_idempotent'.
        Qed.

        Lemma swap_owners_coh'_inv : forall a_fst a_snd st e,
            swap_owners_ll a_fst a_snd st = Err e ->
            swap_owners_arr a_fst a_snd (state_morph_inv st) = Err e.
        Proof.
            intros * H_swap.
            now apply ll_swap_failure in H_swap.
        Qed.

        (* this is true under invariants *)
        Lemma state_morph_iso : forall st, state_morph (state_morph_inv st) = st.
        Proof.
            intro.
            unfold state_morph, state_morph_inv.
            apply ll_to_arr_rev.
        Qed.

        (* this is true under invariants *)
        Lemma state_morph_iso_inv : forall st, state_morph_inv (state_morph st) = st.
        Proof.
            intro.
            unfold state_morph, state_morph_inv.
            induction st.
            (* base case *)
            -   apply empty_arr_transform.
            (* inductive step *)
            -   rewrite ll_to_arr_cons.
                now rewrite IHst.
        Qed.

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


    Section NoDup.
        Lemma nodup_empty : NoDup empty_array.
        Proof. now constructor. Qed.

        Lemma nodup_add : forall a prev_state new_state new_acts,
            add_owner_arr a prev_state = Ok (new_state, new_acts) ->
            NoDup prev_state -> NoDup new_state.
        Proof.
            intros * H_add H_nodup.
            unfold add_owner_arr in H_add.
            destruct (in_dec N.eq_dec a prev_state) in H_add; try inversion H_add.
            now apply NoDup_cons.
        Qed.

        Axiom nodup_remove_aux : forall (l : list N) (n : N),
            NoDup l -> NoDup (List.remove N.eq_dec n l).

        Lemma nodup_remove : forall a prev_state new_state new_acts,
            remove_owner_arr a prev_state = Ok (new_state, new_acts) ->
            NoDup prev_state -> NoDup new_state.
        Proof.
            intros * H_remove H_nodup.
            inversion H_remove as [[H_remove0 H_remove1]].
            now apply nodup_remove_aux.
        Qed.

        Axiom nodup_swap_aux : forall a_fst a_snd prev_state n,
            in_dec N.eq_dec a_snd prev_state = right n -> 
            NoDup prev_state -> 
            NoDup (map (fun o : N => if (o =? a_fst)%N then a_snd else o) prev_state).

        Lemma nodup_swap : forall a_fst a_snd prev_state new_state new_acts,
            swap_owners_arr a_fst a_snd prev_state = Ok (new_state, new_acts) ->
            NoDup prev_state -> NoDup new_state.
        Proof.
            intros * H_swap H_nodup.
            unfold swap_owners_arr in H_swap.
            destruct (in_dec N.eq_dec a_snd prev_state) eqn:H_dup in H_swap;
            inversion H_swap as [[H_states H_acts]];
            try now rewrite <- H_states.
            clear H_swap H_acts.
            now apply (nodup_swap_aux a_fst a_snd prev_state n).
        Qed.

    End NoDup.

    Section NoDuplicates.
    
        Definition no_duplicates_arr (st : owners_arr) : Prop := NoDup st.

        (* assuming some no_duplicates predicate on linked lists ... *)
        Axiom no_duplicates_ll : forall (st : owners_ll), Prop.
        (* e.g. you can cycle through the list and return to SENTINEL *)

        (* ... that carries over state_morph_inv ... *)
        Axiom nodup_carried : forall cstate_arr cstate_ll,
            no_duplicates_arr cstate_arr -> 
            cstate_arr = state_morph_inv cstate_ll -> 
            no_duplicates_ll cstate_ll.
    
    End NoDuplicates.


    (* proved by contract induction *)
    Theorem no_duplciates_arr bstate caddr :
        reachable bstate -> 
        env_contracts bstate caddr = Some (C_arr : WeakContract) ->
        (* *)
        exists (cstate : owners_arr), contract_state bstate caddr = Some cstate /\
        (* *)
        no_duplicates_arr cstate.
    Proof.
        intros reachable_st contract_at_caddr.
        unfold no_duplicates_arr in *.
        contract_induction; auto; intros.
        (* Please establish the invariant after deployment of the contract *)
        -   simpl in init_some.
            unfold init_arr in init_some.
            inversion init_some.
            now apply nodup_empty.
        (* Please reestablish the invariant after a nonrecursive call *)
        -   simpl in receive_some.
            unfold receive_arr in receive_some.
            destruct msg; try inversion receive_some.
            destruct e eqn:H_msg.
            (* addOwner *)
            +   now apply (nodup_add a prev_state new_state new_acts).
            (* removeOwner *)
            +   now apply (nodup_remove a prev_state new_state new_acts).
            (* swapOwners *)
            +   now apply (nodup_swap a_fst a_snd prev_state new_state new_acts).
        (* Please reestablish the invariant after a recursive call *)
        -   simpl in receive_some.
            unfold receive_arr in receive_some.
            destruct msg; try inversion receive_some.
            destruct e eqn:H_msg.
            (* addOwner *)
            +   now apply (nodup_add a prev_state new_state new_acts).
            (* removeOwner *)
            +   now apply (nodup_remove a prev_state new_state new_acts).
            (* swapOwners *)
            +   now apply (nodup_swap a_fst a_snd prev_state new_state new_acts).
        (* Please prove your facts *)
        -   solve_facts.
    Qed.

    (* proved above *)
    Axiom no_duplciates_rr_aux : forall cstate_arr,
        cstate_reachable C_arr cstate_arr -> no_duplicates_arr cstate_arr.

    (* proved by morphism induction *)
    Theorem no_duplciates_ll bstate caddr (trace : ChainTrace empty_state bstate) : 
        (* Forall reachable states with contract at caddr, *)
        env_contracts bstate caddr = Some (C_ll : WeakContract) ->
        (* cstate is the state of the contract AND *)
        exists cstate_ll, contract_state bstate caddr = Some cstate_ll /\
        (* cstate_ll has no duplicate owners *)
        no_duplicates_ll cstate_ll.
    Proof.
        intros c_at_caddr.
        pose proof (left_cm_induction f_inv bstate caddr trace c_at_caddr)
        as H_cm_ind.
        destruct H_cm_ind as [cstate_ll [contr_cstate_ll [cstate_arr [reach H_cm_ind]]]].
        exists cstate_ll.
        repeat split; auto.
        cbn in H_cm_ind.
        assert (no_duplicates_arr cstate_arr) as H_nodup by (now apply no_duplciates_rr_aux).
        now apply (nodup_carried cstate_arr cstate_ll).
    Qed.
        
End Specification.

End ContractOptimization.