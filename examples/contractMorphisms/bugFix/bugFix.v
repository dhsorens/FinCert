From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractMorphisms.
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


(** A buggy contract *)
Section BuggyContract.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* contract types definition *)
Inductive entrypoint := 
    | incr
    | add_permissions (addr : Address).
Record storage := build_storage { n : N ; permissions : FMap Address bool ; }.
Definition setup := FMap Address bool.
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

(* derive serializable typeclass *)
Section Serialization.
    Global Instance storage_serializable : Serializable storage := 
    Derive Serializable storage_rect <build_storage>.

    Global Instance entrypoint_serializable : Serializable entrypoint := 
    Derive Serializable entrypoint_rect <incr, add_permissions>.
End Serialization.


(* an auxiliary function to see if an address has permissions *)
Definition has_permissions (addr : Address) (permissions : FMap Address bool) : bool := 
    match FMap.find addr permissions with 
    | Some b => b 
    | None => false 
    end.

(* init function definition *)
Definition init (_ : Chain)
                (_ : ContractCallContext)
                (init_permissions : setup)
                : ResultMonad.result storage N := 
    let init_state := {| n := 0 ; permissions := init_permissions ; |} in 
    Ok (init_state).

(* receive function definition *)
Definition receive (_ : Chain)
                (ctx : ContractCallContext)
                (storage : storage)
                (msg : option entrypoint)
                : result :=
    match msg with 
    | Some incr => 
        if has_permissions ctx.(ctx_from) storage.(permissions) then 
            let st := {| n := storage.(n) + 1 ; permissions := storage.(permissions) ; |} in 
            Ok (st, [])
        else Err 0
    | Some (add_permissions new_addr) => 
        if has_permissions ctx.(ctx_from) storage.(permissions) then 
            let st := {| 
                n := storage.(n) ; 
                permissions := 
                    FMap.update new_addr (Some true) storage.(permissions) ; |} in 
            Ok (st, [])
        else Err 0
    | None => Err 0
    end.

(* construct the contract *)
Definition C : Contract setup entrypoint storage error := 
    build_contract init receive.

End BuggyContract.


(** The fixed contract *)
Section BugFix.
    Context { Base : ChainBase }.
    Set Primitive Projections.
    Set Nonrecursive Elimination Schemes.


(* contract types definition *)
Definition entrypoint' := entrypoint.
Definition storage' := storage.
Definition setup' := setup.
Definition error' := error.
Definition result' := result.

(* init function definition *)
Definition init' (c : Chain)
                (ctx : ContractCallContext)
                (init_permissions : setup')
                : ResultMonad.result storage' N := 
    init c ctx init_permissions.

(* receive function definition *)
Definition receive' (_ : Chain)
                (ctx : ContractCallContext)
                (storage : storage')
                (msg : option entrypoint')
                : result :=
    match msg with 
    | Some incr => 
        if has_permissions ctx.(ctx_from) storage.(permissions) then 
            let st := {| n := storage.(n) + 1 ; permissions := storage.(permissions) ; |} in 
            Ok (st, [])
        else Err 0
    | Some (add_permissions new_addr) => 
        (* begin bug fix *)
        match FMap.find new_addr storage.(permissions) with 
        | Some _ => Err 0 
        | None => 
        (* end bug fix *)
            if has_permissions ctx.(ctx_from) storage.(permissions) then 
                let st := {| 
                    n := storage.(n) ; 
                    permissions := 
                        FMap.update new_addr (Some true) storage.(permissions) ; |} in 
                Ok (st, [])
            else Err 0
        end
    | None => Err 0
    end.

(* construct the contract *)
Definition C' : Contract setup' entrypoint' storage' error' := 
    build_contract init' receive'.

End BugFix.


Section BugFixCorrect.
Context { Base : ChainBase }.

(* InitCM component definition *)
Definition init_inputs : Chain * ContractCallContext * setup' 
    -> Chain * ContractCallContext * setup := id.
Definition init_outputs : ResultMonad.result storage' error' 
    -> ResultMonad.result storage error := id. 
Lemma init_commutes : forall x : Chain * ContractCallContext * setup',
    uncurry_3 (Blockchain.init C) (init_inputs x) = 
    init_outputs (uncurry_3 (Blockchain.init C') x).
Proof. auto. Qed.

Definition cm_init : InitCM C' C := {| 
    ContractMorphisms.init_inputs := init_inputs ; 
    ContractMorphisms.init_outputs := init_outputs ;
    ContractMorphisms.init_commutes := init_commutes ; |}.

(* RecvCM component definition *)
Definition recv_inputs 
    (x : Chain * ContractCallContext * storage' * option entrypoint') :
        Chain * ContractCallContext * storage * option entrypoint :=
    let '(c, ctx, storage, msg) := x in 
    match msg with 
    | Some (add_permissions new_addr) => 
        match FMap.find new_addr storage.(permissions) with 
        | Some _ => (c, ctx, storage, None)
        | _ => x
        end
    | _ => x 
    end.

Definition recv_outputs : ResultMonad.result (storage' * list ActionBody) error' -> 
    ResultMonad.result (storage * list ActionBody) error := id.


Lemma recv_commutes : 
    forall (x : Chain * ContractCallContext * storage' * option entrypoint'), 
        uncurry_4 (Blockchain.receive C) (recv_inputs x) = 
        recv_outputs (uncurry_4 (Blockchain.receive C') x).
Proof.
    intros. cbn.
    destruct x as [x msg']. destruct x as [x state']. destruct x as [c ctx].
    induction msg'; cbn; auto.
    induction a; cbn; auto.
    induction (FMap.find addr (permissions state')); cbn; auto.
Qed. 

Definition cm_recv := {|
    ContractMorphisms.recv_inputs := recv_inputs ; 
    ContractMorphisms.recv_outputs := recv_outputs ; 
    ContractMorphisms.recv_commutes := recv_commutes ;
|}.

(* contract morphism definition *)
Definition f : ContractMorphism C' C := {| 
    ContractMorphisms.cm_init := cm_init ; 
    ContractMorphisms.cm_recv := cm_recv ;
|}.

End BugFixCorrect.