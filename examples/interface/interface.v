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

(* an example which unifies an interface contract with its backend *)

Section Interface.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* Interface contract types definition *)
Definition setup : Type := Address.
Inductive  entrypoint := | incr (n : N) | decr (n : N) | reset.
Definition storage := Address.
Definition error := N.
Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

(* Backend contract types definition *)
Definition setup' := Address.
Inductive  entrypoint' := | incr' (n : N) | decr' (n : N) | reset'.
Record storage' := build_storage' { 
        interface_address : Address ; 
        counter : N ; }.
Definition error' := N.
Definition result' : Type := ResultMonad.result (storage' * list ActionBody) error'.

Section Serialization.
    Global Instance entrypoint_serializable : Serializable entrypoint := todo "".
    Global Instance storage_serializable : Serializable storage := todo "".
    Global Instance entrypoint'_serializable : Serializable entrypoint' := todo "".
    Global Instance storage'_serializable : Serializable storage' := todo "".
End Serialization.

(* Interface Contract *)
(* init function definition *)
Definition init (_ : Chain)
                (_ : ContractCallContext)
                (storage_contract : setup)
                : ResultMonad.result storage N := 
    Ok (storage_contract).

(* receive function definition *)
Definition receive (_ : Chain)
                (_ : ContractCallContext)
                (storage_contract : storage)
                (msg : option entrypoint)
                : result :=
    match msg with 
    | Some (incr n) => 
        let act_fwd := act_call storage_contract 0 (serialize (incr' n)) in 
        Ok (storage_contract, [ act_fwd ])
    | Some (decr n) => 
        let act_fwd := act_call storage_contract 0 (serialize (decr' n)) in 
        Ok (storage_contract, [ act_fwd ])
    | Some reset => 
        let act_fwd := act_call storage_contract 0 (serialize (reset')) in 
        Ok (storage_contract, [ act_fwd ])
    | None => Err 0
    end.

(* construct the contract *)
Definition interface : Contract setup entrypoint storage error := 
    build_contract init receive.


(* Backend Contract Definition *)
(* init function definition for C' *)
Definition init' (_ : Chain)
                (_ : ContractCallContext)
                (interface_address : setup')
                : ResultMonad.result storage' error' := 
    let init_storage := {| 
        interface_address := interface_address ;
        counter := 0 ; 
    |} in 
    Ok (init_storage).

(* receive function definition for C' *)
Definition receive' (_ : Chain)
                (ctx : ContractCallContext)
                (st : storage')
                (msg : option entrypoint')
                : result' :=
    (* check the call comes from the interface contract *)
    if address_eqb ctx.(ctx_from) st.(interface_address) then Err 0 else 
    (* execute the call *)
    match msg with 
    | Some (incr' n) => 
        let st' := {| 
            interface_address := st.(interface_address) ; 
            counter := st.(counter) + 1 ;
        |} in 
        Ok (st', [])
    | Some (decr' n) => 
        let st' := {| 
            interface_address := st.(interface_address) ; 
            counter := st.(counter) - 1 ;
        |} in 
        Ok (st', [])
    | Some reset' => 
        let st' := {| 
            interface_address := st.(interface_address) ; 
            counter := 0 ;
        |} in 
        Ok (st', [])    
    | None => Err 0
    end.

(* construct the contract *)
Definition backend : Contract setup' entrypoint' storage' error' := 
    build_contract init' receive'.

End Interface.


Section Monolithic.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* contract types definition for C'' *)
Definition setup'' := unit.
Inductive  entrypoint'' := | incr'' (n : N) | decr'' (n : N) | reset''.
Record storage'' := build_storage'' { counter'' : N ; }.
Definition error'' := N.
Definition result'' : Type := ResultMonad.result (storage'' * list ActionBody) error''.

Section Serialization.
    Global Instance entrypoint''_serializable : Serializable entrypoint'' := todo "".
    Global Instance storage''_serializable : Serializable storage'' := todo "".
End Serialization.

(* init function definition for C'' *)
Definition init'' (_ : Chain)
                (_ : ContractCallContext)
                (_ : setup'')
                : ResultMonad.result storage'' error'' := 
    let init_storage := {| 
        counter'' := 0 ; 
    |} in 
    Ok (init_storage).

(* receive function definition for C' *)
Definition receive'' (_ : Chain)
                (_ : ContractCallContext)
                (st : storage'')
                (msg : option entrypoint'')
                : result'' :=
    match msg with 
    | Some (incr'' n) => 
        let st'' := {| 
            counter'' := st.(counter'') + 1 ;
        |} in 
        Ok (st'', [])
    | Some (decr'' n) => 
        let st'' := {| 
            counter'' := st.(counter'') - 1 ;
        |} in 
        Ok (st'', [])
    | Some reset'' => 
        let st'' := {| 
            counter'' := 0 ;
        |} in 
        Ok (st'', [])    
    | None => Err 0
    end.

(* construct the contract *)
Definition mono : Contract setup' entrypoint' storage' error' := 
    build_contract init' receive'.

End Monolithic.


Section WeakEquivalence.

(* TODO *)


End WeakEquivalence.