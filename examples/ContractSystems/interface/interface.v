From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From FinCert.Meta Require Import ContractMorphisms.
From FinCert.Meta Require Import ContractSystems.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.

From FinCert.Meta Require Import ContractMorphisms.
From ConCert.Execution Require Import ContractSystems.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

(** An example of a system of contracts, where an backend contract is nested 
    with an interface contract. The tree structure would be something like:
    
        C_interface
             /
         C_backend

*)

(* TODO *)