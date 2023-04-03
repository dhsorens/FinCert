(* the specification of the Dexter2 contract, an AMM which trades along xy = k *)

(* TODO *)

From PhD.Specifications.FA2Spec Require FA2Spec.
From PhD.Specifications.StructuredPoolsSpec Require Import StructuredPoolsSpec.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
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


(*  *)
Section ImportSP.
Context { Base : ChainBase } 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    `{Msg_Spec Msg}  `{Setup_Spec Setup}  `{State_Spec State} `{Error_Spec Error}
    {contract : Contract Setup Msg State Error}.

(* Context { is_sp : is_structured_pool contract }.*)

End ImportSP.