
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From FinCert.Meta Require Import ContractMorphisms.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.
(* *)
From FinCert.Contracts Require Import SegmentedCFMM.
From FinCert.Specifications Require Import SegmentedCFMMSpec.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

Section SegmentedCFMMCorrect.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* TODO a proof that the segmented CFMM contract is correct wrt its spec *)


End SegmentedCFMMCorrect.