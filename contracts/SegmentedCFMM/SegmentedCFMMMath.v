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
From FinCert.Contracts Require Import SegmentedCFMMTypes.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

Section SegmentedCFMMMath.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.



Definition floor_log_half_bps_x80 (p : x80nat * x80nat * N) : Z := 
    let '(x, y, out_of_bounds_err) := p in 
    todo.


End SegmentedCFMMMath.