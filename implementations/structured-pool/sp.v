From FinCert.Specifications.StructuredPoolsSpec Require Import StructuredPoolsSpec.
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

Import ListNotations.
Open Scope N_scope.
Open Scope string.


(* an implementation of the structured pool contract *)
Section StructuredPoolImpl.
Context {Base : ChainBase}.
Axiom todo : forall {A}, A.

(* Contract type definitions *)
Definition sp_setup : Type := todo.
Definition sp_msg : Type := todo.
Definition sp_state : Type := todo.
Definition sp_err : Type := todo.
Definition other : Type := todo.

(* some key functions *)
Definition calc_delta_y : N -> N -> N := todo.
Definition calc_rx' : N -> N -> N -> N -> N -> N := todo.
Definition calc_rx_inv : N -> N -> N -> N -> N -> N := todo.

(* TODO change *)
Context `{Serializable sp_setup} `{Serializable sp_msg}
        `{Serializable sp_state} `{Serializable sp_err}.

Definition sp_init : Chain -> ContractCallContext -> sp_setup -> result sp_state sp_err := todo.

Definition sp_recv : Chain -> ContractCallContext -> sp_state -> option sp_msg -> result (sp_state * list ActionBody) sp_err := todo.


(* the structured pool contract definition *)
Definition sp_contract : @Contract Base sp_setup sp_msg sp_state sp_err H H0 H1 H2 := 
    build_contract sp_init sp_recv.


Section StructuredPoolCorrect.

Context `{@Msg_Spec Base sp_msg other}
        `{@Setup_Spec Base sp_setup}
        `{@State_Spec Base sp_state}
        `{@Error_Spec sp_err}.

Theorem sp_is_sp2 : @is_structured_pool _ _ _ _ _ _ _ _ _ _ _ _ _ calc_delta_y calc_rx' calc_rx_inv sp_contract.
Proof.
    unfold is_structured_pool.
    repeat split.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + unfold trade_entrypoint_check_2.
      admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
    (*  *)
    + admit.
Admitted.

End StructuredPoolCorrect.

End StructuredPoolImpl.