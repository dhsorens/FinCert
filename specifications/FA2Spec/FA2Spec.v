(* an abstract FA2 token contract *)

From stdpp Require Import decidable.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From Coq.Init Require Import Byte.
From Coq Require Import String.


(* TODO: remove these definitions *)
From Coq Require Import String.
Axiom todo : string -> forall {A}, A.
Ltac todo s := exact (todo s).

(** * Contract storage types *)
Section Storage.
  Context `{BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  (** ** ConCert specific types *)
  Record Setup := { todo_ : N }.
  Definition Error : Type := N.

  (** ** Contract types *)
  Definition token_id_n : Type := N.
(*   Record owner := {
    token_owner : Address;
    owner_token_id : N
  }. *)
  Record token := {
    token_address : Address;
    token_id : N
  }.
  Definition owner : Type := (Address * N). (* TODO: Turn into record *)
(*   Global Instance owner_eq_dec : base.EqDecision owner := ltac:(solve_decision).
  Global Program Instance owner_countable : countable.Countable owner :=
    countable.inj_countable' (fun o => (o.(token_owner), o.(owner_token_id)))
                             (fun '(a, b) => Build_owner a b)
                             ltac:(reflexivity). *)

  Definition operator : Type := (Address * Address * N). (* TODO: Turn into record *)
  Record token_metadata := {
    metadata_token_id : N;
    metadata_token_info : FMap string (list byte) (* TODO: distinguish between map and big_map *)
  }.
  Definition contract_metadata : Type := FMap string (list byte).
  Record storage := {
    (** Oracle / admin : has minting permissions and can edit the contract's metadata *)
    oracle : Address;
    (** The ledger keeps track of who owns what token *)
    ledger : FMap owner N;
    (** An operator can trade tokens on behalf of the fa2_owner *)
    operators : FMap operator unit;
    (** Token metadata for each token type supported by this contract *)
    storage_token_metadata : FMap token_id_n token_metadata;
    (** Contract metadata *)
    metadata : FMap string (list byte)
  }.
  Definition result : Type := ResultMonad.result (storage * list ActionBody) Error.

  (* begin hide *)
  MetaCoq Run (make_setters storage).

  Section Serialization.
    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <Build_Setup>.

(*     Global Instance owner_serializable : Serializable owner :=
      Derive Serializable owner_rect <Build_owner>. *)

    Global Instance token_metadata_serializable : Serializable token_metadata := todo "".
      (*Derive Serializable token_metadata_rect <Build_token_metadata>.*)

    Global Instance storage_serializable : Serializable storage := todo "".
      (*Derive Serializable storage_rect <Build_storage>.*)
  End Serialization.
  (* end hide *)

    (* begin hide *)
    Section STDPPInstances.
    Global Instance token_eq_dec : base.EqDecision token := ltac:(solve_decision).
    Global Program Instance token_countable : countable.Countable token :=
      countable.inj_countable' (fun o => (o.(token_address), o.(token_id)))
                              (fun '(a, b) => Build_token a b)
                              ltac:(reflexivity).
    
    Declare Scope token_scope.
    Notation "x =? y" := (if token_eq_dec x y then true else false)
          (at level 70) : token_scope.
  End STDPPInstances.
  (* end hide *)
End Storage.

(** * Contract entrypoint types *)
Section EntrypointTypeDefinition.
  Context `{BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  Record transfer_to := {
    to_ : Address;
    transfer_token_id : N;
    amount : N
  }.
  Record transfer_data := {
    from_ : Address;
    txs : list transfer_to
  }.
  Record request := {
    request_token_owner : Address;
    request_token_id : N
  }.
  Record callback_data := {
    callback_request : request;
    callback_balance : N
  }.
  Record balance_of_data := {
    requests : list request;
    callback : Address (* TODO: model callback *)
  }.
  Record operator_data := {
    operator_owner : Address;
    operator_operator : Address;
    operator_token_id : N
  }.
  Inductive update_operator_data :=
  | Add_operator : operator_data -> update_operator_data
  | Remove_operator : operator_data -> update_operator_data.
  Definition update_operators_data : Type := list update_operator_data.
  Record mint_data := {
    mint_owner : Address;
    mint_token_id : N;
    qty : N
  }.
  Definition mint : Type := list mint_data.
  Record retire_tokens_data := {
    retiring_party : Address;
    retire_token_id : N;
    retire_amount : N;
    retiring_data : list byte
  }.
  Definition retire : Type := list retire_tokens_data.
  Record update_oracle_data := {
    new_oracle : Address
  }.
  Inductive entrypoint :=
  | Transfer (txs : list transfer_data) (** transfer tokens *)
  | Balance_of (_ : balance_of_data) (** query an address's balance *)
  | Update_operators (_ : update_operators_data) (** chanbge operators for some address *)
  | Mint (_ : mint) (** mint credits *)
  | Retire (_ : retire) (** retire credits *)
  | Add_token_id (_ : list token_metadata)
  | Update_contract_metadata (_ : contract_metadata)
  | Update_oracle (_ : update_oracle_data).

  (* begin hide *)
  Section Serialization.
    Global Instance transfer_to_serializable : Serializable transfer_to :=
      Derive Serializable transfer_to_rect <Build_transfer_to>.

    Global Instance transfer_data_serializable : Serializable transfer_data :=
      Derive Serializable transfer_data_rect <Build_transfer_data>.

    Global Instance request_serializable : Serializable request :=
      Derive Serializable request_rect <Build_request>.

    Global Instance callback_data_serializable : Serializable callback_data :=
      Derive Serializable callback_data_rect <Build_callback_data>.

    Global Instance balance_of_data_serializable : Serializable balance_of_data :=
      Derive Serializable balance_of_data_rect <Build_balance_of_data>.

    Global Instance operator_data_serializable : Serializable operator_data :=
      Derive Serializable operator_data_rect <Build_operator_data>.

    Global Instance update_operator_data_serializable : Serializable update_operator_data :=
      Derive Serializable update_operator_data_rect <Add_operator, Remove_operator>.

    Global Instance mint_data_serializable : Serializable mint_data :=
      Derive Serializable mint_data_rect <Build_mint_data>.

    Global Instance retire_tokens_data_serializable : Serializable retire_tokens_data := todo "".
      (*Derive Serializable retire_tokens_data_rect <Build_retire_tokens_data>.*)

    Global Instance update_oracle_data_serializable : Serializable update_oracle_data :=
      Derive Serializable update_oracle_data_rect <Build_update_oracle_data>.

    Global Instance entrypoint_serializable : Serializable entrypoint := todo "". (*
      Derive Serializable entrypoint_rect <
        Transfer,
        Balance_of,
        Update_operators,
        Mint,
        Retire,
        Add_token_id,
        Update_contract_metadata,
        Update_oracle >.*)
  End Serialization.
  (* end hide *)
End EntrypointTypeDefinition.

(** * Error codes *)
Section ErrorCodes.
  Local Open Scope N_scope.
  (** One of the specified token_ids is not defined within the FA2 contract *)
  Definition error_TOKEN_UNDEFINED : Error := 0.
  (** A token owner does not have sufficient balance to transfer tokens from owner's account *)
  Definition error_INSUFFICIENT_BALANCE : Error := 1.
  (** A transfer failed because of fa2_operatortransfer_policy == No_transfer *)
  Definition error_TX_DENIED : Error := 2.
  (** A transfer failed because fa2_operatortransfer_policy == fa2_ownertransfer and it is invoked not by the token owner *)
  Definition error_NOT_OWNER : Error := 3.
  (** A transfer failed because fa2_operatortransfer_policy == fa2_owneror_fa2_operatortransfer and it is invoked neither by the token owner nor a permitted operator *)
  Definition error_NOT_OPERATOR : Error := 4.
  (** update_operators entrypoint is invoked and fa2_operatortransfer_policy is No_transfer or fa2_ownertransfer *)
  Definition error_OPERATORS_UNSUPPORTED : Error := 5.
  (** The receiver hook failed. This error MUST be raised by the hook implementation *)
  Definition error_RECEIVER_HOOK_FAILED : Error := 6.
  (** The sender failed. This error MUST be raised by the hook implementation *)
  Definition error_SENDER_HOOK_FAILED : Error := 7.
  (** Receiver hook is required by the permission behavior, but is not implemented by a receiver contract *)
  Definition error_RECEIVER_HOOK_UNDEFINED : Error := 8.
  (** Sender hook is required by the permission behavior, but is not implemented by a sender contract *)
  Definition error_SENDER_HOOK_UNDEFINED : Error := 9.
  (** General catch-all for operator-related permission errors *)
  Definition error_PERMISSIONS_DENIED : Error := 10.
  (** A token ID can only be used once, error if a user wants to add a token ID that's already there *)
  Definition error_ID_ALREADY_IN_USE : Error := 11.
  (** A collision in storage *)
  Definition error_COLLISION : Error := 12.
End ErrorCodes.

(** * Auxiliary functions *)
Section AuxFunctions.
  Context `{BaseTypes : ChainBase}.
  
  (** ** Contract defs *)
  Definition update_balance {K : Type}
                            `{countable.Countable K}
                            (k : K)
                            (diff : Z)
                            (ledger : FMap K N)
                            : ResultMonad.result (FMap K N) Error :=
    do new_bal <-
      let old_bal := match FMap.find k ledger with | None => 0%N | Some b => b end in
      do _ <- throwIf ((Z.of_N old_bal) + diff <? 0)%Z error_INSUFFICIENT_BALANCE;
      Ok (Z.abs_N ((Z.of_N old_bal) + diff));
    Ok (FMap.update k (if new_bal =? 0 then None else Some new_bal)%N ledger).

  Definition is_operator (operator : operator)
                         `{countable.Countable FA2Spec.operator} (* TODO: remove later *)
                         (operators : FMap FA2Spec.operator unit) (* TODO: define set or find a set type *)
                         : bool :=
    FMap.mem operator operators.
End AuxFunctions.