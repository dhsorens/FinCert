(* MINIMAL FA2 TYPE DEFINITION

  Here we have provisionally included just the types relevant to an FA2 contract.

  We do this for this repository because, while the FA2 contract has been formalized,
  and is important for the formalization of structured pools, we did not do that 
  formalization.

  Thus we exclude the full specification of an FA2 contract and include only
  the relevant types needed to specify a structured pool contract, which are the
  entrypoint/interface types.
*)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From Coq Require Import ZArith_base.

Section FA2Types.
  Context `{BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  (* the transfer entrypoint *)
  Record transfer_to := {
    to_ : Address;
    transfer_token_id : N;
    amount : N
  }.
  Record transfer_data := {
    from_ : Address;
    txs : list transfer_to
  }.

  (* the mint entrypoint *)
  Record mint_data := {
    mint_owner : Address;
    mint_token_id : N;
    qty : N
  }.
  Definition mint : Type := list mint_data.

  (* the retire entrypoint *)
  Record retire_tokens_data := {
    retiring_party : Address;
    retire_token_id : N;
    retire_amount : N;
  }.
  Definition retire : Type := list retire_tokens_data.

  Inductive entrypoint :=
  | Transfer (txs : list transfer_data) (** transfer tokens *)
  | Mint (_ : mint) (** mint credits *)
  | Retire (_ : retire) (** retire credits *).

  (* begin hide *)
  Section Serialization.
    Global Instance transfer_to_serializable : Serializable transfer_to :=
      Derive Serializable transfer_to_rect <Build_transfer_to>.

    Global Instance transfer_data_serializable : Serializable transfer_data :=
      Derive Serializable transfer_data_rect <Build_transfer_data>.

    Global Instance mint_data_serializable : Serializable mint_data :=
      Derive Serializable mint_data_rect <Build_mint_data>.

    Global Instance retire_tokens_data_serializable : Serializable retire_tokens_data := Derive Serializable retire_tokens_data_rect <Build_retire_tokens_data>.

    Global Instance entrypoint_serializable : Serializable entrypoint :=
      Derive Serializable entrypoint_rect <
        Transfer,
        Mint,
        Retire >.

  End Serialization.
  (* end hide *)

End FA2Types.