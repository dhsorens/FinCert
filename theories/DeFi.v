(* A theory of AMMs in DeFi, embedded in Coq 

    We will roughly follow the structure of the following paper:
    A Theory of Automated Market Makers in DeFi
    - https://arxiv.org/pdf/2102.11350.pdf
    - https://github.com/blockchain-unica/defi-workbench/blob/main/ListAMM/amm.ml

    Some stated goals of this prev work:
    - ``The core of our theory is an abstract operational model of the interactions
        between users and AMMs, which can be concretised by instantiating 
        the economic mechanisms.''
    - `` We exploit our theory to formally prove a set of fundamental properties of AMMs,
        characterizing both structural and economic aspects.''
*)

From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Sets.Ensembles.
From Coq Require Import ZArith.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Permutation.
From Coq Require Import FunctionalExtensionality.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From FinCert.Meta Require Import ContractMorphisms.
From FinCert.Meta Require Import ContractSystems.
From FinCert.Meta Require Import Bisimulation.
From FinCert.Specifications Require Import Token.
From FinCert.Specifications Require Import AMM.

Import ListNotations.

Section DeFi.
Context { Base : ChainBase }.

(* section 2 *)
Section FormalModel.

Section AMMSystem.

(* token and AMM contracts *)
Context { amm_setup amm_msg amm_state amm_error : Type } { amm_other : Type }
    `{Serializable amm_setup}  `{Serializable amm_msg}
    `{Serializable amm_state} `{Serializable amm_err}
    { amm_contract : Contract amm_setup amm_msg amm_state amm_err}
    { amm_contract_is_amm : @is_amm Base amm_setup amm_msg amm_state amm_err
        _ _ _ _  amm_contract }
    (* *)
    { lp_setup lp_msg lp_state lp_err : Type } { lp_other : Type }
    `{Serializable lp_setup}  `{Serializable lp_msg}
    `{Serializable lp_state} `{Serializable lp_err}
    `{@token_msg_spec Base lp_msg lp_other}
    `{@token_state_spec Base lp_state}
    { lp_token : Contract lp_setup lp_msg lp_state lp_err}
    { lp_contract_is_token : @is_token Base lp_setup lp_msg lp_state lp_err 
        _ _ _ _ lp_other _ _ lp_token}.

Definition amm_sys_init := nest amm_contract lp_token.

End AMMSystem.




(* state can transition with: deposit, swam, redeem *)
(* Deposit *)
Section Deposit.
(* token changes *)
(* AMM changes *)

End Deposit.


(* Swap *)
Section Swap.
(* token changes *)
(* AMM changes *)

End Swap.


(* Redeem *)
Section Redeem.
(* token changes *)
(* AMM changes *)

End Redeem.



End FormalModel.


(* Section 3 *)
Section Primitives.

(* token prices *)


(* exchange rates *)


(* slippage *)


(* net worth of a user ... *)


(* a formal definition of key primitives and atomic abstractions such as:
    - swaps
    - swap rate
    - exchange rate
    - liquidity provider
    - liquidity
*)


End Primitives.


(* Section 4 *)
Section Properties.

(* a formal derivation of key properties, such as:
    - demand sensitivity 
    - incentive consistency
    - positive trading cost
    - zero-impact liquidity change
*)

End Properties.

(* Sections 5, 6, 7 *)



(* proofs that the properties given here are invariant under bisimulation *)
Section IsoInvariant.



End IsoInvariant.

End DeFi.