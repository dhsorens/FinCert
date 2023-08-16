(* A theory of AMMs and DeFi, embedded in Coq 
    This is an outline of future work that leverages morphisms, bisimulations,
    and meta specifications to create a theory of AMMs and DeFi, embedded in Coq.

    Below is a rough sketch of what is needed, and a rough outline of 
    what development of a formalized theory of DeFi might look like.
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

Import ListNotations.

(* What is needed for a theory of DeFi:
    - Process-algebraic semantics which build off the bigraph encoding in 
        FinCert.Meta.ContractSystems
    - Formalizations and axiomatizations of key building blocks of DeFi, 
        including:
        - Token contracts (FA2, FA1.2, etc.)
        - AMMs (a la Dexter2)
        - other kinds of DEXs such as auctions
        - etc.

    With these we can build a theory of AMMs and DeFi in roughly the 
    following structure:
*)


Section Primitives.

(* a formal definition of key primitives and atomic abstractions such as:
    - swaps
    - swap rate
    - exchange rate
    - liquidity provider
    - liquidity
*)


End Primitives.


Section Properties.

(* a formal derivation of key properties, such as:
    - demand sensitivity 
    - incentive consistency
    - positive trading cost
    - zero-impact liquidity change
*)

End Properties.