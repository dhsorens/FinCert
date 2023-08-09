(* A theory of AMMs and DeFi, embedded in Coq 
    This is an outline of future work that leverages morphisms, bisimulations,
    and meta specifications to create a theory of AMMs and DeFi, embedded in Coq.
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

(*

Define **desirable economic properties**

- start with some model of "what an AMM is" -- can be in terms of one contract, or drawing on abstract specifications, e.g. the token specifications

- not only do we have a specification (& metaspec) of a specific AMM, but we can 
    **further abstract** from there to prove properties of AMMs

- you need contraction over the link graph to really do this ... this is very hard.

USE THESE TO STUDY DEXTER2 FROM BEFORE

*)