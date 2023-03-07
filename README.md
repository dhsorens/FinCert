# Formal Verification of Financial Smart Contracts

This repository is one of two that houses the code of my PhD thesis, the other being my [fork of ConCert](https://github.com/differentialderek/phd-thesis-ConCert-fork), which is imported as a Git submodule.
This repository is designed to be self-contained, but can also be used as a companion to the text of my thesis, [which can be found here](thesis.pdf).

The goal of this repository is to build up theories and tools for reasoning rigorously about financial smart contracts. We use meta-theoretic reasoning techniques, which means that we have the notion of a *metaspecification*, or a specification of a specification.

A metaspecification is used to reason about:
- a financial smart contract's economic properties, opening the door to rigorously encode theories of decentralized finance within ConCert,
- smart contract upgrades, where we specify and reason about how a contract *specification* changes over the course of upgrades,
- systems of financial smart contracts, where we build theory to encode the semantics of process algebras in ConCert.