# Financial Contract Specifications

This subdirectory houses specifications of various financial smart contracts.

<!-- what/why we want abstract specifications -->
Having specifications in isolation like this is useful for at least two reasons:
1. If a contract specification is abstracted as an isolated object, we can reason about it from various angles, including its economic and upgradeability properties, and how it acts within a system of contracts
1. Many financial smart contracts are designed to interact with other smart contracts which have a standard specification and interface, *e.g.* AMMs which are designed to intermediate trades between token contracts. If we have an abstracted specifications, we can reason rigorously about these interactions by assuming contracts which conform to the specification.

<!-- which ones do we have rn 
Thus far, we have the following "building block" contract specifications, which can be imported and used in implementing and reasoning about financial smart contracts:

- FA2, a [multi-asset token standard](https://gitlab.com/tezos/tzip/-/blob/master/proposals/tzip-12/tzip-12.md)
- Dexter2, a [formally verified AMM](https://dl.acm.org/doi/abs/10.1145/3573105.3575685) on the [Tezos](https://tezos.com/) blockchain
- Structured Pools, a pooling contract for [tokenized carbon credits](https://derekhsorensen.com/docs/sorensen-tokenized-carbon-credits.pdf)
-->
<!-- which ones do we have rn 

- FA1.2, an [approvable ledger token standard](https://gitlab.com/tezos/tzip/-/blob/master/proposals/tzip-7/tzip-7.md)

-->

## An Abstract Specification

TODO: design patterns for a specification; the structure of an abstract specification; how they are imported, etc; instructions for adding to this library of financial smart contracts.