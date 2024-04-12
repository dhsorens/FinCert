# FinCert: Formal Tools for Specifying Financial Smart Contracts

Financial smart contracts are *risk- and property-dense* and can be difficult to specify correctly. Indeed, practitioners of formal verification often say that writing a good specification is the hardest part of formal verification, as efforts of formal verification can be rendered null if the specification is incorrect.

This is an experimental repository whose aim is to develop formal tools with which we can better specify and verify financial smart contracts.



## Formal Tools and Frameworks

The formal tools and frameworks developed here so far are:

### Specifications and Metaspecifications

We introduce the notion of a *metaspecification*, which is a specification of a specification. Our core assertion here is that one way to evaluate the correctness of a specification is to formally prove things about it. This is the purpose of a metaspecification.

So far we have only done so on one contract, the [structured pool contract](specifications/StructuredPoolsSpec/StructuredPoolsSpec.v), which is an [experimental pooling contract](https://ieeexplore.ieee.org/abstract/document/10174866) designed for [tokenized carbon credits](https://ledger.pitt.edu/ojs/ledger/article/view/294). We hope to do more.

See related papers:
* Sorensen, D. (In)Correct Smart Contract Specifications. ICBC 2024.
* Sorensen, D. Structured Pools for Tokenized Carbon Credits. ICBC CryptoEx 2023.
* Sorensen, D. Tokenized Carbon Credits. Ledger, 2023.

### Contract Morphisms

We introduce a theoretical tool called a *contract morhpism* in the [contract morphisms module](theories/ContractMorphisms.v). This is a formal, structural relationship between smart contracts. In the `examples/` folder and accompanying [text of my PhD thesis](sorensen-phd-thesis.pdf) there are several examples of using contract morphisms to:
1. Reuse proofs and properties of previous contract versions when verifying a new contract,
1. Transport Hoare properties over a morphism,
1. Specifying upgrades in terms of previous versions,
1. Formally specifying backwards compatibility, and 
1. Formally define contract upgradeability via a decomposition into its upgradeability framework and version contracts.

We also use contract morphisms to establish the notion of a *contract bisimulation* in ConCert in the [bisimulation module](theories/Bisimulation.v), which shows a strong structural equivalence between contracts in ConCert and can, in principle, be used for optimizations.

See related paper:
* Sorensen, D. Towards Formally Specifying and Verifying Smart Contract Upgrades in Coq. FMBC 2024.

### Models of Contract Systems 

Finally, we model systems of contracts with bigraphs in the [contract system module](theories/Bisimulation.v). The aim of this is to be able to specify and formally reason about a system of contracts as if it were a single, monolithic contract. This could prevent incorrect specification of contract systems by separating the core, desired contract behavior from the specification of the contract system infrastructure (how contracts interact).

## Accompanying Text

This repository is designed to be self-contained, but can also be used as a companion to the text of my thesis, [which can be found here](sorensen-phd-thesis.pdf).

## Repository Organization

* The [theories](theories/) folder houses the formal tools, and has three main files:
    * [ContractMorphisms](theories/ContractMorphisms.v), which develops a theoretical tool called a *contract morphism*
    * [Bisimulation](theories/Bisimulation.v), which develops various notions of equivalences between contracts
    * [ContractSystems](theories/ContractSystems.v), which gives a data structure for iteratively building systems of contracts out of component pieces
    * It also has a file called [DeFi](theories/DeFi.v), which contains a roadmap for encoding a theory of DeFi and AMMs in ConCert, and which is in very early (read: nonexistent) stages.
* The [examples](examples/) folder houses examples of using the techniques mentioned above in verifying smart contracts


## Installing and Compiling

Clone the repository with the `--recursive` tag.
```
git clone git@github.com:dhsorens/FinCert.git --recursive
```

Navigate into the FinCert directory and run

```
opam switch create . 4.13.1 --repositories default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
```

Then navigate into the `ConCert` subdirectory and run
```
opam install ./coq-concert.opam --deps-only
```

These combined actions make a local opam switch for the FinCert directory and install all the necessary dependencies for ConCert.

Now navigate back to the root `FinCert/` directory, and make the Coq project.
```
make
```

(Note, you may run into problems if you make the ConCert project independently of FinCert.)