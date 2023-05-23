# Formal Verification of Financial Smart Contracts

This repository is one of two that houses the code of my PhD thesis, the other being my [fork of ConCert](https://github.com/differentialderek/phd-thesis-ConCert-fork), which is imported as a Git submodule.
This repository is designed to be self-contained, but can also be used as a companion to the text of my thesis, [which can be found here](thesis.pdf).

The goal of this repository is to build up theories and tools for reasoning rigorously about financial smart contracts. We introduce various new notions to reasoning about contracts, including:
1. a *metaspecification*, which is a specification of a specification, used to rigorously justify the strenth of a contract specification,
1. *contract morphisms*, which are formal, structural relationships between smart contracts, and 
1. various notions of *equivalences of contracts*, with which we can reason about bisimulations and process algebras.

Using these techniques we can reason about:
- a financial smart contract's *economic properties*, opening the door to rigorously encode theories of decentralized finance within ConCert,
- smart contract upgrades, using contract morphisms to codify the immutable and mutable (upgradeable) parts of a contract, and
- systems of financial smart contracts, which draws on the various notions of equivalences.

## Installing and Compiling

Clone the repository with the `--recursive` tag so that you include the submodule.
```
git clone git@github.com:differentialderek/phd-thesis.git --recursive
```

Go into the `phd-thesis-ConCert/` subdirectory, my fork of the ConCert codebase, and type `make`.
The first time you do this, this will take a little while.
```
cd phd-thesis-ConCert/
make
```

Now go back to the root `phd-thesis/` directory, and make the Coq project.
```
cd ../
make
```

This definitely compiles on MacOS with these versions:
```
The Coq Proof Assistant, version 8.15.1
compiled with OCaml 4.14.0
```

## Organization 

* the `specifications` folder houses various formalized specifications, including of structured pools, token contracts, and AMMs
* the `phd-thesis-ConCert` folder, the reasoning enginge of the repository, is a fork of ConCert with modifications to include contract morphisms and equivalences of contracts (including bisimulations)
* the `examples` folder houses examples of using the techniques mentioned above in verifying smart contracts
* the `implementations` folder is to house formally verified implementations of, *e.g.* token or AMM contracts (currently empty)
* the `theories` folder is to house theories, *e.g.* a theory of DeFi, built on top of ConCert (currently empty)