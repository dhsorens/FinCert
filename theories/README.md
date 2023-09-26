# Theories 

This subdirectory contains the theoretical tools we use to target meta properties of smart contracts.
The tools housed here include contract morphisms, 
bisimulations, and bigraphs.

We give a (very) short summary here, but for full details, please see the thesis text [which can be found here](../sorensen-phd-thesis.pdf).

## Contract Morphisms
Contract morphisms are functions between smart contracts that relate their 
structureal and computational properties.
Because contracts in ConCert are given by a pair of functions, 
`init` and `receive`, a contract morphism between contracts `C1` and `C2` is 
a pair of functions between each contract's `init` and `receive` functions,
respectively.

```
          inputs (receive C1) ->  inputs (receive C2)
                |                       |                  
                v                       v                  
          outputs (receive C1) -> outputs (receive C1)              
```

A contract morphism can be used in proof and specification of a smart
contract. They can:
-   specify upgrades (see [the upgrade specification example](../examples/ContractMorphisms/specifyUpgrade/))
-   transport Hoare properties of partial correctness (see [Hoare example](../examples/ContractMorphisms/transportHoare/))
-   be used to prove [one contract backwards compatible with another](../examples/ContractMorphisms/backwardsCompatible/)
-   deconstruct a [contract's upgradeability properties](../examples/ContractMorphisms/upgradeable/), separating it into its immutable and mutable parts.

In the [contract morphisms module](ContractMorphisms.v) we also introduce a generic technique to use a contract morphism with ConCert's custom tactic, `contract_induction`.

If two contract morphisms `f : C1 -> C2` and `g : C2 -> C1` compose each way to the identity morphism, we say that `C1` and `C2` are *isomorphic*.
This means that `C1` and `C2` are isomorphic, or equivalent, in some sense.
Of course, a bisimulation is the most influential notion of equivalence between processes.

## Bisimulation

A bisimulation is an isomorhpism of contract (or system) traces. 
To establish a bisimulation of contracts `C1` and `C2`, we need a function `st_morph` between their respective storage types and a function between contract steps (how a contract moves forward) such that:
1. `st_morph` sends initial states of `C1` to initial states of `C2`, and 
1. if `C1` can step from states `st1` to `st2`, then `C2` can step from `(st_morph st1)` to `(st_morph st2)`

Given any execution trace of `C1`, this gives us a corresponding trace of `C2`. If `st_morph` has an inverse that satisfies the properties above, then this gives us a *bisimulation* between contracts `C1` and `C2`.
This means that execution traces are in one-to-one correspondence under an *isomorphism of contract traces*.

An isomorphism of contracts produces a bisimulation of their traces.

This is formalized in the [bisimulation module](Bisimulation.v).

## Considering Contract Systems

In practice, when writing or verifying a smart contract, we care about the behavior of multiple contracts simultaneously. In the [contract systems module](ContractSystems.v), we define a data structure for systems of contracts that lets us consider some contracts "nested within" others.

Like for contracts, systems of contracts have a notion of system morphism and system bisimulation.

## Future Work: A Formalized Theory of AMMs and DeFi

The theoretical tools of metaspecification, contract morphisms, contract systems, and bisimulation, lay the foundation for a formalized theory of AMMs and DeFi in ConCert, which we outline in the [DeFi module](DeFi.v).