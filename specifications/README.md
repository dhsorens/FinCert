# Financial Contract Specifications

This is a subdirectory for abstract specifications of financial smart contracts.
At the present, it only houses the structured pools specification and metaspecification; however, as other financial smart contracts have already been specified and verified in ConCert, we hope to add to this repository in order to grow a strong theory of financial smart contracts, including AMMs and DeFi.

The structured pool specification has two parts:
1. The **specification** of the structured pool contract, and 
1. The **metaspecification**, which considers an abstract contract satisfying the specification and reasons about its properties from there.

Metaspecifications can draw on a theory of AMMs and DeFi to formulate correct economic properties, or use theoretical tools such as bisimulations or contract morphisms.

We expect future contract specifications and metaspecifications added here to follow that same pattern, in order to have a well-specified and formally verified library of token and other contract standards.

NB there is an FA2 specification file present in this repository, but it only contains the relevant types to an FA2 contract which the structured pool specification uses.