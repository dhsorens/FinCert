# Fixing a Bug With Contract Morphisms

In this example, we verify that a new contract `C'` fixes a bug in `C` with a contract morphism.
`C` has a vulnerability of permissions: if the contract indicates that a given address does not have permissions to call `incr`, anyone can override that and give that wallet permissions just by calling `add_permissions`. Instead, the desired functionality is that once an address is blacklisted, they can never call `incr`.

We define a new contract `C'` and show that it fixes the bug in `C` without changing anything else by how we defined the morphism:
- the `CM_Init` component of the morphism is just the identity (so initialization is identical)
- the `CM_Recv` component of the morphism is also the identity, except that it rectifies the buggy execution trace: if one tries to call `add_permissions` to a blacklisted wallet it now returns an error.

The morphism specifies and verifies the structural relationship of a bug fix: these contracts behave identically except in the buggy execution trace.