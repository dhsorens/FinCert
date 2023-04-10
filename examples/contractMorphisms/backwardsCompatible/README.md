# Proving Backwards Compatibility with Contract Morphisms 

This example shows how to specify and verify that a contract upgrade `C'` is backwards compatible with a previous version `C`. 

We will take the simple example of a pair of counter contracts: 
- `C` keeps a nat `n : N` in storage and has an `incr` entrypoint which increments its storage by one.
- `C'` is an upgrade of `C` which adds a `decr` entrypoint to `C`

How do we show that `C'` is backwards compatible? With a contract morphism.

We can define a simple morphism, which we do by specifying what old messages correspond to in the new contract:

```
Definition msg_morph (e : entrypoint) : entrypoint' := 
    match e with | incr _ => incr' tt end.
```

As the rest of the contract types, `setup`, `state`, and `error`, are identical to the old, and the new entrypoint `incr'` functions identicaly to `incr`, the old, we can get a contract morphism by defining the trivial functions 
```
Definition setup_morph : setup -> setup := id.
Definition state_morph : storage -> storage := id.
Definition error_morph : error -> error := id.
```
and then proving the coherence results `init_coherence` and `recv_coherence`.

After defining `f`, the most important result is that `f` is an *embedding*. This means that:
1. There is a copy of `C` in `C'`, which we identify by the image of `C` under `f`. Because `f` is injective (an embedding), the structure of `C` is fully preserved in `C'`.
1. `C'` is backwards compatible with `C`, and we know *exactly* what that means: the `incr'` entrypoint of `C'` is structurally identical to the `incr` entrypoint of `C`, so a message that would have gone to `C` can simply go to `C'` y way of `msg_morph`.