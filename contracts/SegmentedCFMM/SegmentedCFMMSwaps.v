From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From FinCert.Meta Require Import ContractMorphisms.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.
From Coq Require Import Ensembles.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.
(* *)
From FinCert.Contracts Require Import SegmentedCFMMTypes.
(* errors *)
(* consts *)
From FinCert.Contracts Require Import SegmentedCFMMMath.
(* helpers *)

Import ListNotations.
Open Scope N_scope.
Open Scope string.

Section SegmentedCFMMSwaps.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.


(*
Note [Rounding the swap result]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

When calculating how many tokens to give the user for a swap, we can either round the
amount up (using `ceildiv`) or down (using `floordiv`) to the nearest integer.

Rounding it up would mean we'd sometimes give the user ~1 extra token.
Over time, this effect could compound and slowly drain the contract's balance faster than expected.
This, in turn, would mean some Liquidity Providers would not be able to liquidate their positions.

Furthermore, rounding it up would open the door to exploits.
Imagine a scenario where, at the current exchange rate, it costs 20 Y tokens to buy 1 X token.
A user could simply trade in 1 Y token, and receive 0.05 X tokens.
0.05 would be rounded up to 1, and the user would make an easy 1900% profit.

To prevent this, we must round it down.

For similar reasons, we also round up the amount of tokens deposited in the pool
*)

(*
  `calc_new_cur_tick_index` uses `floor_log_half_bps_x80` to calculate
  the delta (`cur_tick_index_delta`) we need to add to the `cur_tick_index`.

  However, when a very small change in `sqrt_price` occurs, `cur_tick_index_delta` might be
  small enough that it gets rounded down to 0.

  For example, assuming liquidity=1,000,000, and the contract is at index 0, the current `sqrt_price` should be:
    $ ligo repl cameligo
    > #use "ligo/main.mligo";;
      #use "ligo/defaults.mligo";;
      let cur_sqrt_price = half_bps_pow(0, default_ladder);;
      cur_sqrt_price;;
    < record[x80 -> +1208925819614629174706176]
  Depositing 10 Y tokens will move the price as follows:
    > let new_sqrt_price = sqrt_price_move_y 1000000n (half_bps_pow(0, default_ladder)) 10n;;
      new_sqrt_price;;
    < record[x80 -> +1208937908872825320997924]
  In this instance, `floor_log_half_bps_x80` would round the `cur_tick_index_delta` down to 0:
    > floor_log_half_bps_x80(new_sqrt_price, cur_sqrt_price, 0n);;
    < 0
  This means that placing many small swaps would slowly move the `sqrt_price` upwards,
  but the `cur_tick_index` would always be stuck without moving (due to all the deltas being rounded down to 0).

  To avoid `cur_tick_index` being stuck, we check whether `sqrt_price_new` has moved beyond
  the price for `cur_tick_index + 1`.
  If it has, then we need to bump up `cur_tick_index` by 1 to unstuck it.

  ---

  Similarly, in some edge cases, `floor_log_half_bps_x80` may end up rounding the `cur_tick_index_delta` up!
  Depositing 50 Y tokens will move the price as follows:
    > let new_sqrt_price = sqrt_price_move_y 1000000n (half_bps_pow(0, default_ladder)) 50n;;
  Which sits between the sqrt_price for ticks 0 and 1, so we would
  expect `cur_tick_index_delta` to be 0 and `cur_tick_index` to stay at 0.
    > half_bps_pow(0, default_ladder) <= new_sqrt_price && new_sqrt_price < half_bps_pow(1, default_ladder);;
    < true(unit)
  However, it is so close to the sqrt_price of tick 1 that `floor_log_half_bps_x80` ends up overshooting and rounds
  the `cur_tick_index_delta` up to 1.
    > floor_log_half_bps_x80(new_sqrt_price, cur_sqrt_price, 0n);;
    < 1

  In this case, we check whether `sqrt_price_new` is below the price for `cur_tick_index`.
  If it is, we decrement `cur_tick_index` by 1.

  ---

  There are yet scenarios where incrementing/decrementing by 1 may not be enough.

  For example, consider the following scenario:
    > let cur_tick_index = {i = -1296};;
      let cur_sqrt_price = { x80 = 1133128297864886536622580n };;
  We can verify that `cur_sqrt_price` indeed falls in the correct range:
    > half_bps_pow(cur_tick_index.i, default_ladder) <= cur_sqrt_price
      && cur_sqrt_price < half_bps_pow(cur_tick_index.i + 1, default_ladder);;
    < true(unit)
  Now let's say we execute a X-to-Y swap that moves the price down to:
    > let new_sqrt_price = { x80 = 1111358172275591244112129n };;
  floor_log_half_bps_x80 would give us the following new tick index:
    > let cur_tick_index_delta = floor_log_half_bps_x80(new_sqrt_price, cur_sqrt_price, too_big_price_change_err);;
      let cur_tick_index_new = {i = cur_tick_index.i + cur_tick_index_delta };;
      cur_tick_index_new;;
    < record[i -> -1685]
  However, `new_sqrt_price` does NOT fall in this range:
    > half_bps_pow(cur_tick_index_new.i, default_ladder) <= new_sqrt_price
      && new_sqrt_price < half_bps_pow(cur_tick_index_new.i + 1, default_ladder);;
    < false(unit)
  Incrementing -1685 by 1 would not be sufficient either. In this case, we have to increment it by 2:
    > let cur_tick_index_new = {i = cur_tick_index_new.i + 2};;
      half_bps_pow(cur_tick_index_new.i, default_ladder) <= new_sqrt_price
      && new_sqrt_price < half_bps_pow(cur_tick_index_new.i + 1, default_ladder);;
    < true(unit)
*)

Definition fix_cur_tick_index
  (p : tick_index * x80nat * ladder) : tick_index :=
  let '(cur_tick_index, sqrt_price_new, l) := p in 
  todo.


(* Calculates the new `cur_tick_index` after a given price change. *)
Definition calc_new_cur_tick_index
  (cur_tick_index : tick_index)
  (sqrt_price_old : x80nat)
  (sqrt_price_new : x80nat)
  (l : ladder): tick_index :=
  let cur_tick_index_delta :=
    floor_log_half_bps_x80(sqrt_price_new, sqrt_price_old, too_big_price_change_err) in
  let cur_tick_index_new := build_tick_index (cur_tick_index.(i) + cur_tick_index_delta) in
    fix_cur_tick_index(cur_tick_index_new, sqrt_price_new, l).


(* Helper function for x_to_y, recursively loops over ticks to execute a trade. *)
Definition x_to_y_rec (p : x_to_y_rec_param) : x_to_y_rec_param := todo.


Definition y_to_x_rec (p : y_to_x_rec_param) : y_to_x_rec_param := todo.


(* Get amount of X spent, Y received, and updated storage. *)
Definition update_storage_x_to_y (s : storage) (dx : nat) : (nat * nat * storage) := todo.




(** Entrypoint function definitions *)

(* Trade up to a quantity dx of asset x, receives dy *)
Definition fn_x_to_y
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : x_to_y_param) : result :=
    (* check_deadline *)
    (* update_storage_x_to_y *)
    (* x_transfer *)
    (* y_transfer *)
    todo.
    (* emits op_recv_x and op_send_y, s_new *)

(* Trade up to a quantity dy of asset y, receives dx *)
Definition fn_y_to_x
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : y_to_x_param) : result :=
    todo.


(* Trade X with X' in a different contract. *)
Definition fn_x_to_x_prime
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : storage)
    (p : x_to_x_prime_param) : result :=
    todo.



End SegmentedCFMMSwaps.