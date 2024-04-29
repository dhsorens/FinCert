
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

Import ListNotations.
Open Scope N_scope.
Open Scope string.

Section SegmentedCFMMTypes.
Context { Base : ChainBase }.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* TODO *)
Axiom todo : forall {A}, A.


(** Type Definitions **)
Definition timestamp : Type := N. (* TODO! *)
Definition ligo_contract : Type -> Type := todo.


(** From types.mligo *)
(* set_position *)
(* Keeps a positive value with -2^80 precision. *)
Record x80nat := { x80n : N }.

(* Keeps a value with -2^128 precision. *)
Record x128 := { x128z : Z }.

(* Keeps a positive value with -2^128 precision. *)
Record x128nat := { x128n : N }.

Record balance_nat      := {x : N ; y : N}.
Record balance_nat_x128 := {x128n' : x128nat ; y128n' : x128nat}.
Record balance_int_x128 := {x128z' : x128    ; y128z' : x128}.

Record tick_index := build_tick_index {i : Z}.

(* FA2 related types *)
Definition position_id := N.
Definition token_id := N.

Record balance_request_item := {
    owner : Address ;
    token_id' : position_id ;
}.

Record balance_response_item := {
    request : balance_request_item ;
    balance : N ;
}.

Record balance_request_params := {
  requests : list balance_request_item ;
  callback : ligo_contract (list balance_response_item) ;
}.

Record transfer_destination := { 
    to_ : Address ;
    token_id'' : position_id ;
    amount : N ;
}.

Record transfer_item := {
    from_ : Address ;
    txs : list transfer_destination ;
}.

Definition transfer_params := list transfer_item.


Record operator_param := {
    owner' : Address ;
    operator : Address ;
    token_id''' : position_id ;
}.

Inductive update_operator :=
  | Add_operator (p : operator_param)
  | Remove_operator (p : operator_param).

Definition update_operators_param := list update_operator.

Record tick_state := {
    (* Index of the previous initialized tick.
        Here we diverge from the article, and effectively store a doubly-linked
        list of initialized ticks for speed-up
        (while the article proposes storing a bitmap for this purpose).
    *)
    prev : tick_index ;

    (* Index of the next initialized tick. *)
    next : tick_index ;

    (* Total amount of liquidity to add to the contract's global liquidity when
        this tick is crossed going up.
        (i.e. when the current tick index `i_c` becomes greater than this tick),
        or subtracted when the tick is crossed going down.
    *)
    liquidity_net : Z ;

    (* Numbers of positions with an edge at the given tick.
        Used for garbage collection.
    *)
    n_positions : N ;

    (* When the current tick index `i_c` is below this tick, this field tracks
        the overall number of seconds `i_c` spent above or at this tick.
        When `i_c` is above or equal to this tick, it tracks the number of
        seconds `i_c` spent below this tick.

        This field is updated every time `i_c` crosses this tick.

        Here we assume that, during all the time since Unix epoch start till
        the moment of tick initialization, i_c was below this tick
        (see equation 6.25 of the uniswap v3 whitepaper).
        So we actually track the number of seconds with some additive error Δ,
        but this Δ remains contant during the lifetime of the tick. Ticks
        created at different moments of time will have different Δ though.

        As example, let's say the tick was initialized at 1628440000 timestamp;
        then `seconds_outside` can be initialized with the same timestamp.
        If i_c crossed this tick 5 seconds later, this `seconds_outside` will
        be set respectively to 5.
        If i_c crossed this tick back 3 seconds later, we will get
        `1628440000 + 3 = 1628440003`
        (effectively this will be computed as `cur_time - last seconds_outside =
        1628440008 - 5 = 1628440003`).

        This field helps to evaluate, for instance, how many seconds i_c
        has spent in an any given ticks range.
    *)
    seconds_outside : N ;

    (* Tick indices accumulator i_o, it keeps track of time-weighted sum of
        tick indices, but accounts them only for "outside" periods.
        For the intuition for "outside" word, see `seconds_outside`.
    *)
    tick_cumulative_outside : Z ;

    (* Overall number of fees f_o that were accumulated during the period
        when the current tick index i_c was below (or above) this tick.

        For intuition for "outside" word, see `seconds_outside`.
       *)
    fee_growth_outside : balance_nat_x128 ;

    (* Seconds-weighted 1/L value accumulator s_lo, it accounts only for
        "outside" periods. For intuition for "outside" word, see `seconds_outside`.

        This helps us to implement liquidity oracle.
    *)
    seconds_per_liquidity_outside : x128nat ;

    (* sqrt(P) = sqrt(X/Y) associated with this tick. *)
    sqrt_price : x80nat
}.


(* We need some proofs to make the finite map *)
Section FMapTypeThings.
    Global Instance decidable_tick_index : stdpp.base.EqDecision tick_index := todo.
    Global Instance countable_tick_index : countable.Countable tick_index := todo.
End FMapTypeThings.

Definition tick_map : Type := FMap tick_index tick_state.

Record position_state := {
    (* Position edge tick indices *)
    lower_tick_index' : tick_index ;
    upper_tick_index' : tick_index ;
    (* The position's owner.
        By default - position's creator, but ownership can be transferred later.
    *)
    owner'' : Address ;
    (* Position's liquidity. *)
    liquidity' : N ;
    (* Total fees earned by the position at the moment of last fees collection for this position.
        This helps to evaluate the next portion of fees to collect.
    *)
    fee_growth_inside_last : balance_int_x128 ;
}.

(* Map containing Liquidity providers. *)
Definition position_map := FMap position_id position_state.

(* What we return when someone requests for the values of cumulatives. *)
Record cumulatives_value := { 
    tick_cumulative' : Z ; (* CHANGED *)
    seconds_per_liquidity_cumulative : x128nat ;
}.

(* Tick index cumulative *)
Record tick_cumulative := {
    (* The time-weighted cumulative value. *)
    sum : Z ;
    (* Tick index value at the beginning of the block. *)
    block_start_value : tick_index ;
}.

(* Seconds per liquidity cumulative *)
Record spl_cumulative := {
    (* The time-weighted cumulative value. *)
    sum' : x128nat ;
    (* Liquidity value at the beginning of the block. *)
    block_start_liquidity_value : N ;
}.

Record timed_cumulatives := {
    time : timestamp ;
    tick : tick_cumulative ;
    spl : spl_cumulative ;
}.

(*  TODO 
Definition init_timed_cumulatives : timed_cumulatives := {
    time := (0 : timestamp) ; (* Should not really matter *)
    tick := { sum = 0; block_start_value = {i = 0} } ;
    spl  := { sum = {x128 = 0n}; block_start_liquidity_value = 0n }
    }.
*)

(* Extendable ring buffer with time-weighted 1/L cumulative values. *)
Record timed_cumulatives_buffer := {
    (* For each index this stores:
    // 1. Cumulative values for every second in the history of the contract
    //    till specific moment of time, as well as last known value for
    //    the sake of future linear extrapolation.
    // 2. Timestamp when this sum was registered.
    //    This allows for bin search by timestamp.
    //
    // Indices in the map are assigned to values sequentially starting from 0.
    //
    // Invariants:
    // a. The set of indices that have an associated element with them is continuous;
    // b. Timestamps in values grow strictly monotonically
    //    (as well as accumulators ofc); *)
    map : FMap N timed_cumulatives ;

    (* Index of the oldest stored value. *)
    first : N ;

    (* Index of the most recently stored value. *)
    last : N ;

    (* Number of actually allocated slots.
    //
    // This value is normally equal to `last - first + 1`.
    // However, in case recently there was a request to extend the set of
    // stored values, this var will keep the demanded number of stored values,
    // while values in the map past `last` will be initialized with garbage.
    //
    // We need to have initialized slots with trash because when the size of
    // the map increases, someone has to pay for the storage diff.
    // And we want it to be paid by the one who requested the extension. *)
    reserved_length : N ;
}.

(* TODO
let init_cumulatives_buffer (extra_reserved_slots : nat) : timed_cumulatives_buffer =
    // Fill [0..n] slots with init values
    let rec fill_map (n, map : nat * (nat, timed_cumulatives) big_map) : (nat, timed_cumulatives) big_map =
        let map = Big_map.add n init_timed_cumulatives map in
        match is_nat(n - 1) with
        | None -> map
        | Some n_dec -> fill_map(n_dec, map)
        in
    { map = fill_map(extra_reserved_slots, (Big_map.empty : (nat, timed_cumulatives) big_map))
    ; first = 0n
    ; last = 0n
    ; reserved_length = extra_reserved_slots + 1n
    }
*)

(* TZIP-16 metadata map *)
Definition metadata_map := FMap string byte.

Record set_position_param := {
    lower_tick_index   : tick_index ;
    upper_tick_index   : tick_index ;
    lower_tick_witness : tick_index ;
    upper_tick_witness : tick_index ;
    liquidity : N ;
    deadline''' : timestamp ; (* CHANGED *)
    maximum_tokens_contributed' : balance_nat ; (* CHANGED *)
}.

(* update_position *)
Record update_position_param := {
    position_id' : position_id ; (* CHANGED *)
    liquidity_delta : Z ;
    to_x : Address ;
    to_y : Address ;
    deadline'''' : timestamp ; (* CHANGED *)
    maximum_tokens_contributed'' : balance_nat ; (* CHANGED *)
}.


(* get position info *)
Record position_index := {
    owner''' : Address ;
    lower_tick_index'' : tick_index ; (* CHANGED *)
    upper_tick_index'' : tick_index ; (* CHANGED *)
}.

Record position_info := {
    liquidity_position : N ; (* changed from liquidity *)
    index : position_index;
}.

Record get_position_info_param := (* [@layout:comb] *)
{
    position_id'' : position_id; (* CHANGED *)
    callback' : ligo_contract position_info;
}.


(* snapshot_cumulatives_inside *)
Record cumulatives_inside_snapshot := {
    tick_cumulative_inside : Z ;
    seconds_per_liquidity_inside : Z ;
    seconds_inside : Z ;
}.

Record cumulatives_inside_snapshot_param := {
    lower_tick_index''' : tick_index ; (* CHANGED *)
    upper_tick_index''' : tick_index ; (* CHANGED *)
    callback'' : ligo_contract cumulatives_inside_snapshot ;
}.

(* observe *)
Definition oracle_view_param := list cumulatives_value.

Record observe_param := (* [@layout:comb] *)
{
    times : list timestamp ;
    callback''' : ligo_contract oracle_view_param ; (* CHANGED *)
}.

(* *)
Record increase_observation_count_param := {
    added_observation_count: N;
}.


Section FMapTypeThings.
    Global Instance decidable_operator_param : stdpp.base.EqDecision operator_param := todo.
    Global Instance countable_operator_param : countable.Countable operator_param := todo.
End FMapTypeThings.

Definition operators := FMap operator_param unit.

Record constants := {
    fee_bps : N ;
    ctez_burn_fee_bps : N ;
    x_token_id : token_id ;
    y_token_id : token_id ;
    x_token_address : Address ;
    y_token_address : Address ;
    tick_spacing : N ;
}.

(* See defaults.mligo for more info *)
Record fixed_point := { v : N ; offset : Z }.
Record ladder_key := { exp : N ; positive : bool }.
Section FMapTypeThings.
    Global Instance decidable_ladder_key : stdpp.base.EqDecision ladder_key := todo.
    Global Instance countable_ladder_key : countable.Countable ladder_key := todo.
End FMapTypeThings.

Definition ladder := FMap ladder_key fixed_point.






(* storage definition *)
Record storage := {
    (* Virtual liquidity, the value L for which the curve locally looks like x * y = L^2. *)
    liquidity'' : nat ;

    (* Square root of the virtual price, the value P for which P = x / y. *)
    sqrt_price' : x80nat ;

    (* Index of the highest tick corresponding to a price less than or equal to sqrt_price^2,
        does not necessarily corresponds to a boundary.
        Article's notation: i_c, tick.
    *)
    cur_tick_index : tick_index ;

    (* The highest initialized tick lower than or equal to i_c. *)
    cur_tick_witness : tick_index ;

    (* The total amount of fees that have been earned per unit of virtual liquidity (L),
        over the entire history of the contract.
    *)
    fee_growth : balance_nat_x128 ;

    (* States of all initialized ticks. *)
    ticks : tick_map ;

    (* States of positions (with non-zero liquidity). *)
    positions : position_map ;

    (* Cumulative values stored for the recent timestamps. *)
    cumulatives_buffer : timed_cumulatives_buffer ;

    (* TZIP-16 metadata. *)
    metadata : metadata_map ;

    (* Incremental position id to be assigned to new position. *)
    new_position_id : position_id ;

    (* FA2-related *)
    operators' : operators ;

    (* Constants for options that are settable at origination *)
    constants' : constants ;

    (* Exponents ladder for the calculation of 'half_bps_pow' *)
    ladder' : ladder;
}.



Section SerializableThings.
    Global Instance storage_ser : Serializable storage := todo.
End SerializableThings.


(* x_to_y *)
Record x_to_y_param := {
    dx : nat ;
    deadline : timestamp ;
    min_dy : nat ;
    to_dy : Address ;
}.

Record x_to_y_rec_param := {s : storage ; dx'' : nat ; dy'' : nat}.

(* y_to_x *)
Record y_to_x_param := {
    dy : nat ;
    deadline' : timestamp ; (* CHANGED *)
    min_dx : nat ;
    to_dx : Address ;
}.

Definition y_to_x_rec_param := x_to_y_rec_param.

(* x_to_x_prime *)
Record x_to_x_prime_param := {
    dx' : N ; (* CHANGED *)
    x_prime_contract : ligo_contract y_to_x_param ;
    deadline'' : timestamp ; (* CHANGED *)
    min_dx_prime : N ;
    to_dx_prime : Address ;
}.

(* FA2 related types *)
Inductive call_FA2_param :=
  | Balance_of (p : balance_request_params)
  | Transfer (p : transfer_params)
  | Update_operators (p : update_operators_param).


(* Error codes are here: https://github.com/tezos-checker/segmented-cfmm/blob/master/docs/error-codes.md *)
Definition error := N.

Section ErrorCodes.
    (**
        Invalid input error codes
     **)

    (* Invalid witness. The witness must refer to an initialized tick that is below or equal to the supplied tick. *)
    Definition invalid_witness_err : error := 100.

    (* The action would apply too big of a change to the price, which is not allowed. We assume that the amount of X or Y tokens in the contract should not change by more than 30% at once (in some circumstances, a larger change may be allowed). *)
    Definition too_big_price_change_err : error := 101.

    (* The action would put the price out of bounds. Used tick indices should remain within `[-1048575; 1048575]` range, and, respectively, amount of one token type in the pair should not exceed `exp(0.0001)^1048575 ≈ 3.46 * 10^45` times the amount in the other token. *)
    Definition price_out_of_bounds_err : error := 102.

    (* Swap has expired: now > deadline. *)
    Definition past_deadline_err : error := 103.

    (* Threshold on amount of bought tokens violated: `dx` received < `min_dx` or `dy` received < `min_dy`. *)
    Definition smaller_than_min_asset_err : error := 104.

    (* User provided tick is not initialized. *)
    Definition tick_not_exist_err : error := 105.

    (* The amount of tokens that needs to be transferred to the contract is higher than `maximum_tokens_contributed`. *)
    Definition high_tokens_err : error := 106.

    (* The X prime contract address provided is not a segmented-cfmm contract. *)
    Definition invalid_x_prime_contract_err : error := 107.

    (* Some of the timestamps passed to the `observe` entrypoint are too far back in the past. *)
    Definition observe_outdated_timestamp_err : error := 108.

    (* Some of the timestamps passed to the `observe` entrypoint are yet in the future. *)
    Definition observe_future_timestamp_err : error := 109.

    (* When setting a new position, `upper_tick_index` must be strictly greater than `lower_tick_index`. When observing cumulative values at range, `upper_tick_index` must be greater or equal than `lower_tick_index`. *)
    Definition tick_order_err : error := 110.

    (* Liquidity of a position went below zero. *)
    Definition position_liquidity_below_zero_err : error := 111.

    (* Tick indexes must be a multiple of the tick spacing. *)
    Definition incorrect_tick_spacing_err : error := 112.

    (* Contract call also transfers some XTZ; this is not allowed, it would be stuck. *)
    Definition non_zero_transfer_err : error := 113.



    (** 
        Contract configuration error codes
     **)

    (* The `x_token_address` or `y_token_address` has no transfer entrypoint. *)
    Definition asset_transfer_invalid_entrypoints_err : error := 200.

    (* The `x_token_address` or `y_token_address` has no `update_operator` entrypoint. *)
    Definition asset_update_operator_invalid_entrypoints_err : error := 201.

    (* The `x_token_address` or `y_token_address` has no `approve` entrypoint. *)
    Definition asset_approve_invalid_entrypoints_err : error := 202.



    (** 
        Internal error codes
     **)

    (* Generic impossible error. *)
    Definition internal_impossible_err : error := 300.

    (* Tick is not initialized. *)
    Definition internal_tick_not_exist_err : error := 301.

    (* Time now is smaller than epoch time. *)
    Definition internal_epoch_bigger_than_now_err : error := 302.

    (* The `fee_bps` is initialized to be higher than 10000 (100%). *)
    Definition internal_fee_more_than_100_percent_err : error := 303.

    (* Unexpected price direction movement after sqrt_price_move_x. *)
    Definition internal_bad_sqrt_price_move_x_direction : error := 304.

    (* Unexpected price direction movement after sqrt_price_move_y. *)
    Definition internal_bad_sqrt_price_move_y_direction : error := 305.

    (* Flip for `fee_growth_outside` failed. (This is an invariant of the contract). *)
    Definition internal_flip_fee_growth_outside_err : error := 306.

    (* Thrown when `(p.dx - dx_consumed)` or `(p.dy - dy_consumed)` is not nat. *)
    Definition internal_307 : error := 307.

    (* Liquidity of a tick went below zero. *)
    Definition internal_liquidity_below_zero_err : error := 308.

    (* Thrown when `(p.dx - r.dx)` is not nat. *)
    Definition internal_309 : error := 309.

    (* Thrown when `s.cur_tick_index.i >= upper_tick_index.i` and `(s.fee_growth.x - upper_tick.fee_growth_outside.x)` (or `y`) is not nat. *)
    Definition internal_311 : error := 311.

    (* Thrown when `s.cur_tick_index.i < lower_tick_index.i` and `(s.fee_growth.x - lower_tick.fee_growth_outside.x)` (or `y`) is not nat. *)
    Definition internal_312 : error := 312.

    (* Number of positions underflow. *)
    Definition internal_position_underflow_err : error := 313.

    (* Thrown when `(fee_growth_inside.x - position.fee_growth_inside_last.x)` is not nat. *)
    Definition internal_316 : error := 316.

    (* Thrown when `(fee_growth_inside.y - position.fee_growth_inside_last.y)` is not nat. *)
    Definition internal_317 : error := 317.

    (* Thrown when `s.cur_tick_index.i < p.lower_tick_index.i` and the `sqrt_price` happened not to grow monotonically with tick indices (This is an invariant of the contract). *)
    Definition internal_sqrt_price_grow_err_1 : error := 318.

    (* Thrown when `p.lower_tick_index.i <= s.cur_tick_index.i && s.cur_tick_index.i < p.upper_tick_index.i` and the `sqrt_price` happened not to grow monotonically with tick indices (This is an invariant of the contract). *)
    Definition internal_sqrt_price_grow_err_2 : error := 319.

    (* Thrown when `seconds_outside` is negative. *)
    Definition internal_negative_seconds_outside_err : error := 320.

    (* Failed to access a value in time-weighted i_c cumulative sums buffer. *)
    Definition internal_bad_access_to_observation_buffer : error := 321.

    (* Some issue with binary search in `observe` entrypoint. *)
    Definition internal_observe_bin_search_failed : error := 322.

    (* Attempt to garbade collect a tick with non-zero liquidity net. *)
    Definition internal_non_empty_position_gc_err : error := 323.

    (* Flip of `seconds_per_liquidity_outside` failed. (This is an invariant of the contract). *)
    Definition internal_flip_seconds_per_liquidity_outside_err : error := 324.

    (* Position creation/change unexpectedly transferred tokens to someone *)
    Definition internal_unexpected_income_err : error := 325.

    (* Price became negative when crossing a tick *)
    Definition internal_negative_price : error := 326.

End ErrorCodes.


Definition result : Type := ResultMonad.result (storage * list ActionBody) error.

End SegmentedCFMMTypes.