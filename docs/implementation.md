# Implementation at the proof-mode merge

Audited source: `e00f2867886b928e6cd420959cf39e0d3975cb8e`, 2026-09-30.

## Audit range

The checkout is the merge of `full-arend-native-proof-mode` into `main`.
The merge's first parent is `4117536` (the previous documentation update), and
its feature parent is `d54d403`. The feature history was rewritten: the merge
message records the original shared ancestor `e11edda`, whose source tree
matches the pre-merge `main` source tree at `4117536`. Consequently, a
merge-base query between the two parent histories does not identify the old
branch point. The delivered source changes are reviewed with:

```sh
git diff e00f286^1 e00f286 -- src proofmode-extension scripts arend.yaml
git log --oneline e00f286^2
```

The feature work establishes the counter and proof mode at `23c527e`, expands
the logical rules at `beced71`/`56be9a0`, migrates the counter and concurrency
proofs through the August commits, and finishes shared automation and nested
framing at `3379d17`. The final `d54d403` commit removes unnecessary files.
The merge retained the earlier documentation, which is why its original
proof-mode and String-support status was stale.

## Source map

Arend module names follow paths under `src/`: for example,
`iris.base_logic.lib.ghost_map` is
[`src/iris/base_logic/lib/ghost_map.ard`](../src/iris/base_logic/lib/ghost_map.ard).

| Layer | Modules and public entry points |
| --- | --- |
| Foundations | `stdpp.pmap`, `coPset`, `finite_coPset`, `namespaces`; `iris.algebra.ofe`, `cmra`, `cofe_solver`, `gmap`, `view`, and their constructions |
| Recursive propositions | `iris.base_logic.lib.gfunctors`, `iprop`, `own`; `iProp`, `inG`, `own`, allocation and update laws |
| Logic and invariants | `iris.base_logic.upred`, `iris.bi.*`, `wsat`, `wsat_alloc`, `wsat_sigma`, `fancy_updates`, `fancy_updates_mask`, `invariants` |
| Concrete program logic | `iris.program_logic.weakestpre`, `lifting`, `iris_sigma`, `adequacy` |
| Proof mode | `iris.proofmode.core`, `iris.proofmode.heap_lang`, and the virtual `iris.proofmode.Meta` supplied by `proofmode-extension/` |
| HeapLang | `iris_heap_lang.lang`, `lang_ectx`, `lang_subst`; `lib.syntax`, `lib.array`, `lib.spawn`, `lib.spawn_proof` |
| Clients | `examples.parallel_counter*`, `tests.generic_heap`, `tests.fact`, and focused `tests.*` modules |

The helper modules `gmap_functor`, `gmap_updates`, `gmap_view_functor`,
`fancy_updates_mask`, `wsat_alloc`, and `wsat_sigma` remain compilation
boundaries next to their parent abstractions. Library modules do not depend
on `tests` or `examples`.

## New ghost resources and logical support

| Module | Delivered API | Scope |
| --- | --- | --- |
| `iris.algebra.lib.frac_auth` | `frac_authR`, `frac_authUR`, authority/fragments, fragment composition, validity, agreement, `frac_auth_update_1` | Exclusive authority and owned positive fragment fractions; the full Rocq discarded/fractional-authority API and generic functor wrappers are not exposed. |
| `iris.algebra.lib.mono_nat` | `MaxNatUCMRA`, `mono_natR`, `mono_natUR`, `mono_nat_auth`, `mono_nat_lb`, validity, inclusion, weakening, `mono_nat_auth_update` | A view-based construction with `Qp` authority and persistent lower bounds. |
| `iris.base_logic.lib.ghost_map` | `ghost_mapSigma`, `ghost_mapGpreS`/`ghost_mapGS`, `ghost_map_auth`, `ghost_map_elem`, empty allocation, insertion, lookup, update, deletion | Reuses `gen_heap`'s gmap-view resource; public elements carry full ownership and authority uses `Qp`. |
| `iris.base_logic.lib.mono_nat` | `mono_natSigma`, `mono_natG`, `subG_mono_natG`, `mono_nat_auth_own`, `mono_nat_lb_own`, allocation and monotone update | Supplies the counter's persistent shard snapshots and sum bounds. |
| `iris.base_logic.lib.saved_pred` | `savedPredSigma`, `savedPredG`, `subG_savedPredG`, `saved_pred_own`, `saved_pred_alloc`, `saved_pred_discarded_persistent`, `saved_pred_agree` | Saved predicates with later agreement; this does not implement the entire Rocq `savedAnything`/`saved_prop` family. |

Discreteness lemmas for agreement, products, finite maps, functions, views,
and fractional fragments support `own_timeless`, `pointsto_timeless`, and
`ghost_map_auth_timeless`. These are used when opening counter invariants.
`big_sepM_delete` supplies map focusing; `pure_consequence_frame_ent`,
`persistent_consequence_frame_ent`, `pure_sep_l_elim`, and
`internal_eq_elim_r_ent` consolidate common logical steps.

[`iris.base_logic.notation`](../src/iris/base_logic/notation.ard) adds aliases
for `⊢`, `⊣⊢`, `∗`, `-∗`, `∧`, `∨`, `|>`, `<#>`, `<except_0>`, and `|==>`.
They elaborate to existing `ProperUPred` operations.

## HeapLang and weakest preconditions

`Name` is now `Nat`, with constructive `nameDecEq`. Lambda and recursive
substitution use this carrier; the old unresolved String equality and
arbitrary-result substitution helper are gone. Proof-mode labels are a
separate `PMName = List Nat` representation.

HeapLang adds natural-number addition/equality and location addition through
`BinOp`, contiguous allocation through `AllocN`, and fetch-and-add through
`FAA`. `Fork` produces a child thread. Context and substitution laws cover
these operations and prophecy expressions. `lib.syntax` provides `letE`,
`seqE`, application helpers, and `resolveProphE`.

`iris.program_logic.lifting` now exposes `wp_binop`, `wp_nat_add`,
`wp_nat_eq_true`/`wp_nat_eq_false`, `wp_loc_add`, `wp_fork`, `wp_faa`,
`wp_allocN`, and pure lambda/recursive/pair/projection/conditional rules.
`wp_new_proph`, `wp_resolve_store`, and `wp_resolve_skip` connect prophecy
ownership to observation-producing steps. The counter resolves a prophecy
around a skip expression through `resolveProphE`.

`pointsto_block` and `pointsto_array` in `gen_heap` express contiguous and
list-valued ownership. `pointsto_array_extract`/`pointsto_array_insert` focus
a cell; `pointsto_block_replicate` connects uniform allocation to arrays.
`iris_heap_lang.lib.array` packages location-index arithmetic and list
decomposition/replacement helpers used by the counter.

The masked WP layer adds `wp_atomic`, `wp_bupd`, and `wp_frame_r`.
`wp_atomic_inv_acc` opens invariants around strongly atomic operations;
its timeless/frame and existential variants support resource-preserving
atomic updates. These term-level rules also back proof-mode automation.

## Concurrency, adequacy, and the counter

`irisSigma` combines `wsatSigma`, `gen_heapSigma`, and `proph_mapSigma`.
`irisGS` includes world satisfaction, heap and prophecy resources, and a
fork postcondition. `ThreadStep`/`ThreadSteps` model scheduled execution;
`wp_thread_pool_step` and `wp_thread_pool_preservation` transport logical
resources across the pool.

`Adequate.adequate_result` proves the main thread's postcondition when it
returns. `Adequate.adequate_not_stuck` proves `ThreadPoolSafe` for every
reachable pool. `wp_adequacy_with_fork` additionally supplies
`fork_post_inhabited` to clients. These are partial-correctness and safety
results, not termination or fairness guarantees.

[`iris_heap_lang.lib.spawn_proof`](../src/iris_heap_lang/lib/spawn_proof.ard)
defines `spawnSigma`, `spawnG`, exclusive spawn tokens, `join_handle`,
`spawn_spec`, `join_spec`, and `par_spec`/`par_lam_spec`. Join polls an
invariant-protected heap cell; the token controls collection of its result.

| Counter module | Purpose and entry points |
| --- | --- |
| [`parallel_counter`](../src/examples/parallel_counter.ard) | Executable `msc_new_counter`, `msc_incr`, `msc_sum_loop`, `msc_read`, and `msc_closed_client`; prophecy decoding via `msc_proph_total` |
| [`parallel_counter_model`](../src/examples/parallel_counter_model.ard) | `frac_auth (agree Nat)` model, fractional fragments, allocation, replacement, and agreement |
| [`parallel_counter_ghost`](../src/examples/parallel_counter_ghost.ard) | `mscSigma`, `mscG`, and sub-signature witnesses |
| [`parallel_counter_proof`](../src/examples/parallel_counter_proof.ard) | Counter/shard invariants, pending/completed read requests, saved predicates, scan bounds, `msc_new_counter_spec`, `msc_incr_spec`, `msc_read_spec`, and client protocols |
| [`parallel_counter_client`](../src/examples/parallel_counter_client.ard) | Constructor-to-client composition, `msc_closed_client_wp`, concrete resource signature and initial state, `msc_closed_client_adequate` |

The closed client allocates two zeroed shards, runs two parallel workers that
each increment twice, joins them, and reads the counter. Its adequacy theorem
states that every returning execution yields `natV 4`, and every thread in
every reachable pool is a value or can step. The proofs now use shared
proof-mode operations for resource handling, invariant access, pure
evaluation, and WP sequencing.

## Examples and remaining scope

`tests.fact` now uses numeric binders and contains complete source terms for
`factorial_correct'` and `factorial_correct_Q`. It retains its example-local
fixed-heap compatibility stack in `tests.fact.heap` and
`tests.fact.program_logic`; it has not been migrated to generic `irisGS`.
`tests.generic_heap` exercises the canonical generic WP/Hoare path.

The core port and counter do not imply coverage of all upstream modules.
Still absent are libraries such as `ghost_var`, `mono_Z`, `na_invariants`,
and `cancelable_invariants`, much of the general `saved_prop` API, total WP
and total adequacy, and the full abstract Rocq language/typeclass surface.
Step indices remain natural numbers rather than an abstract `StepIndex`/`SI`
interface. HeapLang implements the operations needed by these clients, not
every upstream primitive. Rocq Ltac parsers are outside scope, while native
proof-mode functionality is now in scope and is documented separately.

## Verification

The merge audit counted **82 Arend source modules** and found **no explicit
`{?}` placeholders**. Focused suites include `tests.proofmode`,
`proofmode_env`, `proofmode_classes`, `proofmode_custom_instances`,
`proofmode_wp_pures`, `proofmode_wp_primitives`, `parallel_primitives`,
`prophecy`, `ghost_map`, `mono_nat`, `frac_auth`, `saved_pred`, and `notation`.
Proof-mode tests include rejected misuse via `fails`, not just positive
examples.

The subsequent [official/patched toolchain audit](typecheck-2026-09-30.md)
rebuilt both checkers and checked all 82 modules from source with the patched
variant. **80 passed; `tests.fact.program_logic` and `tests.fact` failed**
with 164 diagnostics and no goals. The current Iris core, native proof mode,
and parallel counter client passed. A fresh process loaded all 80 successful
module caches and reproduced the same factorial failures; the counter client
also passed a separate cache check. All 51 selected checker regression tests
passed. The official full source run exceeded its deadline; a complete
per-module source sweep passed 63 targets and timed out on 19 at a
120-second deadline per target.

The factorial failures include missing `State.usedProph` implementations,
outdated primitive-step applications, and a failed normalization equality.
They remain unresolved. Source inventory and dashboard mappings must not be
read as a whole-repository correctness claim. Older local audit notes and
benchmark timings describe earlier trees; use the linked audit's exact
revisions and logs for this merge.
