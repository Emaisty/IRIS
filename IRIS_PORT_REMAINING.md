# IRIS Arend Port: Remaining Work

Last audited: 2026-08-22

This document records the remaining proof holes, missing Rocq IRIS APIs, and
unfinished roadmap phases. It distinguishes code that merely typechecks from a
roadmap point that is complete with its intended public interface.

## Current Summary

- The source tree contains **no explicit `{?}` holes**. Heap-language binders
  use the semantic `Name = Nat` carrier with decidable equality; all basic
  substitution laws are proved, and the formerly unsound arbitrary-result
  substitution helper has been removed.
- A1-A5 provide the main recursive-domain and generic ownership foundation,
  with only optional compatibility aliases described below.
- A7-A10 are implemented and pass both source and cached verification.
  `wsatΣ` packaging is complete and no longer has a conversion-performance
  blocker with the guarded PR #132 checker.
- The complete `BI` instance (`BILaterMixin` + all mixins) is in place:
  `BIuPredBI` in `src/iris/bi/updates.ard`, verified directly by the full build.
- **A11 is complete** with its full public API in the canonical
  `src/iris/base_logic/lib/invariants.ard`; the former numbered iteration fragments have been
  merged in dependency order. The minimal `Timeless` class remains in
  `src/iris/bi/derived_laws_later.ard`. Delivered: `inv_contractive`/`inv_ne`/
  `inv_proper`, `inv_alter`, `inv_iff`, `inv_alloc_open`, `inv_combine`,
  `inv_combine_dup_l`, `except_0_inv`, `inv_split_l`/`_r`/`inv_split`,
  `inv_acc_strong`, `inv_acc_timeless` (all typecheck; `inv_acc_strong` and the
  two `inv_combine*` are proved in sealed form). Proof-mode instances
  (`IsExcept0`/`IntoInv`/`IntoAcc`) remain out of scope (term-mode port).
- A12 is now the canonical program-logic stack in the Rocq-shaped hierarchy:
  `iris/base_logic/lib/gen_heap.ard` implements the generic heap resource and
  its allocation/update/lookup/init laws;
  `iris/program_logic/weakestpre.ard` implements the masked `iProp S` WP
  fixpoint; `iris/program_logic/lifting.ard` proves step readiness,
  reducibility, primitive/context/atomic lifting, and pure/load/store/alloc
  rules; `iris/program_logic/iris_sigma.ard` packages
  `wsatSigma ++ gen_heapSigma`; and `iris/program_logic/adequacy.ard` contains the
  two-resource bootstrap plus full scheduled thread-pool safety/value adequacy,
  including the fork-post witness package used by fork/join clients.
  The fixed-`HeapCMRA` compatibility logic needed by the deferred factorial
  client is consolidated in `src/tests/fact/program_logic.ard`.
- The required non-String A12 source is implemented, and the argument-first
  conversion change from [Arend PR #132](https://github.com/arend-lang/Arend/pull/132)
  makes `iris.program_logic.adequacy:init` and `iris.program_logic.adequacy:wp_adequacy` finish. The guarded follow-up
  prevents inference-state mutation and recursive re-entry; its focused tests,
  arend-lib dependency check, and the complete IRIS source/cache audit pass.
- The canonical public program-logic names are `wp`/`wp_*`, `ht`/`ht_*`, and
  `fupd_wp`. The temporary `iris_wp_*`/`iris_ht_*` prefixes were removed once
  the fixed-heap implementation was isolated under `tests.fact.program_logic`. Names
  such as `irisGS`, `iris_wsat`, and `iris_gen_heap` remain because they name
  Iris resource structures rather than duplicate WP operations.
- A13 is optional and has not been started.

## Candidate Patched Arend Checker

The current local candidate build is:

```text
~/Projects/Arend/cli/build/libs/cli-1.12.0-full.jar
```

It is Arend `v1.12.0` plus guarded PR #132, with the local v1.12 adaptation at
commit `b1a256cb6`; the current
jar SHA-256 is
`3839c7e71796db6561b5a64e52a8e90ca2889a71395301e82b6e2cc3e1cd11c2`.
`scripts/typecheck-all.sh` defaults to this jar and still accepts an explicit
`AREND_JAR` override. Detailed motivation, examples, commands, and measured
results are in `AREND_CONVERSION_EXAMPLES.md`.

**Do not treat this build as validated yet.** A cache-disabled build of the
whole project also recompiles arend-lib and exposes widespread inference and
termination regressions. The conversion optimization needs the ground/closed
term gate and failure rollback described in `AREND_CONVERSION_FIX.md` (or an
equivalent upstream-safe design), followed by a clean arend-lib and IRIS audit.

## Former String/Substitution Blocker — resolved

The compiler's legacy opaque `String` primitive is no longer used as the
semantic binder carrier. `iris_heap_lang.lang.Name` is `Nat`, so binder
equality computes and the substitution layer is constructive.

### 1. Decidable equality for names

File: `src/iris_heap_lang/lang.ard`

```arend
\func nameDecEq (x y : Name) : (x = y) `Or` (Not (x = y))
```

This is implemented using `NatSemiring.decideEq`.

### 2. Basic substitution lemmas

File: `src/iris_heap_lang/lang_subst.ard`

| Line | Definition | Required fact |
|---:|---|---|
| 14 | `subst_var_same` | Substitution replaces the matching variable. |
| 21 | `subst_var_ne` | Substitution preserves a distinct variable. |
| 27 | `subst_lam_same` | Substitution stops at a matching lambda binder. |
| 34 | `subst_lam_ne` | Substitution descends through a distinct lambda binder. |
| 40 | `subst_rec_same_f` | Substitution stops at the recursive function binder. |
| 47 | `subst_rec_same_x` | Substitution stops at the recursive argument binder. |
| 54 | `subst_rec_ne` | Substitution descends when both recursive binders differ. |

All seven laws are implemented by case analysis over `nameDecEq`.

### 3. `subst_by_string_decisions`

File: `src/iris_heap_lang/lang_subst.ard:105`

The former statement was:

```arend
\lemma subst_by_string_decisions (x : String) (v : Value) (e e' : Expr)
  : subst x v e = e' => {?}
```

This unsound statement has been removed. Concrete factorial substitutions now
reduce to `idp` after the numeric binder migration.

## Missing Foundation APIs

### A1: step-index wrapper

The required Nat-based step-index machinery and `DistLater` laws exist in
`src/iris/algebra/ofe.ard`. The optional Rocq-shaped `StepIndex`/`SI` wrapper described by
the roadmap is absent. Add it only if later ports require the abstract API;
the current semantic construction does not need it.

### A5: generic ownership API

`src/iris/base_logic/lib/own.ard` implements `inG`, `own`, validity, deterministic updates,
predicate-valued updates, allocation, unit ownership, and persistent ownership.

Completed (2026-07-19):

- `own_alloc_strong`: allocate a fresh name satisfying a predicate `P`, given a
  value-polymorphic freshness oracle (`∀ m, ∃ γ, m!!γ = None ∧ P γ`); yields
  `⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a`. Backed by the new
  `gmap_alloc_strong_updateP` in `lib/gmap_updates.ard`.
- `own_updateP` (the standard nondeterministic ownership wrapper,
  `own_update_ND`): `a ~~>: P → own γ a ⊢ |==> ∃ b, ⌜P b⌝ ∗ own γ b`, the
  separating-conjunction form derived from `own_updatePM`.

Still missing from the planned public surface:

- Rocq-compatible aliases/instances for `own_ne` and `own_persistent` if exact
  downstream API compatibility is desired. The corresponding semantics exist
  as `own_dist` and `own_core_persistent`.

### Complete concrete BI instance

Completed. `src/iris/bi/updates.ard` provides the later, persistence, and base mixins
and assembles `BIuPredBI`; the canonical definition is checked directly.

## A7: `wsat` Packaging (`wsatΣ` / `subG_wsatΣ`)

The semantic `wsatGS`, `wsat`, `ownI`, `ownE`, `ownD`, opening, closing, and
allocation laws are implemented and typecheck.

Packaging status (re-audited 2026-08-11, in `src/iris/base_logic/lib/wsat_sigma.ard`):

- `wsatSigma` (Rocq `wsatΣ`) — the concrete three-functor `gFunctors` — is
  defined and typechecks. It rests on new, independently verified functor
  infrastructure: `agreeRF`/`agreeRF_contractive` (`lib/gmap_view_functor.ard`),
  `constRF`/`constRF_contractive`/`mkGFunctor` (`lib/gFunctors.ard`), and
  `subG_inG` (`own.ard`).
- `subG_wsatSigma` (Rocq `subG_wsatΣ`) is present; its two constant components
  (`wsatGpreS_enabled`, `wsatGpreS_disabled`, over `coPset_disjR` / `gset_disjR`)
  are fully proved via `subG_inG` + `rFunctor_apply_constRF`.

`subG_wsatSigma` is complete and contains no hole. The invariant component is
transported by the proved `wsat_invR_eq`; the two constant components use
`rFunctor_apply_constRF`. Targeted, whole-module, serialized, and cached checks
all pass.

## A11: Invariant API — complete

The semantic core and all promised term-mode public laws are implemented in
`src/iris/base_logic/lib/invariants.ard`. This includes non-expansiveness,
properness, alteration/equivalence, open allocation, combination,
except-zero, strong/timeless accessors, and splitting. Rocq proof-mode instances remain
outside scope because this port has no proof-mode framework.

## A6/A12: Program Logic Retrofit

The required non-String portion of this phase is now implemented.

The compatibility layer `src/tests/fact/program_logic.ard` and its client
`src/tests/fact.ard` use:

- `ProperUPred (HeapCMRA Loc cnt Value)` instead of `iProp Σ`.
- A fixed `HeapCMRA` instead of heap ghost state selected through `inG`.
- `mkProperBUpd` in `wp_pre` instead of masked `mkProperFUpd`.
- No WP mask parameter.
- Direct heap authoritative ownership instead of a `gen_heapGS`-style class.

This is example-local compatibility code, not the canonical A12 implementation.

Status and remaining work:

1. **Done:** generic heap functor, `gen_heapGpreS`/`gen_heapGS`, authoritative
   interpretation, fractional points-to, lookup, allocation, update, and init.
2. **Done:** masked generic WP carrier, E/empty/E step transition,
   contractivity, fixpoint, unfolding, and value rule.
3. **Done:** non-value step readiness, reducibility, and the fundamental
   primitive-step lifting rule.
4. **Done/source-checked:** `irisSigma`/`irisGpreS` packaging (the combined
   `subG` witness is a known slow conversion check).
5. **Done:** full fixed-point postcondition monotonicity is proved via
   monotone finite approximants and the COFE limit (`wp_pre_mono`,
   `wp_approx_mono`, `wp_mono`). Same-mask fancy-update elimination
   (`fupd_wp`), the general evaluation-context bind theorem and all
   language context wrappers are complete. Generic pure-step, fractional load,
   full store, and allocation laws are implemented through the common
   mask-safe atomic lifting rule `wp_lift_atomic`.
6. **Implemented and verified with the canonical patched checker:**
   `adequacy.ard` combines
   `wsat_alloc` and `gen_heap_init`, packages their Set1 witnesses into one
   `irisGS`, proves sequential multi-step WP preservation and safety/value
   extraction, and closes the fancy-update soundness bridge. Official Arend
   1.12 had already checked `init_from_allocations` and
   `wp_adequacy_from_init`; PR #132 closes the remaining conversion boundary.
   The patched checker completes the concrete `init`, `wp_adequacy`, and public
   signature test without any target-local errors or goals. No proof-side
   workaround or change to the Iris definitions was required.
7. **Done for the term-mode scope:** generic masked Hoare triples include
   pre/post/combined consequence, bind, value/introduction, pure-step, load,
   store, and allocation rules. Proof-mode typeclass instances remain outside
   the scope of this port.
8. **Deferred entirely by request:** factorial syntax itself contains String
   literals, and Arend 1.12 currently reports `Cannot check string` before any
   substitution proof is considered. No generic factorial file is retained in
   this pass; resume it only with the separate String implementation.

## A13: Optional Ghost Libraries

The following optional Plan A library is now ported because the modular
counter requires it:

- `ghost_map`: implemented as the public ownership layer over the already
  verified `gmap_view`/`gen_heap` algebra, including empty allocation,
  insertion, lookup, update, and deletion.
- `mono_nat`: implemented with fractional authoritative ownership, persistent
  lower-bound snapshots, validity and weakening laws, allocation, and
  frame-preserving monotone updates.
- `frac_auth`: the generic fractional-fragment authoritative CMRA is ported,
  including fragment composition, validity, agreement, and the full-fragment
  replacement update used by the modular counter model.
- `saved_pred`: ported with allocation, persistent discarded ownership, and
  agreement; it now backs the modular counter's pending read protocol.

Still absent:

- `ghost_var`
- `mono_Z`
- `saved_prop`
- `na_invariants`
- `cancelable_invariants`

They are not required for the basic invariant/WP pipeline. Start them only
after A11 and A12 are complete.

## Parallel modular counter port

Implemented and source-checked:

- heap-language `BinOp`, `AllocN`, and `FAA` syntax and base steps;
- a real fork-aware operational semantics and existing multi-thread adequacy;
- complete step inversions for binary operations, `Fork`, and `FAA`;
- derived `wp_binop`, `wp_nat_add`, `wp_loc_add`, `wp_fork`, and `wp_faa`;
- strongly-atomic mask changing (`wp_atomic`) and the reusable
  invariant-opening rule `wp_atomic_inv_acc`;
- contiguous `pointsto_block` and list-valued `pointsto_array` ownership,
  their uniform-block bridge, block-freshness construction, and `wp_allocN`;
- source-clean prophecy-map allocation/agreement/update and the
  `wp_new_proph` / `wp_resolve_store` rules;
- the counter's `frac_auth (agree Nat)` model resource, functor packaging,
  fractional model fragments, allocation, authority/fragment replacement,
  and agreement rule;
- executable Arend ports of `msc_new_counter`, `msc_incr`, `msc_sum_loop`,
  `msc_read`, spawn/join/par, the parallel client, and `msc_proph_total`.
- the counter/request ghost protocols, invariant and persistence assertions,
  array/list focusing laws, monotone snapshots and sum bounds, request
  register/take/advance proofs, and the complete source-checked
  `msc_new_counter_spec`;
- the atomic shard update and public `msc_incr_spec`, the complete scan-loop and
  prophecy-resolution `msc_read_spec`, and their source-language wrappers;
- invariant-backed spawn and join handles/specifications, `par`, and the
  two-thread four-increment client proof;
- `msc_new_counter_two_client_spec` and `msc_closed_client_wp`, connecting the
  constructor's retained size equation to handles 0 and 1 and proving that the
  actual closed source program returns `4`;
- the concrete `irisSigma ++ mscSigma ++ spawnSigma` instance and
  `msc_closed_client_adequate`, which proves both the result and safety of every
  thread in every reachable pool.

The full term-mode Rocq modular-counter proof port is complete.  The extra BI
permutation lemmas in `parallel_counter_client.ard` are proof-mode quality-of-
life replacements; they introduce no new resource algebra or semantic axiom.

## Tests and Build Quality

Forwarding-only `*_test` modules and the standalone conversion reproducer were
removed during the 2026-08-15 consolidation. Canonical definitions are checked
directly. `src/tests/generic_heap.ard` remains as the closed binder-free A12
client with WP and Hoare specifications and has no String dependency.

The Rocq-structured tree contains 51 modules. A cache-disabled
`--recompile --serialize` run checked all of them in 5m32s and persisted 50;
only the explicitly deferred `tests.fact` String failures were skipped.
The subsequent fresh-process load reported `51 loaded out of 51 candidates`
with no deserialization fallback; `tests.fact` still reports its expected
source diagnostics.

Non-blocking cleanup:

- Remove duplicate-import warnings (`decideEq`, `own_mono`, `own_unit`,
  `own_valid`, `heap_update`, and `||`).
- Keep source and binary-cache verification in the release checklist after
  changes to recursive `iProp` definitions.

## Remaining Work and Next Steps

### Required to close the current port

1. Implement String checking and finish the deferred factorial example.
2. Close the explicit goals in `iris_heap_lang/lang.ard` and
   `iris_heap_lang/lang_subst.ard`.

The non-String core, including `iris.base_logic.lib.wsat_sigma`, consolidated invariants, generic
program logic, adequacy, serialization, and cache reload, is complete.

### Follow-up compatibility work, only when a client needs it

1. Add Rocq-compatible `own_ne` and `own_persistent` aliases/instances over the
   already proved `own_dist` and `own_core_persistent` semantics.
2. Add the optional Rocq-shaped `StepIndex`/`SI` wrapper only if a downstream
   port requires that abstract interface.
3. Reduce duplicate-import warnings. They affect build noise, not the proved
   semantics.

### Explicitly not part of the next implementation pass

- Do not implement or repair String equality, substitution lemmas, or the
  String-based factorial client until String support is handled as a separate
  task.
- Do not implement proof-mode classes (`IsExcept0`, `IntoInv`, `IntoAcc`) as
  part of the term-mode core port.
- Do not start A13 ghost libraries unless one is requested by a concrete
  example or downstream theorem.

### Definition of done for the current stage

The stage is complete when an arend-lib-regression-clean patched checker validates the
concrete `init` and `wp_adequacy` definitions, the public signature test passes,
the complete `iris.program_logic.adequacy` module serializes, and the dependency-ordered final run
reports no goals outside the explicitly deferred String files. The three
definition targets elaborate with the current candidate patch, but the full
audit and clean-cache criteria do not pass.

## Verification Snapshot

At the 2026-08-11 audit:

- Foundations, generic ownership, A7, and A8 typechecked.
- A9 fancy updates and all A9 smoke tests typechecked.
- A10 namespaces and all A10 smoke tests typechecked.
- A11 and its public signature tests typecheck.
- The historical fixed-model WP/lifting/adequacy stack still typechecks.
- Generic heap definitions and laws typecheck and were serialized with their
  dependency layer (8 modules persisted).
- The generic masked WP core and primitive-step lifting rule typecheck.
- Generic step-readiness/reducibility, primitive-step lifting,
  `fupd_wp`, evaluation-context bind, atomic lifting, and pure/load/store/
  allocation rules typecheck; `iris.program_logic.lifting` and its new dependency layer are
  serialized.
- Generic Hoare consequence/bind/value/introduction/pure/load/store/allocation
  rules and the expanded smoke suite typecheck and are serialized.
- The binder-free generic allocation example typechecks and is serialized.
- An official Arend 1.12 CLI was built directly from tag `v1.12.0`
  (`c51e285e0`), without the pending comparison change. A cache-disabled
  `iris.program_logic.adequacy:init_from_allocations` run completed in 39.9s and persisted its
  41-module source dependency cone.
- A cache-disabled official check of `iris.program_logic.adequacy:wp_adequacy_from_init` completed
  in 21.0s. Thus the abstract bootstrap and the complete sequential adequacy
  argument are release-verified.
- Official dependency checks completed for `iris.program_logic.weakestpre` (12.9s), `iris.program_logic.lifting`
  (3m0s), `iris_deprecated.program_logic.hoare` (3m0s), and `tests.generic_heap` (1m9s). Their only goal
  was `iris_heap_lang.lang:112` (`String` decidable equality).
- Official `iris.program_logic.adequacy:init` did not finish. Independent runs were stopped after
  10 and 30 silent minutes with all 41 official-generated caches loaded. No
  error or new goal was emitted, but nontermination is not verification.
- Guarded Arend PR #132 was rebased onto local v1.12 master and adapted at
  `b1a256cb6`. Its focused `ComparisonTest` suite passed, and the built jar has
  SHA-256 `3839c7e71796db6561b5a64e52a8e90ca2889a71395301e82b6e2cc3e1cd11c2`.
- `iris.program_logic.adequacy:init` and `iris.program_logic.adequacy:wp_adequacy` complete with the patched checker;
  the former forwarding-only signature smoke module has been removed.
- The only accepted goal encountered by new modules is the deliberately
  ignored String equality goal imported from `lang`.
- After the Rocq-layout refactor, a cache-disabled check attempted all 51
  modules, completed in 5m32s, persisted 50, and skipped only `tests.fact`. A
  fresh-process cache reload loaded all 51 candidates with no fallback. Thus all
  non-String modules have clean source, serialization, and cache verification.
