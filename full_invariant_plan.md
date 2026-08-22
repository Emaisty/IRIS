# Full IRIS Port — Plan A (Rocq-Faithful) Roadmap

## 0. Goal

Port IRIS to Arend with full Rocq fidelity:

  `iProp Σ ≈ uPred (∀ i : gid Σ. gname →fin (Σ i)(iProp Σ))`

where `Σ : gFunctors` is a user-extensible list of contractive CMRA functors,
`gname = Positive`, and `own γ a` is the generic ghost-state primitive for
*any* CMRA `A` such that `inG Σ A` holds.

This is the **impredicative** version: invariants can store any `iProp Σ`,
including `inv N' Q` itself; `saved_prop`, `saved_pred`, gset bijection
ghost state, etc., are all naturally expressible. The price is
significantly more infrastructure than the predicative Plan B.

This document is the plan for that path. The factorial example and
"first-order" invariants can be built on the lighter Plan B (see
`invariants_plan.md`); this plan is the right choice if/when:

- You need nested invariants (`inv N (inv N' P)`).
- You need stored propositions (`saved_prop_alloc`, `saved_prop_agree`).
- You want library-style ghost state: a third-party file adds a new CMRA
  by extending `Σ`, gets `own γ a` for free, with no edit to a monolithic
  `GlobalM`.
- You want the port to match Rocq line-for-line for didactic reasons.

---

## 1. What you already have (assumes Plan B is in place)

Plan A reuses every piece of Plan B *except* the monolithic `GlobalM`.
The shared foundation:

| Done as part of Plan B / Phase 1 / Phase 2 | File |
|---|---|
| OFE / COFE / Banach element-fixpoint | `src/iris/algebra/ofe.ard` |
| `LaterOFE` / `next` | `src/iris/algebra/ofe.ard` |
| CMRA + UCMRA (equiv-flavoured, Rocq-faithful) | `src/iris/algebra/cmra.ard` |
| `mkProperOwn`, `mkProperCMRAValid`, `bupd_ownM_updateP` | `src/iris/base_logic/upred.ard` |
| `Agree` CMRA | `src/iris/algebra/agree.ard` |
| `coPset` data structure + `coPpick` | `src/stdpp/coPset.ard` |
| `coPset_disj` CMRA + UCMRA | `src/iris/algebra/coPset.ard` |
| `gset_disj` CMRA + UCMRA | `src/iris/algebra/gset.ard` |
| Auth / Excl / Gmap CMRAs | `src/iris/algebra/{auth,excl,gmap}.ard` |
| BUpd modality + bupd-rules | `src/iris/bi/updates.ard` |

The CMRA-class weakening to `equiv` (done in Plan B Phase 2) is required
by Plan A as well — Rocq's `RAMixin` is equiv-flavoured for the same reason.

---

## 2. New infrastructure unique to Plan A

These are the components Plan B deliberately skipped. They are
substantial, ordered by dependency. Estimated Arend line counts in
parentheses.

### A1. Step-index infrastructure (300 LoC)

**Rocq:** `algebra/stepindex.v`, `algebra/stepindex_finite.v`.

For the Arend port we likely just use `Nat` as the step-index type (we
already do). What we may still need from these files:

- The `SI` class (or fixed `Nat` instance).
- Lemmas about step-index ordering.
- `dist_later` (already in `src/iris/algebra/ofe.ard`).

For finite step indices specifically, Rocq's `stepindex_finite.v`
specialises to `Nat`. If we never need transfinite step indices (and we
don't for sequential heap programs), this can be inlined into `ofe.ard`.

**Status:** mostly subsumed by existing `ofe.ard`. Probably needs a
small `\class StepIndex` wrapper to make the rest of the Plan A code
look like Rocq.

### A2. `cofe_solver` — America-Rutten / recursive domain equations (500–800 LoC)

**Rocq:** `algebra/cofe_solver.v`.

The heart of Plan A. Solves

  `X ≅ F(X)`     as an OFE,

for any locally contractive functor `F : OFE → OFE`. Construction:

1. Define an approximating chain `X_0 := unit_OFE`, `X_{n+1} := F(X_n)`.
2. Show the chain has consistent embedding/projection maps
   `e_n : X_n → X_{n+1}`, `p_n : X_{n+1} → X_n` with `p_n ∘ e_n = id`.
3. Define the bilimit `X_∞` as Cauchy sequences `(x_n)` with
   `p_n x_{n+1} = x_n`.
4. Prove `X_∞ ≅ F(X_∞)` via the universal property.

Steps in detail:

  - **`Solution` record**: an OFE `X` together with `ofe_iso : X ≃ F X`
    (isomorphism in the category of OFEs).
  - **Approximation indices**: `Nat` (or general step-index).
  - **A_n / F_n / P_n / E_n constructions**: the embedding/projection
    morphisms between approximations.
  - **`solver`**: takes a locally contractive `rFunctor F` and produces
    a `Solution F`.
  - **Coherence lemmas**: about 30 small lemmas connecting `solver.unfold`,
    `solver.fold`, contractivity, and the universal property.

This is the hardest single deliverable in the whole port. Rocq's version
is about 500 lines, packed; an Arend transliteration may be longer due
to explicit universe / level management.

**Suggested checkpoint:** prove `solver` works for one toy example
(`X ≅ Later X`, whose solution is the all-`unit` OFE) before sinking
time into the IRIS application.

### A3. `gFunctor`, `gFunctors`, `gid`, `gname` (200 LoC)

**Rocq:** `base_logic/lib/iprop.v` (header section).

- `gFunctor`: a bundled `rFunctor` + contractivity proof.
- `gFunctors`: indexable list of `gFunctor`s. Rocq uses
  `{ gFunctors_len : nat ; gFunctors_lookup : fin len → gFunctor }` to
  avoid universe inconsistencies; we should do the same.
- `gid Σ := fin (gFunctors_len Σ)`.
- `gname := Positive`.
- `subG Σ₁ Σ₂` typeclass: "Σ₁ is contained in Σ₂".

`gFunctors` operations: `nil`, `singleton`, `app`, and the `subG_app_l/r`
instances. The corresponding Arend declarations should be light — most
of the work is in the right universe management.

### A4. `iResF Σ` and the recursive `iProp Σ` solution (200 LoC)

**Rocq:** `base_logic/lib/iprop.v` (`iProp_solution_sig` and `iProp_solution`).

Given `Σ : gFunctors`, define:

```
iResF Σ : urFunctor :=
  discrete_funURF (λ i. gmapURF gname (Σ i))
```

The recursive definition

```
iProp Σ ≅ uPred (iResUR Σ iProp Σ)
```

is solved by `cofe_solver` from §A2. Concretely, apply `solver` to
`uPredOF (iResF Σ)` to get an `iPrePropO Σ` such that

```
iPrePropO Σ ≅ uPredO (iResUR Σ iPrePropO Σ)
```

then define `iProp Σ := uPred (iResUR Σ iPrePropO Σ)` and `iPropO Σ`
similarly. The isomorphism gives:

- `iProp_unfold : iPropO Σ -n> iPrePropO Σ`
- `iProp_fold : iPrePropO Σ -n> iPropO Σ`
- `iProp_fold_unfold : iProp_fold (iProp_unfold P) ≡ P`
- `iProp_unfold_fold : iProp_unfold (iProp_fold P) ≡ P`

These four lemmas are used everywhere downstream.

### A5. `inG Σ A` and `own γ a` (400 LoC)

**Rocq:** `base_logic/lib/own.v` (the entire file).

`inG Σ A`: typeclass with fields `inG_id : gid Σ` and a coercion
`A ≅ rFunctor_apply (Σ inG_id) (iPropO Σ)`. Says: CMRA `A` is among
the functors in `Σ`, instantiated at the iProp solution.

`iRes_singleton γ a : iResUR Σ`: place `a` at position `inG_id, γ`,
zero elsewhere. (`discrete_fun_singleton (inG_id i) {[γ := unfold a]}`)

`own γ a := uPred_ownM (iRes_singleton γ a)`. This is the generic
ghost-state predicate.

Once these are in place, the standard library of lemmas falls out:

  - `own_op : own γ (a · b) ⊣⊢ own γ a ∗ own γ b`
  - `own_mono : a ≼ b → own γ b ⊢ own γ a`
  - `own_valid : own γ a ⊢ ✓ a`  (with the step-indexed flavour)
  - `own_alloc_strong : ✓ a → ⊢ |==> ∃ γ. ⌜γ ∉ G⌝ ∧ own γ a`
  - `own_alloc : ✓ a → ⊢ |==> ∃ γ. own γ a`
  - `own_update : a ~~> b → own γ a ⊢ |==> own γ b`
  - `own_update_ND : a ~~>: Φ → own γ a ⊢ |==> ∃ b. ⌜Φ b⌝ ∧ own γ b`
  - `own_unit : ⊢ |==> own γ ε` (for UCMRAs)
  - `own_persistent : CoreId a → Persistent (own γ a)`
  - `own_proper`, `own_ne`

Each reduces to `bupd_ownM_updateP` (already provided in `src/iris/base_logic/upred.ard`
from Plan B Phase 1) applied to an `iRes_singleton`-based
frame-preserving update.

The trickiest pieces:
- `own_alloc_strong` needs a fresh-name lemma over `gname = Positive`,
  which the `coPpick` of Plan B's `coPset.ard` should cover.
- The discrete_fun infrastructure: lemmas about
  `discrete_fun_singleton`, `discrete_fun_lookup_singleton`,
  etc., need an Arend port.

### A6. Replace Plan B's `GlobalM₀ / GlobalM` (–200 LoC)

Plan A *removes* the layered Plan B resource entirely. Instead of
parameterising over a fixed `M : UCMRA`, the WP / adequacy / Hoare
chain is now parameterised over `Σ : gFunctors`, and `iProp Σ` plays
the role formerly played by `ProperUPred M`.

Concretely:

  - `weakestpre.ard` swaps `ProperUPred M` for `iProp Σ`.
  - `adequacy.ard` likewise.
  - The `state_interp` for the heap language becomes
    `gen_heapGS Σ Loc Value` plus a CMRA in `Σ`.
  - `lifting.ard`'s rules become `inG Σ heap_cmra → wp …`.

### A7. `wsatGS`, `wsat`, `ownI`, `ownE`, `ownD` - complete

**Rocq:** `base_logic/lib/wsat.v`.

With `Σ`-based ghost state in place, these are direct ports. `wsatGS Σ`
demands three resources via `inG`:

  - The invariant map: `gmap_view positive (agree (later (iProp Σ)))`.
  - The enabled set: `coPset_disjUR` (from Plan B Phase 2).
  - The disabled set: `gset_disjUR positive` (from Plan B Phase 2).

Definitions:

  - `ownI i P := own invariant_name (gmap_view_frag i DfracDiscarded
                  (to_agree (next P)))`
  - `ownE E := own enabled_name (CoPset E)`
  - `ownD D := own disabled_name (GSet D)`
  - `wsat := locked (∃ I. own invariant_name (gmap_view_auth … I) ∗
              [∗ map] i↦Q ∈ I, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})`

Lemmas (one-for-one from `wsat.v`):

  - `ownE_op`, `ownE_disjoint`, `ownE_op'`, `ownE_singleton_twice`
  - `ownD_op`, `ownD_disjoint`, `ownD_op'`, `ownD_singleton_twice`
  - `invariant_lookup`
  - `ownI_open`, `ownI_close`
  - `ownI_alloc`, `ownI_alloc_open`
  - `wsat_alloc`

The two `ownI_alloc` lemmas need `gset_disj_alloc_updateP_strong'`
(from Plan B) and `gmap_view_alloc` (a `gmap_view` lemma — see §A8).

### A8. `gmap_view` CMRA - complete (full fractional version)

**Rocq:** `algebra/view.v` plus `algebra/gmap_view.v` (specialisation).

`gmap_view K V` is `auth (gmap K (dfrac × agree V))` with the
`view_rel` baked in. It powers `gen_heap`, `wsat`'s invariant store,
`ghost_map`, etc.

Implemented in `src/iris/algebra/view.ard` and
`src/iris/algebra/lib/gmap_view.ard`, with supporting product, fraction,
discardable-fraction, option, and functor modules.  The port includes
fractional authoritative and fragment constructors, validity/lookup
lemmas, discarded Agree lookup, fresh allocation, updates, and the
`gmap_view` functor laws.

`wsat` and `wsat_alloc` use the full Rocq shape: authoritative ownership
at `DfracOwn 1`, discarded invariant fragments, and agreed later iProps.
The recursive `iProp` specialization is exposed through a sealed
`GmapViewAgreeKit`, keeping Arend conversion checking terminating.

### A9. Concrete `fupd` (300 LoC)

**Status: complete.**

**Rocq:** `base_logic/lib/fancy_updates.v`.

```
uPred_fupd_def E1 E2 P := wsat ∗ ownE E1 -∗ |==> ◇ (wsat ∗ ownE E2 ∗ P)
```

Implemented in `src/iris/base_logic/lib/fancy_updates.ard` and `src/iris/base_logic/lib/fancy_updates_mask.ard`; the canonical
definitions are checked directly. The generic `FUpd`, `BiFUpd`, and
`BiBUpdFUpd` interfaces live alongside the existing update classes in
`src/iris/bi/updates.ard`. The concrete port includes non-expansiveness,
monotonicity, basic-update lifting, except-0 elimination, transitivity,
framing, mask framing, subset mask opening/closing, introduction, and
mask monotonicity, together with concrete `iProp` instances.

The subset proof uses an opaque inner update to keep Arend conversion
checking finite over the recursive resource domain. All A9 modules are
hole-free. A full project check reaches every A9 law with
no A9 goals; the only remaining project goals are the pre-existing ones
in `lang.ard` and `lang_subst.ard`.

### A10. Namespaces (250 LoC)

**Status: complete.**

**Rocq:** `stdpp/namespaces.v` + `base_logic/lib/invariants.v`.

Implemented in `src/stdpp/namespaces.ard`, with the reusable finite-set
bridge in `src/stdpp/finite_coPset.ard`; the canonical API is checked directly.
Namespace is `List Pos`; `nclose` uses a
prefix-free encoding into `coPset`. The port includes root closure,
closure monotonicity under `ndot`, namespace disjointness, distinct
sibling disjointness, left/right disjointness preservation, constructive
infinitude, and `fresh_inv_name`.

The finite-set bridge embeds `Gset Pos` into `coPset`, proves pointwise
membership equivalence, and expresses infinitude as escaping every finite
set. Fresh invariant names follow the Rocq structure: subtract the finite
embedding from `nclose N`, then select a witness with `coPpick`. All A10
modules are hole-free and pass normal and core double-checking.

### A11. `inv N P` (300 LoC)

**Status: complete.**

**Rocq:** `base_logic/lib/invariants.v`.

Same as Plan B Phase 6. The internal `own_inv` definition uses `ownI`;
the public `inv N P` is `□ ∀ E. ⌜↑N ⊆ E⌝ → fupd …`. All the
standard lemmas (`inv_alloc`, `inv_acc`, `inv_iff`, `inv_alter`,
`inv_combine`, `inv_split`) port one-for-one.

### A12. Retrofit WP / adequacy / lifting (500 LoC)

**Status: canonical non-String stack and derived operational API implemented;
the bootstrap and adequacy pipeline typechecks and serializes with the guarded
Arend conversion fix (verified 2026-08-15).**

**Rocq:** `program_logic/{weakestpre,adequacy,lifting}.v`.

Same shape as Plan B Phase 7 — replace `mkProperBUpd` with
`mkProperFUpd E ∅` in `wp_pre`, carry the mask, bootstrap adequacy
with `wsat_alloc`. The difference: everything is now over `iProp Σ`,
and the heap language requires `inG Σ heap_view_cmra`.

Heap-language-specific:

  - `gen_heap.v` from `base_logic/lib/gen_heap.v` (≈200 LoC). Defines
    `heap_interp σ : iProp Σ` and the points-to predicate
    `l ↦{q} v`.
  - `heap_lang/lang.v` and `lifting.v` (implemented under
    `src/iris_heap_lang/` and `src/iris/program_logic/`).

Current checked implementation (the unsuffixed names are canonical; the
factorial-specific fixed-heap compatibility layer is consolidated in
`src/tests/fact/program_logic.ard`):

  - `src/iris/base_logic/lib/gen_heap.ard`: constant ghost functor over a full
    `gmap_view (Agree (Discrete V))`, with `gen_heapGpreS`/`gen_heapGS`,
    interpretation, fractional points-to, validity, allocation, update, and
    initialization.
  - `src/iris/program_logic/weakestpre.ard`: `irisGS`, state interpretation, masked WP
    pre-body with the `E -> empty -> E` transition, contractivity, fixed point,
    unfolding, bidirectional value rule, and full postcondition monotonicity
    through finite approximants and the COFE limit.
  - `src/iris/program_logic/lifting.ard`: non-value readiness, reducibility, the fundamental
    concrete primitive-step rule, and same-mask fancy-update elimination.
  - `src/iris/program_logic/iris_sigma.ard`: `wsatSigma ++ gen_heapSigma` packaging.
  - `src/iris_deprecated/program_logic/hoare.ard`: masked generic Hoare definition and full pre/post/combined
    consequence.
  - `src/iris/program_logic/adequacy.ard`: independent world/heap allocation, `irisGS` packaging,
    sequential multi-step WP preservation, safety/value extraction, and the
    step-indexed fancy-update soundness bridge used by adequacy.
  - `src/tests/fact/program_logic.ard`: fixed-heap WP, lifting, and Hoare support
    retained for the existing factorial development.

The derived non-String A12 API is now implemented: WP bind/context rules,
generic load/store/alloc/pure rules, the corresponding term-mode Hoare rules,
and a binder-free allocation example all typecheck. The combined bootstrap,
sequential multi-step adequacy theorem, and concrete allocation specialization
all pass deep checking and serialization with the guarded conversion fix.

### A13. Heap language ghost-state libraries (optional, 200 LoC each)

Now that ghost state is generic, you can finally port the standard
helper libraries:

  - `ghost_var Σ A`: ghost variable storing an A.
  - `ghost_map Σ K V`: ghost finite map.
  - `mono_nat Σ`, `mono_Z Σ`: monotone counters.
  - `saved_prop`, `saved_pred`: stored propositions.
  - `na_invariants`, `cancelable_invariants`: alternative invariant
    flavours.

None of these are necessary for the basic invariants pipeline; they
are the kinds of libraries that *only* Plan A unlocks.

---

## 3. Estimated cost

| Component                  | Arend (est.) | Rocq ref (LoC) |
|----------------------------|--------------|----------------|
| A1. Step-index infra       | 300          | `stepindex.v` (~500) |
| A2. cofe_solver            | 500–800      | `cofe_solver.v` (~500) |
| A3. gFunctor / gFunctors / subG | 200      | `iprop.v` (header) |
| A4. iProp solution          | 200          | `iprop.v` (solution) |
| A5. inG + own + own_alloc   | 400          | `own.v` (~540) |
| A6. Plan-B retrofit         | −200 (net)   | — |
| A7. wsat                    | 400          | `wsat.v` (~200) |
| A8. gmap_view               | 300 (light) / 700 (full) | `view.v` + `gmap_view.v` |
| A9. fupd (concrete)         | 300          | `fancy_updates.v` |
| A10. namespaces             | 250          | `namespaces.v` |
| A11. inv                    | 300          | `invariants.v` (~220) |
| A12. WP retrofit            | 500          | `program_logic/*.v` |
| **Total**                   | **~3500–4000 Arend lines** | |

Plus everything already done for Plan B Phase 1–2 (~3000 lines), for a
**grand total of roughly 6500–7000 Arend lines** to reach feature
parity with Iris's invariants + generic ghost state.

For reference, full Iris (every feature) is about 30k Coq lines; this
plan is a focused subset.

---

## 4. Order of work

The cofe_solver is the long-pole item: nothing past A4 can be defined
without it, but A1, A3, and the Plan B Phase 2 algebra are independent.

Suggested sequence:

  1. **A1** (step-index wrapper).
  2. **A2** (cofe_solver). Verify with the `Later X` toy.
  3. **A3** (gFunctor / Σ / subG / gid / gname).
  4. **A4** (iProp via cofe_solver applied to `uPredOF (iResF Σ)`).
  5. **A8** (gmap_view, full fractional version). **Complete.**
  6. **A5** (inG + own). Implement `own_alloc` last (needs gmap_view).
  7. **A7** (wsat). **Complete.**
  8. **A9** (fupd).
  9. **A10** (namespaces).
  10. **A11** (inv).
  11. **A12** (retrofit WP / adequacy / lifting).
  12. **A13** (heap-language ghost-state libraries, optional).

Phases 1–6 take you to "generic ghost state works"; 7–11 take you to
"invariants work"; 12 takes you to "the existing factorial example
ports forward to the parametric Σ form".

---

## 5. Risks specific to Plan A

- **Universe management**. Iris uses `gFunctors` as a sigma-like record
  precisely to avoid universe inconsistencies with `list gFunctor`.
  Arend's universe polymorphism is different from Coq's; some
  Rocq-tricks (e.g. `Σ` being equivalent to `list gFunctor` but
  defined as a dependent record) may not carry over directly. Allow
  extra time for universe debugging.
- **`cofe_solver` correctness**. The construction is delicate; the
  Rocq proof relies on extensive setoid rewriting that Arend lacks.
  Re-deriving the contractivity arguments in path-based form is the
  main risk in A2.
- **The `iRes_singleton` machinery**. `discrete_fun_singleton` requires
  decidable equality on `gid Σ = fin (len Σ)`, which is fine, but the
  surrounding combinators (`map_singleton`, `proper`-instances) require
  ~50 small lemmas.
- **gmap_view conversion cost**. The full fractional View infrastructure
  is implemented. Recursive `iProp` clients must use the sealed Agree-kit
  interface rather than unfold the full View CMRA record during conversion.
- **No `iProp`-as-modal-logic shortcut**. Some Rocq proofs use the
  Iris proofmode (`iIntros`, `iApply`, `iInv`); we have none of that.
  Every Plan A proof is a direct uPred manipulation. This is true of
  Plan B too, but Plan A's proofs are typically longer because they
  reference parametric `Σ`-machinery.

---

## 6. Why not Plan B?

We chose Plan B in `invariants_plan.md` because:

- The factorial example only needs first-order invariants.
- Plan B reaches a working invariants pipeline in ~3000 Arend lines vs.
  Plan A's ~6500–7000.
- The recursive domain construction (A2) is technically demanding and
  high-risk for a first Iris port.

Plan B's limitations (no nested `inv`, no `saved_prop`, no
library-style ghost state) only bite once you start verifying
higher-order or strongly modular code. For all the examples currently
in this repository, Plan B is enough.

Pick Plan A if you decide the long-term goal is a faithful Iris port,
not just "invariants for sequential heap programs".

---

## 7. Things still out of scope even in Plan A

- `BiFUpdPlainly`, plainness modality, later credits, atomic updates,
  prophecies, total WP. Each is an independent extension.
- Iris's proofmode (`iIntros`, `iApply`, `iInv`). Implementing a tactic
  language for Arend is a separate, large project — orthogonal to all
  of the above.
- Concurrency / language extension to a concurrent semantics. Iris's
  `language.v` parameterises over a forking step relation; the heap
  language here is sequential. Adding fork would be substantial but
  is mostly independent of the invariants machinery.
- HeapLang automation (`wp_pures`, `wp_alloc`, `wp_load`, `wp_store`
  notation/tactics). Again, tactic-language work.
