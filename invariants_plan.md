# Invariants Implementation Plan — Arend Port of IRIS

> Historical planning snapshot. The paths have been updated to the current
> Rocq-shaped source hierarchy, but the “missing/not started” statuses below
> describe the project before the completed full-architecture implementation.
> Use `IRIS_PORT_REMAINING.md` for current status.

## 0. Goal

Extend the existing Arend port of IRIS so that **semantic invariants**
`inv N P` can be allocated, opened (with mask tracking), and closed. This
brings the port from a single-resource WP into the full IRIS recipe with
ghost state and the world-satisfaction predicate `wsat`.

The current port works directly over a *fixed* CMRA `M : UCMRA` (set in
practice to `HeapCMRA Loc cnt Value`). Propositions are
`ProperUPred M`. There is no notion of *named* ghost ownership (`own γ a`),
no fancy update `fupd`, no `wsat`, and no recursive `iProp` solution. All
of that has to be added.

---

## 1. Current State (recap)

| Component                | Arend file                       | Status      |
|--------------------------|----------------------------------|-------------|
| OFE / COFE / Banach      | `src/iris/algebra/ofe.ard`                    | done        |
| CMRA / UCMRA             | `src/iris/algebra/cmra.ard`                   | done        |
| Excl / ExclU             | `src/iris/algebra/excl.ard`          | done        |
| Pmap / Gmap CMRA         | `src/stdpp/pmap.ard`, `src/iris/algebra/gmap.ard` | done |
| Auth CMRA                | `src/iris/algebra/auth.ard`          | done        |
| Heap CMRA (Auth∘Gmap∘ExclU) | `src/tests/fact/heap.ard`            | done        |
| `uPred` / `ProperUPred`  | `src/iris/base_logic/upred.ard`                  | done        |
| BI interface + mixin     | `src/iris/bi/interface.ard`              | done        |
| BIuPredMixin instance    | `src/iris/bi/updates.ard` (top)          | done        |
| Derived BI laws          | `src/iris/bi/derived_laws.ard`           | done        |
| `bupd` (basic update)    | `src/iris/bi/updates.ard`                | done        |
| Language                 | `src/iris_heap_lang/lang.ard`, `src/iris_heap_lang/lang_ectx.ard` | done     |
| `wp` (Banach fixpoint)   | `src/iris/program_logic/weakestpre.ard`             | done        |
| Adequacy                 | `src/iris/program_logic/adequacy.ard`               | done        |
| Hoare triples            | `src/iris_deprecated/program_logic/hoare.ard`                  | done        |
| `Agree` CMRA             | (missing)                        | **not started** |
| `coPset` / `coPset_disj` | (missing)                        | **not started** |
| `gset_disj` (positive)   | (missing)                        | **not started** |
| `Later`-OFE / next       | (missing)                        | **not started** |
| `gmap_view` / `gmap (Agree (Later iProp))` | (missing)      | **not started** |
| `gFunctors` / `inG`      | (missing)                        | **not started** |
| `uPred_ownM` (primitive) | (missing — only `mkProperEmp`)   | **not started** |
| `own γ a`                | (missing)                        | **not started** |
| `wsat`, `ownI`, `ownE`, `ownD` | (missing)                  | **not started** |
| `fupd`                   | (missing)                        | **not started** |
| `inv N P` + namespaces   | (missing)                        | **not started** |

Refs in `support_files/iris/`:

- `base_logic/upred.v` — primitive `uPred_ownM`
- `base_logic/lib/iprop.v` — `iProp Σ`, recursive domain equation (`cofe_solver`)
- `base_logic/lib/own.v` — `own γ a`, `inG`, frame composition into `iResUR Σ`
- `base_logic/lib/wsat.v` — `wsat`, `ownI`, `ownE`, `ownD`
- `base_logic/lib/fancy_updates.v` — `uPred_fupd_def`, the `BiFUpdMixin`
- `base_logic/lib/invariants.v` — `inv N P`, `inv_alloc`, `inv_acc`
- `algebra/agree.v`, `algebra/coPset.v`, `algebra/gset.v`, `algebra/view.v`, `algebra/gmap_view.v`
- `algebra/cofe_solver.v` — solves `X ≅ uPred (iResUR Σ X)`

---

## 2. Architectural Choice

Two viable strategies — pick **B** and keep **A** as future work.

### A. Full Iris architecture (parametric `Σ`, recursive `iProp`)

Faithful to Rocq:

  `iProp Σ ≈ uPred (∀ i, gname →fin Σ_i (iProp Σ))`

Pros: matches the published paper; supports impredicative invariants
(invariants over `iProp` itself, via `Agree (Later iProp)`); is the only
way to get `saved_prop` and higher-order ghost state.

Cons: requires the **cofe_solver** (recursive COFE construction) — a
large bit of infrastructure (~500 LoC in Rocq, every step requiring
contractive functors). Empty placeholder `cofe_solver.ard` is already
in the project notes.

### B. Predicative / monolithic-resource architecture (recommended)

Keep the current "fixed `M : UCMRA`" design. Pre-bake the resource
algebra so the invariant store contains *uPreds of M* (not of `iProp`).
The recursion is broken by **`Later`** on the invariant value — the
store holds `Later (ProperUPred M)`, not `ProperUPred M`, so there is no
circular type dependency. This is what IRIS-Lite / "non-impredicative"
formalisations do and is enough for sequential heap programs and for
non-higher-order invariants (which covers every example currently in the
project, including the factorial).

**Concretely**: define one big resource

```
GlobalM (Loc, cnt, Val) :=
  ProdUCMRA
    HeapCMRA Loc cnt Val                                      -- physical heap
    InvCMRA Loc cnt Val                                       -- invariant map
    EnabledCMRA                                               -- ownE
    DisabledCMRA                                              -- ownD
```

where `InvCMRA = AuthUCMRA (GmapUCMRA Positive _ (AgreeUCMRA (LaterOFE (ProperUPred M))))`.

The "knot" that breaks the recursion: `Later P` is non-expansive in `P`
but only "later"-non-expansive — so `Later (ProperUPred M)` is well
defined as long as we read its content one step-index lower than the
ambient predicate. This is exactly how Iris itself handles the
recursive invariant value.

Pick **B**. Less infrastructure, no domain-equation solver, fits the
current "single CMRA + ProperUPred" design.

---

## 3. Phase Breakdown

Each phase compiles and the example (`src/tests/fact.ard`) should
still type-check at the end of each phase.

### Phase 1 — primitive `ownM`

Add the primitive ownership upred. This is independent of invariants
but is the building block for everything below.

**Rocq:** `base_logic/upred.v` lines 376–386 (`uPred_ownM_def`).

**Arend (new):** add to `src/iris/base_logic/upred.ard`:

```
\func mkProperOwn {M : UCMRA} (a : M.E) : ProperUPred M \cowith
  | upred_holds n x => inclN {M} a n x
  | upred_mono       => -- transitivity of inclN (already proved in cmra.ard)
```

Plus derived lemmas:

  - `own_op`        : `ownM (a · b) ⊣⊢ ownM a ∗ ownM b`
  - `own_mono`      : `a ≼ b ⊢ ownM b ⊢ ownM a`     (via inclN_trans)
  - `own_valid`     : `ownM a ⊢ <pure> validN n a` (use `cmra_validN_op_l`)
  - `own_unit`      : `True ⊢ ownM ε`
  - `bupd_ownM_updateP` : frame-preserving update lemma — needed for
    `inv_alloc` to extend the invariant map.

Note: `mkProperEmp` is exactly `mkProperOwn M.unit`. Re-prove
`mkProperEmp` in terms of `mkProperOwn` (or remove it).

### Phase 2 — supporting CMRAs

For each, follow the pattern of `lib/excl_cmra.ard` and
`lib/auth_cmra.ard`.

| Rocq file                          | Arend file (new)                | Notes |
|------------------------------------|---------------------------------|-------|
| `algebra/agree.v`                  | `src/iris/algebra/agree.ard`        | "List of dist-equivalent elements". The analysis notes claim this exists; it does not. Re-do it. |
| `algebra/coPset.v` (`coPset_disj`) | `src/iris/algebra/coPset.ard`       | Need a `coPset` type first (countable infinite subsets of `Positive`). Implementation: a tree like `Pmap`, branches labelled `all/none/branch`. |
| `algebra/gset.v` (`gset_disj`)     | `src/iris/algebra/gset.ard`         | `gset_disj` over `Positive` (countable). Disjoint-union semantics with `Invalid`. |
| `algebra/cmra.v` (`Later` OFE)     | extend `src/iris/algebra/ofe.ard`            | Add `LaterOFE A` with `dist n (next x) (next y) ↔ DistLater n x y`. `DistLater` is already in `ofe.ard`. |
| `algebra/agree.v` over `Later`     | combinator                      | `AgreeUCMRA (LaterOFE (ProperUPred M))` falls out of phase 2 components. |
| `algebra/view.v` / `gmap_view.v`   | use `AuthUCMRA (GmapUCMRA …)`   | Skip `view` in this iteration. The simpler `Auth (Gmap K (Agree (Later P)))` is enough for invariants. |

**Sub-steps inside each file:**

1. Define the carrier (data type + OFE instance).
2. Define `op`, `pcore`, `valid`, `validN`, `unit`.
3. Discharge the CMRA mixin (10 obligations, same shape as
   `lib/excl_cmra.ard`).
4. Discharge the UCMRA mixin (3 obligations).
5. Local lemmas the invariants layer needs:
   - `coPset_disj_alloc_strong_updateP` (Rocq `coPset.v` ~L70+)
   - `gset_disj_alloc_empty_updateP_strong'` (Rocq `gset.v` ~L130+)
   - `agree_op_invN` (idempotent op for `to_agree x`)

### Phase 3 — extend / replace the global resource `M`

The current `HeapCMRA` becomes one *component* of a wider product.

**New file:** `src/iris/algebra/global_cmra.ard`

```
\func InvCMRA (M : UCMRA) : UCMRA =>
  AuthUCMRA (GmapUCMRA Positive _ (AgreeUCMRA (LaterOFE (ProperUPred M))))

\func EnabledCMRA : UCMRA => CoPsetDisjUCMRA          -- carries ownE
\func DisabledCMRA : UCMRA => GsetDisjUCMRA            -- carries ownD

\func GlobalM (Loc : \Set) (cnt : Countable Loc) (Val : \Set) : UCMRA =>
  ProdUCMRA (HeapCMRA Loc cnt Val)
            (ProdUCMRA (InvCMRA (GlobalM Loc cnt Val))            -- knot
                       (ProdUCMRA EnabledCMRA DisabledCMRA))
```

The recursion in `GlobalM` is broken because `InvCMRA` puts its
predicate under `LaterOFE`. In Arend this requires a `\record` /
`\class` definition or a step-indexed fixed-point — see *§6 Knot* below.

For phase 3 it is sufficient to introduce a *non-recursive*
approximation:

```
\func GlobalM₀ (Loc cnt Val) : UCMRA =>                            -- shallow
  ProdUCMRA (HeapCMRA Loc cnt Val)
            (ProdUCMRA (InvCMRA EmptyOFE)                          -- placeholder
                       (ProdUCMRA EnabledCMRA DisabledCMRA))
```

and refine later. `ProdUCMRA` is missing from the port; add it
(componentwise op/pcore/valid; obvious obligations).

Add projection lemmas so the *existing* heap proofs continue to work:

- `lift_heap : ProperUPred (HeapCMRA …) → ProperUPred (GlobalM …)`
- `pointsTo` in `lib/heap.ard` is generalised to `pointsTo l v :
  ProperUPred (GlobalM …)` via `mkProperOwn` on the heap-projection.
- WP (in `src/iris/program_logic/weakestpre.ard`) is reparameterised over `GlobalM` —
  most of the file is unchanged because the proofs are about
  `mkProperBUpd`/`mkProperLater`/`mkProperSep`, not about the
  specific structure of `M`.

### Phase 4 — `wsat`, `ownI`, `ownE`, `ownD`

**Rocq:** `base_logic/lib/wsat.v` (203 lines).

**Arend (new):** `src/iris/base_logic/lib/wsat.ard`:

```
\func ownI (i : Positive) (P : ProperUPred (GlobalM …))
  : ProperUPred (GlobalM …)
  => mkProperOwn (invariant-name component:
       Auth-frag (gsingleton i (to_agree (next P))))

\func ownE (E : CoPset) : ProperUPred (GlobalM …)
  => mkProperOwn (enabled component: CoPset E)

\func ownD (E : Gset Positive) : ProperUPred (GlobalM …)
  => mkProperOwn (disabled component: GSet E)

\func wsat : ProperUPred (GlobalM …) =>
  exists I : Gmap Positive (ProperUPred (GlobalM …)).
    ownM (Auth-auth ⟨to_agree ∘ next⟩ I)
      ∗ big_sep_map I (λ i Q, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})
```

Lemmas (port one-for-one from `wsat.v`):

- `ownE_empty`, `ownE_op` (disjointness)
- `ownE_disjoint`, `ownE_singleton_twice`
- `ownD_*` symmetric versions
- `invariant_lookup` (ties `ownI i P` to the auth content; requires
  `Agree` validity / inclusion)
- `ownI_open`, `ownI_close`
- `ownI_alloc`, `ownI_alloc_open`
- `wsat_alloc` (initial allocation — used by adequacy)

These all use `bupd_ownM_updateP` (added in phase 1) plus the
algebra-specific frame-preserving updates from phase 2.

### Phase 5 — concrete fancy update `fupd`

**Rocq:** `base_logic/lib/fancy_updates.v`, `uPred_fupd_def`:

```
fupd E1 E2 P := wsat ∗ ownE E1 -∗ bupd (◇ (wsat ∗ ownE E2 ∗ P))
```

**Arend (new):** `src/iris/base_logic/lib/fancy_updates.ard`:

```
\func mkProperFUpd
  (E1 E2 : CoPset) (P : ProperUPred (GlobalM …))
  : ProperUPred (GlobalM …)
  => mkProperWand
       (mkProperSep wsat (ownE E1))
       (mkProperBUpd
          (mkProperExceptZero
             (mkProperSep wsat (mkProperSep (ownE E2) P))))
```

(`mkProperExceptZero P := mkProperOr (mkProperLater False) P` —
the IRIS `◇ P`. Add a tiny helper.)

Discharge `BiFUpdMixin`:

  - `fupd_ne`             — uses `upredDist` of `bupd`, `wand`, `sep`
  - `fupd_mask_subseteq`  — frame `wsat`, split `ownE`
  - `fupd_except_0`       — by definition
  - `fupd_mono`
  - `fupd_trans`          — uses `bupd_trans` and disjointness
  - `fupd_frame_r`        — uses `bupd_frame_r`

`BiBUpdFUpd` instance: `bupd P ⊢ fupd E E P`.

The `BiFUpdMixin` / `BiFUpd` typeclass needs to be re-introduced into
`src/iris/bi/interface.ard` (currently absent — `interface.ard` has the BI core
but no `FUpd` class).

### Phase 6 — namespaces and `inv N P`

**Rocq:** `stdpp/namespaces.v` + `base_logic/lib/invariants.v` (220
lines).

**Arend (new):** `src/stdpp/namespaces.ard`:

```
\func Namespace : \Set => List Positive
\func nclose (N : Namespace) : CoPset => -- coPset of all positives whose
                                          -- prefix in the binary tree starts with N
\func ndisjoint (N1 N2 : Namespace) : \Prop => -- disjoint as prefix codes
```

Required lemmas:

- `nclose_subseteq_l`, `nclose_subseteq_r`
- `ndisjoint_implies_disjoint : N1 ## N2 → nclose N1 ## nclose N2`
- `nclose_infinite` — every namespace contains infinitely many
  positives (needed for `fresh_inv_name`).

**Arend (new):** `src/iris/base_logic/lib/invariants.ard`:

```
\func own_inv (N : Namespace) (P : ProperUPred GlobalM)
  : ProperUPred GlobalM
  => mkProperExist Positive
       (λ i. mkProperAnd (mkProperPure (i ∈ nclose N)) (ownI i P))

\func inv (N : Namespace) (P : ProperUPred GlobalM)
  : ProperUPred GlobalM
  => mkProperPersistently
       (mkProperForall CoPset
         (λ E. mkProperImpl (mkProperPure (nclose N ⊆ E))
           (mkProperFUpd E (E ∖ nclose N)
              (mkProperSep (mkProperLater P)
                (mkProperWand (mkProperLater P) (mkProperFUpd (E ∖ nclose N) E True))))))
```

Port one-for-one:

| Rocq lemma                | Arend                          |
|---------------------------|--------------------------------|
| `own_inv_acc`             | `own_inv_acc`                  |
| `fresh_inv_name`          | `fresh_inv_name`               |
| `own_inv_alloc`           | `own_inv_alloc`                |
| `own_inv_to_inv`          | `own_inv_to_inv`               |
| `inv_persistent`          | `inv_persistent`               |
| `inv_alloc`               | `inv_alloc`                    |
| `inv_acc`                 | `inv_acc`                      |
| `inv_alter`, `inv_iff`    | derived from `inv_acc`         |
| `inv_split_l/r`           | derived                        |

### Phase 7 — re-thread WP and adequacy through `fupd`

**Rocq:** `program_logic/weakestpre.v`, the canonical definition

```
wp E e Φ ≡
  match to_val e with
  | Some v => fupd E E (Φ v)
  | None   => ∀ σ. state_interp σ ={E,∅}=∗
              ⌜reducible e σ⌝ ∗
              ∀ e' σ'. ⌜prim_step e σ e' σ'⌝ ={∅,∅,E}=▷=∗
              state_interp σ' ∗ wp E e' Φ
  end
```

**Arend (modify):**

- `src/iris/program_logic/weakestpre.ard` — replace `mkProperBUpd` with `mkProperFUpd E ∅`
  in `wp_pre`. Carry the mask `E` as an extra parameter (or keep `E = ⊤`
  in a first cut and add masks later). The contractivity proof is
  unchanged in structure — `fupd` is non-expansive (proved in phase 5),
  and the recursive `WP` argument is still under `mkProperLater`.
- `src/iris/program_logic/adequacy.ard` — bootstrap with `wsat_alloc` at the start; replace
  `bupd_later_iter_soundness` with the `fupd`-aware version (Rocq:
  `step_fupdN_soundness`). The shape of `wp_steps` is unchanged.
- `src/iris/program_logic/lifting.ard` — port `wp_lift_step_fupd` so heap operations are
  expressed against the new WP.

### Phase 8 — examples

- `src/tests/fact.ard` should still go through against the new WP.
  Two changes: the precondition becomes `True ⊢ fupd ⊤ ⊤ (wp ⊤ e Φ)`
  (or just unchanged if we hide the masks behind `⊤`), and the heap
  ownership predicate is now expressed through the heap projection
  of `GlobalM`.
- New small example: a one-shot ghost-state invariant
  `inv N (ℓ ↦ 0 ∨ ℓ ↦ 1)` plus a load that returns either 0 or 1.

---

## 4. File Map — Rocq ↔ Arend (after invariants land)

| Rocq                                  | Arend (current)          | Arend (after) |
|---------------------------------------|--------------------------|---------------|
| `algebra/ofe.v`                       | `src/iris/algebra/ofe.ard`            | + `LaterOFE`, `next`, `OptionOFE` morphisms |
| `algebra/cmra.v`                      | `src/iris/algebra/cmra.ard`           | + `ProdUCMRA` |
| `algebra/agree.v`                     | —                        | `src/iris/algebra/agree.ard` (new) |
| `algebra/excl.v`                      | `src/iris/algebra/excl.ard`  | unchanged |
| `algebra/gmap.v`                      | `src/iris/algebra/gmap.ard`  | + `gmap_view`-style frag/auth lemmas |
| `algebra/auth.v`                      | `src/iris/algebra/auth.ard`  | + `auth_frag`, `auth_alloc`, `auth_update` |
| `algebra/coPset.v`                    | —                        | `src/iris/algebra/coPset.ard` (new) |
| `algebra/gset.v`                      | —                        | `src/iris/algebra/gset.ard` (new) |
| `base_logic/upred.v`                  | `src/iris/base_logic/upred.ard`          | + `mkProperOwn`, `mkProperExceptZero` |
| `base_logic/derived.v`, `bi/*.v`      | `src/{interface,derived_laws}.ard` | + `FUpd` class, more derived rules |
| `base_logic/lib/iprop.v`              | (skipped — no `Σ`)       | — |
| `base_logic/lib/own.v`                | (skipped — no `Σ`)       | — |
| `base_logic/lib/wsat.v`               | —                        | `src/iris/base_logic/lib/wsat.ard` (new) |
| `base_logic/lib/fancy_updates.v`      | —                        | `src/iris/base_logic/lib/fancy_updates.ard` (new) |
| `base_logic/lib/invariants.v`         | —                        | `src/iris/base_logic/lib/invariants.ard` (new) |
| `stdpp/namespaces.v`                  | —                        | `src/stdpp/namespaces.ard` (new) |
| `program_logic/weakestpre.v`          | `src/iris/program_logic/weakestpre.ard`     | thread `fupd`/mask |
| `program_logic/lifting.v`             | `src/iris/program_logic/lifting.ard`        | thread `fupd`/mask |
| `program_logic/adequacy.v`            | `src/iris/program_logic/adequacy.ard`       | bootstrap `wsat`, use `step_fupdN_soundness` |

---

## 5. Pre-existing Holes

`grep -rn '{?}' src` returns only:

- `src/iris_heap_lang/lang.ard:112`, `src/iris_heap_lang/lang_subst.ard` (8 sites) — decidable
  equality on `String`. **Intentional** (per commit `c7066a0`); these
  block nothing in this plan.
- `src/stdpp/pmap.ard:972` — one helper in the induction principle
  (`entries_of_lookup` / `entries_of_nodup` shape). Not on the
  critical path for invariants either, but close it opportunistically
  if Phase 2's `gmap_view`-style lemmas hit it.

There is **no phase 0** in the original sense — the previous version of
this plan over-estimated the remaining holes based on a stale
`implementation_analysis.txt`. The CMRA / uPred / Auth / Heap layers
are fully closed in the current tree.

---

## 6. The Knot — `InvCMRA` and Recursion

The recursive bit is unavoidable: the invariant map stores
`Agree (Later (ProperUPred GlobalM))`, but `GlobalM` itself contains
that invariant map. Three ways to handle this in Arend, listed by
amount of work:

1. **Inline the recursion via `\record`/copattern unfolding.** Define
   `GlobalM` as a record whose fields are `heap : HeapCMRA.E`,
   `inv : Gmap _ (Agree (Later GlobalM-uPred))`, etc., and provide a
   COFE structure on `GlobalM.E` directly. The recursion is well-founded
   because the `Later` in `Agree (Later ...)` shifts the step index. The
   approach mirrors how Iris-Lite formalisations close the knot without
   a domain-equation solver.

2. **Use the existing `Inhabited` + Banach machinery** in
   `src/iris/algebra/ofe.ard`. Define `GlobalM` as a fixpoint of a contractive
   functor `F : OFE → UCMRA` where `F X = HeapCMRA × InvOver X × …`.
   Reuse `fixpoint` from `ofe.ard`. This is the cleanest path but
   requires that `fixpoint` work on the **UCMRA** category, not just
   on `OFE`. Lift `fixpoint` accordingly.

3. **Full `cofe_solver`.** Port `algebra/cofe_solver.v`. Heaviest;
   defer until impredicative invariants are actually required.

Recommended: **(1)** for the first cut. Switch to (2) if higher-order
ghost state (saved propositions) shows up.

---

## 7. Estimated Effort (very rough)

| Phase                                | Lines (est.) | Coq ref. |
|--------------------------------------|--------------|----------|
| 1. `mkProperOwn` + derived           | 200          | `upred.v` |
| 2. `Agree`, `coPset_disj`, `gset_disj`, `LaterOFE` | 1500 | `algebra/{agree,coPset,gset}.v` |
| 3. `ProdUCMRA` + `GlobalM` knot      | 300–700      | n/a (Iris uses `Σ`) |
| 4. `wsat`, `ownI`/`ownE`/`ownD`      | 400          | `wsat.v` |
| 5. `fupd` (concrete) + `BiFUpd`      | 300          | `fancy_updates.v` |
| 6. namespaces + `inv`                | 500          | `invariants.v` + `namespaces.v` |
| 7. retrofit WP/adequacy/lifting      | 500          | `program_logic/*.v` |
| 8. examples                          | 200          | n/a |
| **Total**                            | **~3800–4100** Arend lines | |

---

## 8. Suggested Order of Work

1. Phase 1 (`mkProperOwn`).
2. Phase 2 in this internal order: `LaterOFE` → `Agree` → `coPset_disj`
   → `gset_disj`. Reason: `Agree` and `coPset_disj` are independent,
   but `Agree (Later _)` is what the invariant map carries.
3. Phase 3 (`ProdUCMRA` + non-recursive `GlobalM₀`). At this point the
   existing factorial example should still compile under the broader
   resource (lifted through projections).
4. Phase 3.5 — close the recursion knot (§6 option 1).
5. Phase 4 (`wsat` + ownership primitives).
6. Phase 5 (`fupd`) — at this point you can already state, but not yet
   use, invariants.
7. Phase 6 (namespaces + `inv`).
8. Phase 7 (retrofit WP/adequacy).
9. Phase 8 (sanity check with a small invariant example).

---

## 9. Things Explicitly Out of Scope

- `gFunctors`/`Σ` parametricity. Without it: no modular ghost state, no
  separate libraries that "extend the resource". One monolithic
  `GlobalM` per language is the trade.
- `cofe_solver` (the recursive domain equation solver). Replaced by the
  hand-coded knot in §6.
- `BiFUpdPlainly`, plainness modality, later credits, atomic updates,
  prophecies, total WP. All are independent extensions; none are
  required for `inv`.
- Proof-mode tactics (`iMod`, `iInv`, `iApply`). All proofs in the
  Arend port are by direct manipulation of `ProperUPred`. Tactic
  development is its own project.
- `na_invariants`, `cancelable_invariants`. Standard `inv` first.
