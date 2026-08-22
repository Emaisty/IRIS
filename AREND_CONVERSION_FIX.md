# Arend conversion-checker fix — unblocking IRIS §A7 (`wsat` allocation)

**Date:** 2026-07-16
**Component patched:** Arend (`~/Projects/Arend`), `base/src/main/java/org/arend/core/expr/visitor/CompareVisitor.java`
**Goal:** make the five `wsat` allocation lemmas in `src/iris/base_logic/lib/wsat_alloc.ard` typecheck. They are
proved in full (no `{?}` holes) and are structurally correct, but Arend's definitional-equality
checker **diverged** (> 75 CPU-min for a single lemma, no result).

---

## 1. The problem

Comparing two terms whose types live over the recursive resource domain

```
iResUR S  ≅  F(iResUR S)          -- the cofe_solver / recursive-domain solution
wsat_invR = gmap_viewR gname gnameCountable (LaterOFE (iPropO S))
```

sent Arend's conversion checker into an effectively non-terminating loop whenever a term of type
`own … (gmap_view_auth …)` at `wsat_invR` had to be converted in a non-trivial context (e.g.
passed as a lemma argument).

Every **proof-level** workaround was tried and ruled out beforehand:

- `\sfunc`-sealing `own_val` — did not stop the divergence;
- `\sfunc`-sealing `own` — could not even compile (a `ProperUPred`/`Gmap` conversion wall);
- moving every `bupd` combinator into generic fused lemmas — did not stop the divergence.

So the fix had to be in **Arend itself**.

## 2. Root cause (established by profiling, not guessing)

A minimal reproducer, `src/bench_repro.ard`

```
bupd_mono A_I A_I (refl A_I)          A_I = ∃ g. own g (gmap_view_auth …)   -- at wsat_invR
```

was run under periodic `jstack` sampling. **100 % of the CPU was in `CompareVisitor`** (the
comparison recursion `compare → normalizedCompare → compareLists → visitDefCall → visitFunCall
→ compare …`), and essentially **none** in `NormalizeVisitor`.

Instrumenting a comparison-result cache revealed the decisive fact: the set of *distinct closed
sub-term pairs* being compared **grew linearly without bound** (24 k → 800 k → 1.8 M → 2.8 M …).
That is the signature of the recursive domain being **unfolded infinitely**:

- `CompareVisitor.compare` normalizes each side to WHNF (`normalize(WHNF)`) **before** it can try
  congruence. For a call of an unfoldable `\func`, WHNF unfolds the head.
- So comparing `iResUR S` vs `iResUR S` **unfolds the tower** (`… F(iResUR S) …`) instead of
  just noticing "same definition, same argument `S`". Each unfolding produces new, structurally
  distinct closed subterms → unbounded work.

Arend already has an identity fast-path (`expr1 == expr2`) and an *all-or-nothing*
`nonNormalizingCompare` congruence path, but the latter forbids normalizing arguments, so it
fails as soon as any leaf needs a reduction and the checker falls back to the unfolding
`normalizedCompare`.

## 3. The fix (final audited form)

Two changes in `CompareVisitor.java`, both sound and localized.

### (a) Congruence **before** unfolding — the core fix

Before the unfolding `normalize`, if both sides are calls of the **same unfoldable `\func`**, are
**currently ground** (no unsolved term or universe metavariables anywhere) and **closed** w.r.t.
the current binder substitution, first try to prove them equal by comparing arguments
(`visitDefCall`, which does *not* unfold the head). Already-solved term metavariables may be
followed for this one-shot congruence attempt; unsolved term metavariables and inference-level
variables disable it. Ordinary universe parameters are allowed. On success → equal (return
`true`). On failure → fall through to the existing `normalizedCompare`.

- **Sound:** `a₁ = b₁, …, aₙ = bₙ ⇒ f a₁…aₙ = f b₁…bₙ` (congruence of a function over equal
  arguments). Completeness is preserved: if arguments are not equal the calls may still be equal
  via unfolding, and we still fall through to it.
- **No lasting effects on failure:** the speculative attempt is wrapped in the *existing* checkpoint pattern
  `myEquations.saveState(state)` … `myEquations.loadState(state)` (mirroring the code already at
  `CompareVisitor` ~line 2147), so a failed attempt restores inference/equation state. The
  current-groundness cache is cleared at every rollback.
- **Why it terminates the tower:** `iResUR S` vs `iResUR S` now compares the argument `S` (trivial)
  instead of unfolding `F(iResUR S)`.

### (b) A ground-pair comparison memo

A per-visitor identity-pair memo memoizes successful `CMP.EQ` comparisons only when both
expressions contain **no inference references at all** and are closed w.r.t. the binder
substitution. This stricter condition is deliberate: a solved metavariable may later be unsolved
by an outer equation checkpoint, so it is acceptable for a one-shot congruence proof but not for
a persistent memo entry.

### The soundness lesson that shaped the gate

The **first** version fired congruence on terms that still contained **metavariables** and
**over-committed** them: comparing `f ?m` vs `f 5` solved `?m := 5` (forcing the arguments equal)
even though `f` might be equal regardless of its argument. That corrupted inference and **broke
arend-lib's `Arith.Nat`** (termination check + type mismatch on the recursive lemmas `*-comm`,
`triGreater`).

**Fix:** gate congruence on terms with no **unsolved** inference variables, and gate memoization
more strictly on terms with **no inference references**. Inference-level variables are checked
as well. Ground terms cannot over-commit, so `Arith.Nat` compiles cleanly again, while the
elaborated `wsat_invR` payloads still hit the fast path.

The validation toggles and shutdown debug counters have been removed from the final patch.

## 4. One proof-side fix it surfaced

Once the proof actually *completed*, one pre-existing gap (previously hidden by the divergence)
appeared in `src/iris/base_logic/lib/wsat_alloc.ard`: `ucmra_unit_{left,right}_id_dist n x` where `M : UCMRA` is a
`\let`-binding (`=> iResUR S`). Let-bindings are not typeclass instances, so instance resolution
for the implicit `{U : UCMRA}` failed. Fixed by passing the instance explicitly: `… {M} n x`.

## 5. Results

| Item | Before | After |
|---|---|---|
| `bench_repro` (reproducer) | > 75 CPU-min, diverged | **4.8 s** |
| `src/iris/base_logic/lib/wsat_alloc.ard` — all 5 lemmas | diverged (> 75 min *per lemma*) | **25 m 04 s cold rebuild, 0 errors, 0 holes** |
| arend-lib `Arith.Nat` | (clean) | **clean** (regression avoided) |

The earlier warm run was 3 m 35 s. The final audit deliberately ran after invalidating many
dependency binaries, so it also rechecked substantial parts of `wsat` and `own`; all five target
lemmas were still finite. The final cold per-lemma slow warnings included `wsat_alloc` 32 s,
`ownD_alloc_fresh` 9 s, `ownI_auth_alloc` 3 m 19 s, `ownI_alloc` 5 m 38 s, and
`ownI_alloc_open` 4 m 32 s.

**IRIS §A7 (`wsat` allocation) is complete:** `wsat_alloc`, `ownD_alloc_fresh`, `ownI_auth_alloc`,
`ownI_alloc`, `ownI_alloc_open` all typecheck with no holes.

## 6. Build / run

```bash
# rebuild the patched Arend CLI
cd ~/Projects/Arend && ./gradlew :cli:jarDep      # → cli/build/libs/cli-1.11.0-full.jar

# typecheck the allocation module
cd ~/Aarhus_uni/MSc/IRIS
java -Xmx16g -jar ~/Projects/Arend/cli/build/libs/cli-1.11.0-full.jar \
     -L ~/.arend/libs --no-daemon wsat_alloc
```

## 7. Validation status

- [x] Reproducer `bench_repro` fast (4.8 s)
- [x] `wsat_alloc.ard` — all 5 lemmas verify, 0 errors, 0 holes (final cold audit: 25 m 04 s)
- [x] arend-lib `Arith.Nat` regression avoided (final jar: 572 ms, 0 errors)
- [x] Arend JUnit audit completed — the initial full `./gradlew test` passed in 1 m 02 s; the
  final focused `ComparisonTest.congruenceBeforeRecursiveHeadUnfolding` passes. **Caveat:** a
  clean final full-suite rerun is not certified because `:cli:buildPrelude --rerun-tasks` prints
  `Cannot locate module ... While persisting: Prelude`, exits successfully, and removes the
  generated `Prelude.arc`; Prelude-dependent tests then fail with null Prelude definitions.
  The same generator failure reproduces on a clean `master` checkout and is independent of this
  `CompareVisitor` patch.
- [x] IRIS `--double-check` — `wsat_alloc` elaborated core re-verified
- [x] `own` / `weakestpre` controlled rebuild audit — **mixed result / acceptance criterion
  failed**: `own` is 5 m 24 s patched vs 4 m 39 s unpatched (~16% slower), while
  `weakestpre` is 3.6 s patched and the unpatched checker was still running after 3 minutes.
- [x] Added Arend regression test `congruenceBeforeRecursiveHeadUnfolding` (5 s timeout)
- [x] Removed debug counters/toggles; built and shipped `cli-1.11.0-full.jar`
  (SHA-256 `63288be1dc1e8ca6810a0a37b0c73b0e83163797dea76c19cebf504e4aeebf81`)

## 8. Effect outside IRIS and master-branch decision

This is a change to Arend's global definitional-equality algorithm, so it affects **all** Arend
projects, not only IRIS. The intended semantic result is unchanged: congruence can only establish
an equality that was already definitionally valid, and failed speculation falls back to the old
normalizing comparison. The observable effects are performance and per-comparison memory use.
The controlled IRIS measurements show both large wins and a measurable loss (`own`, ~16%).

**Decision: do not merge this implementation into `master` unchanged.** The core idea and the
regression test are suitable for an upstream PR, but the PR needs (1) a bound or cheaper precheck
for failed congruence attempts, (2) a clean full-suite run after the independent Prelude-generator
fixture problem is fixed/worked around, and (3) a minimal rebase onto `master`. The working Arend
checkout is on `consoleTooling2`, whose HEAD is not `master`, so the current working-tree diff
must not be submitted as a direct master commit.

## 9. Files touched

- `~/Projects/Arend/base/src/main/java/org/arend/core/expr/visitor/CompareVisitor.java`
  — congruence-before-unfolding, inference/closedness checks, rollback-aware groundness cache,
  and strict comparison memo (no debug toggles).
- `~/Projects/Arend/src/test/java/org/arend/term/expr/visitor/ComparisonTest.java`
  — focused recursive-head non-divergence regression test.
- `~/Aarhus_uni/MSc/IRIS/src/iris/base_logic/lib/wsat_alloc.ard`
  — two `{M}` instance annotations on `ucmra_unit_{left,right}_id_dist`.
- `~/Aarhus_uni/MSc/IRIS/cli-1.11.0-full.jar` — finalized audited binary.
- `src/bench_repro.ard` was temporary and is no longer present.
