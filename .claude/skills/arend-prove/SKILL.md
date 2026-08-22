---
name: arend-prove
description: Use when asked to prove something in Arend interactively — guided hole-by-hole proving with explicit checkpoints, hardest-case-first ordering, and proof methodology. Builds on the base `arend` skill (CLI tools, search workflow, error priority).
---

# Arend Proof Methodology (Interactive)

Non-negotiable constraints for writing Arend proofs in interactive mode. The base `arend` skill is assumed (CLI-only library access via `java -jar cli-1.11.0-full.jar -L $ARENDLIBS_PATH`, `-ps`/`-ss`/`-ag` workflow, error-priority order). This file adds the proving-specific discipline on top.

## One Hole at a Time

Fill one hole (`{?}`), typecheck, review diagnostics, repeat. Never fill multiple holes before checking.

- **`{?}` is acceptable** for placeholders you're not actively working on — Arend treats them as well-typed terms, so dependent code still typechecks.
- **Typecheck after each change.** Run the CLI on the changed module — e.g. `java -jar cli-1.11.0-full.jar -L $ARENDLIBS_PATH <Module.Path>` — and read the diagnostics. No exceptions. If you've started a daemon (see the base skill), this is near-instant.

## When stuck on a single hole — delegate to `arend-debug`

If the same hole produces two or more distinct error messages, or the error matches one of:

- `Cannot resolve reference 'finCard'` (or any class-field name)
- `Expected 1 pattern` from `mcases`
- `Cannot find matching subexpressions` from `mcases`
- `Function 'X' cannot be unfolded` (where X is a `\cowith`/`\new` definition)
- `Type mismatch` naming a parameter that "obviously" has the right type (likely field-name shadowing)
- Mismatch between `\case decideEq …` and `Dec.rec … (\case trichotomy …)` shapes
- `Cannot infer parameter 'A' of definition 'prop-pi'`
- A confusing dependent Σ-path involving Fin↔Nat coercion
- `Clauses are not allowed here` or `Cannot infer an expression` from a `\case` on a Fin / inductive value
- A `\case \elim x` rejected with a parser error (`\elim` is not part of `\case`)

…invoke the `arend-debug` skill rather than continuing to guess. It contains a catalog of these specific failure modes with fix recipes. Don't waste cycles re-deriving them.

## Work on the Hardest Case First

### Across Lemmas

Go directly to the target lemma. Don't fill in `{?}` in helper lemmas first.

Move holes earlier in the file by replacing a `{?}` proof with references to simpler lemmas:

```arend
-- Before:
\lemma main_theorem : A = C => {?}

-- After:
\lemma lemma1 : A = B => {?}
\lemma lemma2 : B = C => {?}
\lemma main_theorem : A = C => lemma1 *> lemma2
```

### Within a Proof

When a proof has multiple cases, use `{?}` for easy cases and work on the hardest one first. If the hard case fails, effort on easy cases is wasted.

```arend
\lemma example (n : Nat) : P n \elim n
  | 0 => {?}           -- fill in later
  | suc n' => {?}      -- WORK ON THIS FIRST if it's harder
```

## Checkpoint Protocol

Before writing code in Arend create an informal proof plan:

1. **Initial assessment** — informalize the expected type.
2. **Look at relevant parts of libraries** — what's already proven in arend-lib and the current project (use `-ps` / `-ss` / `-ag`).
3. **Look for generalizations** — see *Look for natural generalizations* below. If the proof structure is really about a more abstract principle, surface it now so the user can choose to prove the general form.
4. **Proof plan** — write an informal plan that fits maximally well to what's already there. Suggest lemmas for arend-lib if the gap is general.

Before proceeding to actual code write your plan and ask if it's ok. Example:

```
Context: n r s : Nat, nd : Nat, S : \Pi (Fin r) -> Fin n, h : \Pi (i : Fin r) -> (S i : Nat) div nd < s
Expected type: BigSum (\new Array Nat s (\lam u => countComp nd S u)) = r

Proof plan:
countComp counts sizes of fibers of the function S(i) div nd and r is the domain size.
This claim can be naturally derived from the following general statements:
 1) Fibers are disjoint, 2) Domain is the union of fibers, 3) sum of cardinalities
of disjoint sets equals cardinality of the union. 1 and 2 reasonable to prove for all
functions, 3 for functions between finite sets.

Proceed to implementation?
```

As soon as the user agrees to proceed, fill the hole. After each hole is filled:

1. **Typecheck** — re-run the CLI on the affected module and verify no new errors.
2. **Report** — tell the user what was filled and what remains.
3. **Ask** — get confirmation before proceeding to the next hole.

Example checkpoint message:

```
✓ Filled hole in `lemma1` (base case)
  Remaining holes: 2 (in `lemma2`, `main_theorem`)

  Proceed to next hole? [y/n]
```

## Sanity-check formal definitions before proving

Before proving a target lemma whose statement involves a freshly-formalized definition translated from prose (a paper, a textbook, a whiteboard sketch), **sanity-check both sides at concrete small inputs**. Pick the smallest non-trivial parameter values and compute each side by hand (or in your head); confirm they match.

Why: prose definitions are routinely ambiguous about weak vs. strong constraints, 0- vs. 1-indexing, "include the trivial case" vs. "skip it", whether quantifiers are over all elements vs. only "non-zero / non-degenerate" ones. An off-by-one or convention mismatch makes the target lemma *false*, and you can spend many proof attempts before realising. A 30-second hand calculation at the smallest interesting input catches this.

Apply this *before* writing your proof plan, especially when:
- The definition involves a finite-set indexing where the encoding could be either inclusive or exclusive (positive vs. non-negative parts; subsets-of-size-k vs. arbitrary maps; partitions vs. multisets).
- The definition has a conditional that's easy to drop in formalization ("skip the empty / zero / trivial case").
- The source is 1-indexed and the formalization is 0-indexed (or vice versa).

If the small-case computation reveals a mismatch, **fix the definition first** before attempting the proof. Don't try to prove a false lemma.

## Common Proof Patterns

### Induction
```arend
\lemma example (n : Nat) : P n \elim n
  | 0 => base-case-proof
  | suc n' => inductive-step-proof
```

### Path Induction
```arend
\lemma path-example {A : \Type} {a b : A} (p : a = b) : Q a b p =>
  \case p \with { | idp => reflexive-case }
```

### Case Analysis
```arend
\case expression \with {
  | pattern1 => result1
  | pattern2 => result2
}
```

### Using mcases
```arend
mcases \with {
  | yes _ => result1
  | no _ => result2
}
```

## Look for natural generalizations

The strongest cleanup move in Arend is **lifting the lemma to a more general statement** when the proof never used the specific shape of its inputs. A specialized proof tangled in coercions often factors into a clean general lemma plus a small bridge — the general lemma becomes reusable, and the original target falls out as a corollary.

**Detect generalization opportunities** during the proof plan and again after the proof typechecks. Ask:

- Did the proof structure *use* the specific shape of any parameter, or did it just route the parameter through? (E.g. our `bigFib s nd S` proof never used the `S`/`nd`/`div` structure — only the function `\lam i => (S i : Nat) div nd : Fin r → Nat` and a bound. That's a sign the lemma is really about an arbitrary `g : Fin r → Nat`, or further, an arbitrary `g : A → B`.)
- Is the proof an instance of a textbook principle? (Disjoint union of fibres, total space ≃ domain, finite-sum reindexing, induction on a list, etc.) Textbook principles are almost always library-level statements waiting to be extracted.
- Are the awkward parts of the proof (coercions, transports, `Jl` over a propositional fibre) confined to a *narrow* part — typically a per-fibre or per-element bridge? If yes, generalize away the awkwardness: state the clean lemma over abstract types, and isolate the coercion in a small bridge equivalence.

**When you spot one, surface it before implementing.** The plan should explicitly mention:
- the general statement,
- which hypotheses can be dropped or weakened,
- where in arend-lib a similar lemma might already live (use `-ps` with the general signature shape to scan),
- and the cost of the bridge between general and specific.

Then ask the user whether to prove the general form or the specific form. Worked example:

> "I notice the proof of `countComp_total` doesn't use the `S`, `nd`, or `div` structure — only that `g : Fin r → Nat` is bounded. The natural generalization is `\Sigma (b : B) (Fib g b) ≃ A` for any `g : A → B` (a standard HoTT fact). The original lemma falls out by setting `g i := toFin (S i div nd) (h i)` and bridging the per-fibre Nat-equality to Fin-equality via `sigma-right`. Prove the general form instead?"

**Anti-pattern.** Specializing the proof to the concrete inputs and then leaving generalization as a TODO. The general form is usually *easier* to prove (no coercions to fight) and the bridge is mechanical — generalize first, specialize as a corollary.

## Proof Cleanup

After getting a proof to work, clean it up immediately:

- Combine redundant steps.
- Check if simpler arend-lib lemmas can replace manual proofs (re-run `-ps` with the cleaned-up subgoal shapes).
- Remove unnecessary intermediate `\let` or `\have` bindings.
- **Re-check for generalizations** (see section above) — they're easier to spot once the proof typechecks.
- Find the truly minimal proof.

## Verification

Never declare a proof complete while:

- `{?}` holes remain in agreed scope.
- Error diagnostics exist.
- Typechecking fails.
