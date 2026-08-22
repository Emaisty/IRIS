---
name: arend-debug
description: Use when an Arend proof step produces a confusing local error — type mismatch around `\cowith`/class fields, `mcases` complaints, dependent Σ-paths, Fin↔Nat coercion mismatches, `unfold` failing, `Dec.rec` vs `\case` reduction discrepancies, `Clauses are not allowed here` from a `\case` on Fin/inductive constructors, "Expected = Actual" mismatches with `{?hidden}` from `\property` args, or `ext` failing to recurse on nested Σ-paths. Trigger from arend-prove (or any other skill) when a single hole has been fought for more than one or two attempts and the error message looks like one of the symptoms below.
---

# Arend Local-Error Debugging

A catalog of recurring Arend pitfalls that consume disproportionate time in interactive proving. Each entry pairs the **error string** (so you can grep your own session) with the **root cause** and a **fix recipe**.

The base `arend` skill is assumed (CLI-only library access via `java -jar cli-1.11.0-full.jar -L $ARENDLIBS_PATH`, error-priority order). After applying a fix, re-typecheck the affected module via the CLI to confirm.

## When to invoke

Trigger this skill mid-`arend-prove` when:
- The same hole has produced two or more distinct error messages.
- An error mentions an *unrelated* term (e.g. complaining about `g` when you wrote `f`).
- A `pmap` / `ext` / `mcases` step that "should obviously work" doesn't.
- The expected and actual types differ by what looks like cosmetic reduction (`rec` vs `\case`, `Dec.rec` vs `\case`, `decideEq` vs `\case trichotomy`).

Do **not** invoke for syntax errors, unresolved references, or termination errors — those are surface issues handled directly (for unresolved references, use `-ai` to get import suggestions).

## Rule of thumb

Fix in this order: **shape mismatches → coercion ascriptions → reduction-shape bridges → dependent paths**. Most "annoying" errors are at the first two levels; people reach for `rewrite`/`coe` prematurely.

---

## Catalog

### 1. `Cannot resolve reference 'finCard'` (or any class field)

**Cause.** Class fields aren't free identifiers — they live behind dot-projection.

**Fix.** `(instance).finCard` instead of `finCard {instance}`.

```arend
-- ✗ finCard {Fib-FinSet f u} = …
-- ✓ (Fib-FinSet f u).finCard = …
```

### 2. `Expected 1 pattern` (after a comma in `mcases`)

**Cause.** `mcases` accepts one pattern per branch.

**Fix.** Nest mcases per scrutinee:

```arend
mcases \with {
  | yes p => mcases \with { | yes _ => … | no _ => … }
  | no q  => mcases \with { | yes _ => … | no _ => … }
}
```

### 3. `Cannot find matching subexpressions` from `mcases`

**Cause.** mcases needs a `\case` (or pattern-match `\elim`) **literally** in the current goal. A `\cowith` field whose body is `Dec.rec …` looks like a case analysis but is reached only via field projection — mcases can't always see through it.

**Fix.** Either `unfold` the field-defining function, or bridge via a helper that *is* a `\case`:

```arend
\func dec-ind {P : \Prop} (d : Dec P) : Nat
  => \case d \with { | yes _ => 1 | no _ => 0 }

\lemma decFin_dec-ind {P : \Prop} (d : Dec P) : (DecFin d).finCard = dec-ind d \elim d
  | yes _ => idp
  | no _ => idp
```

### 4. `Function 'X' cannot be unfolded`

**Cause.** `X` is defined by `\cowith` / `\new` / instance-anonymous-class. Such definitions don't have a body to unfold as a whole.

**Fix.** Don't `unfold X`. Instead unfold consumers, or wrap in a `\func` whose body you can unfold.

### 5. Spurious type mismatch on a parameter — `In: f`

**Symptom.** `Type mismatch. Expected: Fin r -> Fin s. Actual: Fin r -> Nat. In: f` — at a call site that should clearly use the outer `f`.

**Cause.** The outer parameter shadows a class field of the same name (commonly `Map.f`, `Section.f`, `Equiv.f`) inside a `\cowith` block.

**Fix.** Rename the outer parameter:

```arend
-- ✗ \func d {…} (f : A -> B) : QEquiv … \cowith
--      | f a => …  -- the second `f` is the field, not the parameter
-- ✓ \func d {…} (g : A -> B) : QEquiv … \cowith
--      | f a => (g a, …)
```

### 6. Fin↔Nat coercion in a dependent type fails to propagate

**Symptom.** Defining something like `\Sigma (u : Fin s) (Fib g u)` with `g : Fin r → Nat` produces `Expected: Fin r -> Fin s`. Arend retypes `g` instead of coercing `u`.

**Cause.** Coercion sites need a hint at *binding* time. The implicit `Fin → Nat` coercion is not exhaustively pushed through when the codomain is being inferred.

**Fix.** Ascribe at the use site:

```arend
\Sigma (u : Fin s) (Fib g (u : Nat))
```

The same applies to `pmap (\lam (x : Fin s) => (x : Nat)) p` for promoting Fin paths to Nat paths.

### 7. `Dec.rec (λ_ => 1) (λ_ => 0) d` ≠ `\case d \with { yes _ => 1 | no _ => 0 }` definitionally

**Symptom.** A `pmap (… Nat.+) IH` fails with the goal showing `rec {Nat} … (\case trichotomy …) Nat.+ Big …` while your term has `(\case decideEq …) Nat.+ countComp …`. The `decideEq` is unfolded on one side but not the other; `Dec.rec` is used on one side and `\case` on the other.

**Cause.** Two layers of cosmetic reduction differ:
- `\case` and `Dec.rec` aren't unified (despite both case-analysing on `Dec`).
- `decideEq` for `Nat`/`Fin` may unfold to `\case trichotomy …` opportunistically.

**Fix.** Pick one form and rewrite the other to it. Build a *bridge lemma* with the same `\case` shape as the user-written term, then prove the FinSet-side equals the bridge by induction (one `pmap` per case-split):

```arend
\func dec-ind {P : \Prop} (d : Dec P) : Nat
  => \case d \with { | yes _ => 1 | no _ => 0 }

\lemma countComp=BigSum-decInd … \elim r
  | 0 => idp
  | suc r' => pmap (_ Nat.+) (countComp=BigSum-decInd …)
```

### 8. `prop-pi` cannot infer its proposition

**Symptom.** `Cannot infer parameter 'A' of definition 'prop-pi'`.

**Cause.** `prop-pi {A : \Prop}` infers `A` from context, but coerced equality types (`g i = {Nat} u` where `u : Fin s`) don't unify under inference.

**Fix.** Supply the type explicitly:

```arend
prop-pi {g i = {Nat} u}
```

If even that fails, also pin the endpoints: `prop-pi {A} {a} {a'}`.

**Companion: `set-pi` for paths in a `\Set`.** A path `(a = b : Nat)` is propositional but `(a = b)` itself isn't a `\Prop` — `prop-pi` won't infer it. For path-fibres over a `\Set` (Nat, Fin, products of these), use `set-pi {S} {a} {b} {p} {q} : p = q`. When implicits won't unify, supply **all five** (carrier, both endpoints, both paths) — partial pinning leaves metavariables that don't propagate.

### 9. `ext` does NOT auto-recurse on nested `\Sigma`-paths

**Symptom.** `Type mismatch. Actual: \Sigma (\Pi {A : \Type} -> ...) (\Pi {A : \Set} -> ...). Expected: <single path>` while writing `ext (p1, (p2, p3))` or `ext (p1, ext (p2, p3))`. The "Actual" shows Π-types of `idp`/`set-pi` because Arend typechecked the inner `(p2, p3)` as a Σ-typed *value*, not as further `ext` arguments.

**Cause.** `ext (a, b)` takes *one* literal tuple and expects `b` to already be a path. A nested tuple gets typed as a Σ-value of unrelated type. Arend does not push `ext`-elaboration through the second component recursively. (Confusingly, the printed "Expected" type sometimes shifts as you nest — that's not `ext` recursing, it's just propagating shape constraints from the outer call.)

**Diagnostic cue.** If two `ext` shapes you try produce two *different* "Expected" types (one a Σ-path, the other a `.1`-component path), `ext` is silently inferring partial structure — your cue to abandon `ext` and switch to `Jl`. Don't keep trying nesting variants.

**Fix.** Either:
- Construct the inner path with `pmap (\lam y => (a, y)) (set-pi {…})` so the second arg is itself a path, not a tuple.
- For Σ-paths whose dependent component lives in a propositional/Set fibre, jump to **entry 10** (`Jl`-based recipe) — it's almost always the right tool, and trying to nest `ext` first wastes cycles.

### 10. Dependent Σ-paths across a coercion (Fin↔Nat) — `ext` gives up

**Symptom.** A retraction equation in a `QEquiv` between something Fin-valued and something Nat-valued; `ext` produces an inscrutable transport-equation as the second component.

**Cause.** The dependent path mixes a Fin-side path (e.g. `fin_nat-inj …`) with Nat-coerced equalities — `ext`'s synthesis has no canonical tactic, and the propositional fibre (`(S i : Nat) div nd = u`) is path-in-a-Set, not literally a `\Prop`.

**Fix — worked recipe (tested).** Bind everything explicitly, then `Jl` over the Fin-side path with an `\Pi`-quantified motive that defers the dependent-component proof:

```arend
| ret_f x =>
    \let
      | i : Fin r => x.2.1
      | k : Nat => (S i : Nat) div nd
      | hi : k < s => h i
      | u0 : Fin s => toFin k hi
      | base : k = u0 => inv toFin=id
      | firstPath : u0 = x.1 => fin_nat-inj (toFin=id *> x.2.2)
      | sigType : \Type =>
          \Sigma (u : Fin s) (\Sigma (i' : Fin r) ((S i' : Nat) div nd = u))
    \in Jl {Fin s} {u0}
           (\lam u' q =>
              \Pi (p' : k = u') -> (u0, (i, base)) = {sigType} (u', (i, p')))
           (\lam p' => pmap (\lam (z : k = u0) => ((u0, (i, z)) : sigType))
                            (set-pi {Nat} {k} {u0} {base} {p'}))
           {x.1} firstPath x.2.2
```

Three non-obvious load-bearing details:

1. **Bind every ingredient with explicit types** — `i`, `k`, `hi`, `u0`, `base`, `firstPath`, `sigType`. A bare `\let u0 := toFin k h` lets the elaborator unfold `u0` partway and lose the `\property` argument, producing the symptom in entry 10b below.
2. **Parenthesised type ascription inside the `pmap` lambda** — `((u0, (i, z)) : sigType)` not `(u0, (i, z)) : sigType`. The bare form parses the `:` as part of the lambda body and fails with "type mismatch: expected `sigType`, got `k = u0 -> Σ(...)`."
3. **Explicit `Jl {Fin s} {u0}` and `{x.1}` implicits** — without them, `Jl` may pick the unfolded `toFin`-form for `{a}` and you'll be back fighting `\property`.
4. **`set-pi` with all five implicits** — `{Nat} {k} {u0} {base} {p'}`. Partial pinning leaves metavariables that fail to propagate.

Alternative escape hatch: **`path (\lam k => (eq @ k, (a, ?path-at-k)))`** — explicit cubical interpolation. Rarely cleaner.

If neither works in a tight time budget, **leave the hole as `{?}` with a comment** rather than rewriting upstream code. The rest of the proof typechecks against `{?}`.

### 10b. "Expected = Actual" type mismatch with `{?hidden}` in both — `\property` arg lost

**Symptom.** `Type mismatch. Expected type: ... toFin (k) {s} {?hidden} ... Actual type: ... toFin (k) {s} {?hidden} ...` — printed Expected and Actual look character-for-character identical, both with `{?hidden}` for an implicit. Unification still fails. Most often happens during a `Jl`-based ret_f after binding `\let u0 := toFin k h`.

**Cause.** `toFin` (and similar) takes a `\property` argument — propositional, displayed as `{?hidden}` in error output. When you `\let`-alias the result and reference it through `Jl`/transport, the elaborator unfolds `u0` partway and instantiates the `\property` with a fresh metavariable instead of the original `h`. Both sides end up with a different `?hidden`, but they print the same.

**Fix.** Don't trust an alias to carry the `\property` arg. Bind every related value separately so the property witness has a name in scope:

```arend
\let
  | k : Nat => …
  | hi : k < s => h i      -- ← give the property witness a name
  | u0 : Fin s => toFin k hi
```

Then references to `u0` are stable. See entry 10's worked recipe.

**Diagnostic cue.** Whenever Expected and Actual print *identically* and both contain `{?hidden}`, suspect a `\property` arg being re-metavariabled. This is not a "real" type mismatch — it's a unification failure on an invisible argument.

### 11. `Clauses are not allowed here` / `Cannot infer an expression` from a `\case` on Fin

**Symptom.** A `\case x \with { | 0 => … | fsuc k => … }` where `x : Fin (suc r)` works in some contexts (e.g. inside a `FinProd`/`FinSum` lambda whose return type is constrained) and fails in others (e.g. as the entire body of a `\func`, or inside `\new Array Nat s (\lam u => …)`) with `Clauses are not allowed here` or `Cannot infer an expression` at the `\case` keyword.

**Cause.** Arend's elaborator must know `x`'s type *before* parsing the constructor patterns — otherwise it can't resolve `0` / `fsuc k` to constructors of `Fin (suc r)`. In the failing contexts, the surrounding context doesn't push the type down to the scrutinee fast enough; the parser then treats `\with { | … | … }` as if it were an unattached top-level clause block.

**Fix.** Three approaches in increasing order of intervention:

1. **Type-ascribe the scrutinee** — usually enough:
   ```arend
   \case (x : Fin (suc r)) \with { | 0 => … | fsuc k => … }
   ```
2. **Switch to Nat coercion + Nat patterns** — loses `k : Fin r` you'd get from `fsuc k`; need a separate bound proof:
   ```arend
   \case (x : Nat) \with { | 0 => … | suc k => … }
   ```
3. **Pull the case out into a `\func ... \elim k`** — always works because `\elim` puts the type of `k` directly into the elaboration scope:
   ```arend
   \func myCase {r : Nat} (k : Fin (suc r)) : T \elim k
     | 0 => …
     | fsuc k => …
   ```
   Same pattern for any other inductive type whose `\case` mysteriously refuses to elaborate.

### 12. `\case \elim x \with { … }` — `\elim` is not part of `\case`

**Symptom.** Writing `\case \elim x \with { … }` produces `Clauses are not allowed here` or another opaque parser error.

**Cause.** `\elim` is for top-level pattern matching in a `\func` (`\func foo (x : T) : R \elim x | … | …`), *not* for `\case`. `\case` takes only an expression and a `\with` block.

**Fix.** Drop the `\elim`: `\case x \with { … }`. If the elaborator now can't see the inductive structure of `x`, see entry 11 — type-ascribe, switch to Nat-coercion patterns, or pull out into a `\func ... \elim`.

---

## Workflow when stuck

1. **Replace the failing subterm with `{?}`.** Re-typecheck via the CLI and read the inferred goal — it's far more informative than the original error.
2. **Compare expected vs actual shape token-by-token.** If they differ by `\case` ↔ `rec`, by an unfolded `decideEq`, or by an explicit coercion, that's the issue — not the surrounding logic. If they look *identical* but mention `{?hidden}`, suspect a `\property` argument (entry 10b).
3. **If `ext` produces two different "Expected" types across two nesting variants**, stop trying to nest `ext` — it's not auto-recursing, it's just propagating shape constraints. Switch to `Jl` (entry 10).
4. **If the error mentions a parameter name with a confusing type**, check for field-name shadowing in any enclosing `\cowith`.
5. **If `mcases` complains**, run `unfold` on whatever introduces the `\case` you want — the field-projected body may not be visible.
6. **If you've made three attempts**, leave `{?}` and report. Do not rewrite the surrounding lemma to dodge a single subterm.

## What this skill is *not* for

- Searching arend-lib (use the host skill's `-ps` / `-ss`).
- Strategic decisions about proof structure (those belong upstream — this is for tactical local errors).
- Termination, universe-level, or unresolved-reference errors — fix those directly without invoking this skill (use `-ai` for unresolved-reference candidate suggestions).
