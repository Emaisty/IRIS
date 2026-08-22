# Two terminating examples for argument-first conversion checking

**Related change:** [Arend PR #132 — Compare function arguments before unfolding calls](https://github.com/arend-lang/Arend/pull/132)  
**Patch tested here:** PR commit `b67bd9594af03d426614cc749a8c46e601e5aa9b`, rebased onto Arend `v1.12.0` as local commit `84c2914842328036e509eeb2641f32a0d62a7ff7`  
**Purpose of this note:** give one example in ordinary recursive-domain mathematics and one concrete example from the Arend port of Iris.

The change is small, but the order of operations matters. Suppose conversion checking must decide

```text
f a₁ ... aₙ  =?=  f b₁ ... bₙ.
```

The old path first tries a deliberately non-normalizing comparison. If one pair of arguments is equal only after a small reduction, that attempt fails. The fallback then weak-head normalizes both *whole calls*. Since `f` is unfoldable, this unfolds `f` before returning to its arguments. For an ordinary finite definition this is usually harmless. For the carrier of a recursive domain, however, unfolding `f` can expose another occurrence of that carrier, and the comparison can grow without ever reaching the small reducible argument that would have settled the original question.

PR #132 inserts one additional sufficient test before that fallback:

1. both expressions must be calls of the same `\func` definition;
2. the definition must not be a sealed `\sfunc`;
3. compare universe levels and arguments with `visitDefCall`, temporarily using equality mode;
4. if that succeeds, accept by congruence without unfolding the common head;
5. if it fails, restore the comparison result and run the old weak-head-normalizing path.

Thus the new branch can only establish an equality of the standard form “equal arguments give equal applications.” It is not the only conversion rule: failure still falls back to unfolding, which is essential for definitions such as `constZero 0` and `constZero 1` whose applications are equal even though their arguments are not.

The observable difference in the two examples below is therefore not which mathematical equality is valid. It is whether the checker discovers an already-valid equality by a finite congruence argument, or commits first to an unbounded unfolding path.

## Example 1: a recursive domain equation from general mathematics

### Mathematical setting

Recursive domains occur in denotational semantics, step-indexed models, complete metric spaces, and guarded recursion. A typical construction starts with a category whose objects carry a notion of approximation and with a contractive endofunctor

```text
F : C → C.
```

Contractiveness permits construction of a fixed point `μF` together with an isomorphism

```text
unfold : μF ≅ F(μF).
```

One standard construction builds a tower of finite approximations

```text
D₀, D₁ = F(D₀), D₂ = F(D₁), ...
```

and defines the carrier of `μF` as coherent threads through this tower. Its implementation contains projections to successive approximants, coherence equations, a limit/completion operation, and the fold/unfold isomorphism. Although every individual operation is mathematically legitimate, blindly expanding the entire carrier while comparing two types can expose the next tower layer, then the next one, and so on.

Assume the library exposes this construction through a definition

```text
recursiveCarrier (F : ContractiveFunctor) : CompleteDomain
```

and assume that a caller writes the same functor through a small reducible wrapper:

```text
\func normalizeFunctor (F : ContractiveFunctor) => F
```

The checker may then be asked to decide

```text
recursiveCarrier (normalizeFunctor F)
  =?=
recursiveCarrier F.
```

The mathematics is immediate:

```text
normalizeFunctor F  ≡  F
--------------------------------  congruence
recursiveCarrier (normalizeFunctor F)  ≡  recursiveCarrier F
```

No fact about the internal tower is needed. In particular, proving this conversion should not require comparing `D₀`, `D₁`, `D₂`, and all subsequent approximants.

### Why the old comparison order can fail to terminate

At a high level, the old execution is:

```text
compare recursiveCarrier(normalizeFunctor F), recursiveCarrier(F)
  ├─ pointer identity: fails; the two applications were constructed separately
  ├─ non-normalizing structural comparison
  │    └─ compare normalizeFunctor(F), F without reducing: fails
  └─ normalize both whole applications to weak-head normal form
       ├─ unfold recursiveCarrier(normalizeFunctor F)
       └─ unfold recursiveCarrier(F)
```

Unfolding `recursiveCarrier` exposes its tower/limit representation. That representation refers to the recursive solution through later approximants or through the fold/unfold structure. The next structural comparison therefore contains a fresh pair morally equivalent to the original pair, but under one more layer of `F`. Repeating the same policy produces

```text
μF
F(μF)
F(F(μF))
F(F(F(μF)))
...
```

rather than reducing the harmless `normalizeFunctor F` leaf. The checker can remain busy, allocate fresh comparison pairs, and consume CPU indefinitely without emitting a type error or a goal. This is divergence of a conversion *procedure*, not evidence that the domain equation is invalid.

### Why the new comparison order terminates

With PR #132, after the strict non-normalizing attempt fails but before either common head is unfolded, the checker observes that both expressions call the same definition `recursiveCarrier`. It keeps that head fixed and compares only its levels and arguments:

```text
compareFunCalls
  recursiveCarrier(normalizeFunctor F)
  recursiveCarrier(F)
    └─ visitDefCall
         └─ compare normalizeFunctor(F), F
              └─ reduce normalizeFunctor(F) to F
                   └─ success
```

Congruence now closes the original comparison. The tower representation is never requested. The result changes from an unbounded check to acceptance, while the accepted equality is exactly the equality already justified by congruence.

### Executable kernel regression that isolates this behavior

The test added by PR #132 constructs the smallest possible version of the same comparison shape. It first typechecks two harmless surface definitions:

```arend
\func idType (A : \Type) => A
\func loop (A : \Type) => A
```

The Java regression test then replaces the core body of `loop` by

```text
loop A := loop (idType A)
```

and directly asks the kernel comparison visitor to compare

```text
loop (idType Type₀)  =?=  loop Type₀.
```

The two calls are definitionally equal by the one-step argument reduction

```text
idType Type₀  ↦  Type₀.
```

Normalizing either complete `loop` call, however, produces another `loop` call forever. The test therefore has a five-second timeout and succeeds only if comparison uses the finite argument proof before trying to unfold the head.

The body replacement is intentional. It is a kernel-level test of the conversion algorithm, not a proposal to admit an unguarded surface-level Arend definition. It isolates the looping shape that a much larger, total recursive-domain construction can expose indirectly. This makes the regression small, deterministic, and independent of the domain solver library.

### Why fallback must remain

The PR also contains a complementary regression:

```arend
\func constZero (n : Nat) => 0
```

For

```text
constZero 0  =?=  constZero 1
```

the argument-first attempt correctly fails because `0` is not equal to `1`. The old fallback then unfolds both calls to `0` and accepts. Conversely, comparing `idNat 0` with `idNat 1` still rejects. Together, these tests establish the intended control flow:

| Calls | Argument comparison | Fallback | Result |
|---|---:|---:|---:|
| `loop (idType Type₀)` / `loop Type₀` | succeeds | not entered | accept finitely |
| `constZero 0` / `constZero 1` | fails | both reduce to `0` | accept |
| `idNat 0` / `idNat 1` | fails | results differ | reject |

This example is not specific to Iris. The same conversion shape arises whenever a proof assistant implements a recursive object behind a function call and a client presents one of its parameters through a definitionally trivial wrapper. Contractive fixed points, completions, inverse limits, recursive semantic universes, and step-indexed models are all natural sources.

## Example 2: the concrete Iris `init` boundary

### The recursive Iris model

Iris assertions are predicates over a resource algebra, while the resource algebra itself contains assertions. In the Arend port, the relevant definitions are in `src/iris/base_logic/lib/iprop.ard`:

```arend
\func iResF (S : gFunctors) : URFunctor =>
  discrete_funURF (\lam (i : gid S) =>
    gmapURF gname gnameCountable (S.gFunctors_lookup i).gFunctor_F)

\sfunc iProp_result (S : gFunctors) : Solution (uPredOF (iResF S)) =>
  solver_result (uPredOF (iResF S))
    (uPredOF_applyCOFE (iResF S))
    (uPredOF_contractive (iResF S) (iResF_contractive S))
    (uPredOF_inhabited (iResF S))

\func iPrePropO (S : gFunctors) : COFE =>
  (iProp_result S).solution_car

\func iResUR (S : gFunctors) : UCMRA =>
  urFunctor_apply (iResF S) (iPrePropO S)

\func iProp (S : gFunctors) : \Set =>
  ProperUPred (iResUR S)
```

Schematically, this is the recursive equation

```text
iProp(S) = uPred(iResUR(S))
iResUR(S) = iResF(S)(iPrePropO(S))
iPrePropO(S) ≅ uPred(iResUR(S)).
```

`iProp_result` is sealed with `\sfunc`, corresponding to the opaque module around the solution in Rocq Iris. Fold and unfold are exposed explicitly through `iProp_fold` and `iProp_unfold`. The port therefore does not rely on unrestricted unfolding as a proof of the recursive equation.

### The exact application where official Arend 1.12 stalls

The abstract allocation combiner in `src/iris/program_logic/adequacy.ard` has this interface:

```arend
\lemma init_from_allocations {cnt : Countable Loc} {S : gFunctors}
    (sigma : State cnt)
    (heapAlloc : properUPred_ent mkProperEmp
      (mkProperBUpd (heap_package {cnt} {S} sigma)))
    (worldAlloc : properUPred_ent mkProperEmp
      (mkProperBUpd (world_package {S})))
  : properUPred_ent mkProperEmp
      (mkProperBUpd
        (mkProperExist1 (irisGS cnt S)
          (\lam H => init_resources H sigma)))
```

It typechecks with the official release. The two producer lemmas also typecheck independently:

```arend
gen_heap_init Hpre.iris_heap_pre sigma.heap
wsat_alloc Hpre.iris_wsat_pre
```

The public concrete bootstrap merely supplies those results to the abstract combiner:

```arend
\lemma init {cnt : Countable Loc} {S : gFunctors}
    (Hpre : irisGpreS cnt S) (sigma : State cnt)
  : properUPred_ent mkProperEmp
      (mkProperBUpd
        (mkProperExist1 (irisGS cnt S)
          (\lam H => init_resources H sigma))) =>
  init_from_allocations sigma
    (gen_heap_init Hpre.iris_heap_pre sigma.heap)
    (wsat_alloc Hpre.iris_wsat_pre)
```

The expected second argument contains

```text
heap_package sigma
  = mkProperExist1 (gen_heapGS Loc cnt Value S)
      (λ G => gen_heap_interp G sigma.heap),
```

which is exactly the conclusion produced by `gen_heap_init` after reducing the `heap_package` alias. The expected third argument contains

```text
world_package
  = mkProperExist1 (wsatGS S)
      (λ W => mkProperSep (wsat W) (ownE W coPset_universe)),
```

which is exactly the conclusion of `wsat_alloc` after reducing the `world_package` alias. No mathematical coercion or missing lemma is required. These are definitional conversions between two presentations of the same types.

### Evidence that this is conversion divergence

The official `v1.12.0` checker validates `iris.program_logic.adequacy:init_from_allocations` from source in about 40 seconds and validates the later `wp_adequacy_from_init` theorem in about 21 seconds. It also validates `gen_heap_init` and `wsat_alloc` in their defining modules. However, targeted checks of the one-line concrete `iris.program_logic.adequacy:init` produced no error and no goal and were stopped after 10 and 30 silent minutes.

Earlier profiling of the same recursive-resource conversion shape found the main thread continuously `RUNNABLE`, with CPU time tracking elapsed time. Stack samples were dominated by

```text
CompareVisitor.compare
CompareVisitor.normalizedCompare
CompareVisitor.compareLists
CompareVisitor.visitDefCall
CompareVisitor.visitFunCall
```

rather than by proof elaboration or ordinary normalization. Instrumentation showed the number of distinct closed expression pairs growing from roughly 24,000 to 800,000, then 1.8 million and 2.8 million. That growth rules out a deadlock: the checker is making local steps but repeatedly generating deeper comparison obligations.

### How a tiny alias conversion reaches the recursive tower

At the `init_from_allocations` application, independently elaborated expected and actual types are structurally the same but are not necessarily the same Java object, so pointer identity is insufficient. The non-normalizing comparison descends through types such as

```text
properUPred_ent
mkProperBUpd
mkProperExist1
mkProperSep
ProperUPred (iResUR S)
```

until it reaches a leaf that needs a small delta, beta, projection, or implicit-argument reduction. Because that comparison mode intentionally refuses normalization, the cheap attempt fails. The old fallback weak-head normalizes the enclosing calls.

Eventually it encounters separately constructed applications with a common recursive head, most importantly the resource model indexed by the same signature:

```text
iResUR S  =?=  iResUR S.
```

The two arguments `S` are already equal. Nevertheless, the old fallback unfolds `iResUR` first:

```text
iResUR S
  ↦ urFunctor_apply (iResF S) (iPrePropO S)
  ↦ urFunctor_apply (iResF S) (iProp_result S).solution_car.
```

That expansion exposes `iResF`, `uPredOF`, solver projections, functor applications, and the recursive relation between propositions and resources. Comparing freshly constructed expanded records field by field eventually reaches another occurrence of the same resource-domain problem. The checker therefore explores a deeper representation even though equality of the original calls followed immediately from equality of their signature arguments.

### What PR #132 changes at this point

For the pair

```text
iResUR S  =?=  iResUR S
```

the new branch sees the same `FunctionDefinition` on both sides and calls `visitDefCall` before weak-head normalization. It compares the universe levels and then `S` with `S`. That succeeds, so congruence establishes equality of the complete calls:

```text
S ≡ S
-----------------
iResUR S ≡ iResUR S.
```

The comparison returns without exposing `urFunctor_apply`, `iResF`, or the solver carrier. The same rule also handles larger common heads around the heap and world packages whenever their arguments are definitionally equal after a small reduction. One finite local argument comparison therefore prevents entry into the recursive expansion that dominated the official-release run.

This does **not** make an ill-guarded Iris definition acceptable. `iProp_result` remains a contractive solver result, remains sealed, and its fold/unfold maps remain explicit. The patch changes how the checker proves equality of two applications of the same already-accepted definition. It does not add a recursion rule, relax termination checking, or assert that a type equals its unfolding without proof.

### Verification target

The decisive end-to-end check uses the CLI built from patched Arend master:

```bash
cd ~/Aarhus_uni/MSc/IRIS
java -Xmx16g \
  -jar ~/Projects/Arend/cli/build/libs/cli-1.12.0-full.jar \
  -L ~/.arend/libs iris.program_logic.adequacy:init --double-check
```

After that succeeds, the dependent public boundary should be checked with the same jar:

```bash
java -Xmx16g \
  -jar ~/Projects/Arend/cli/build/libs/cli-1.12.0-full.jar \
  -L ~/.arend/libs iris.program_logic.adequacy:wp_adequacy --double-check

```

The important acceptance criterion is not merely that the process returns quickly. Each target must reach its `--- Done (...) ---` marker, report no typechecking error in the target, and report no new proof goal. Since this repository deliberately retains the imported String-equality hole at `iris_heap_lang.lang:112`, the current CLI process returns status 1 even when the selected non-String target checks successfully. That known global goal must be distinguished from a diagnostic inside the selected target.

### Result with the patched v1.12 build

The jar built from local Arend commit `84c291484` has SHA-256

```text
d6f1dc095341a5ac7c0aabd7c3f8034c22b6a029ce15901cc46753aa0c176c8a
```

Both checks were run on 2026-08-11 with 41 dependency caches loaded and `--double-check` enabled:

| Target | Selected-definition time | Target result | Other diagnostics |
|---|---:|---|---|
| `iris.program_logic.adequacy:init` | 219 ms | done, no target errors/goals | known imported `iris_heap_lang.lang:112` goal |
| `iris.program_logic.adequacy:wp_adequacy` | 244 ms | done, no target errors/goals | known imported `iris_heap_lang.lang:112` goal |

The complete CLI invocations took about 17 seconds each, mostly loading and double-checking the dependency cone. The relevant comparison boundary itself is represented by the selected-definition time. Most importantly, `init` changed from no result after 30 minutes on official `v1.12.0` to a completed check in 219 ms with the PR patch.

### Full-audit caveat discovered afterwards

The targeted result above is real, but it is not sufficient to validate the current PR implementation. A later cache-disabled command

```bash
java -Xmx16g \
  -jar ~/Projects/Arend/cli/build/libs/cli-1.12.0-full.jar \
  -L ~/.arend/libs --recompile --serialize
```

recompiled the complete IRIS graph and arend-lib. It exposed many new arend-lib failures, beginning with termination and dependent-type errors in `Arith.Nat` and continuing through `Arith.Int`, array, algebra-solver, matrix, polynomial, and fan-theorem modules. This is consistent with speculative argument comparison committing unsolved metavariables before the old fallback runs.

Consequently, the earlier 21-line revision of PR #132 demonstrated the
performance fix but was not safe as the canonical checker. That revision was
superseded by the guarded implementation, which prevents inference-state
mutation and recursive re-entry and has since passed the arend-lib regression
and the full IRIS source/cache audit. The historical audit persisted 69 of 72
IRIS modules and skipped what are now
`iris.base_logic.lib.wsat_sigma`, `iris.base_logic.lib.invariants`, and the
intentionally deferred String-based `tests.fact`.

## Conclusion

Both examples have the same logical shape:

```text
small argument conversion
        ↓
same-head congruence proves the application conversion
        ↓
recursive head unfolding is unnecessary
```

In the mathematical example, the common head constructs a fixed point of a contractive functor. In Iris, it constructs the recursively defined resource model used by propositions and ghost state. In both cases the old strategy can enter an unbounded unfolding tree before using a finite congruence proof. PR #132 puts that proof first and retains the old unfolding behavior as a fallback.
