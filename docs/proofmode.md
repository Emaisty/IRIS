# Arend-native proof mode

Implemented at the 2026-09-30 merge. This is an Arend extension with Iris-style
operations and explicit proof evidence; it does not interpret Rocq Ltac.

## Architecture and imports

[`iris.proofmode.core`](../src/iris/proofmode/core.ard) defines `PMEnv`,
`PMEnvs`, `of_envs`, and `envs_entails`. Spatial hypotheses combine with `∗`;
the intuitionistic environment wraps each hypothesis in persistence.
`PMSelection`, `PMPersistentSelection`, and `PMSplit` include proofs of the
resource permutations they perform.

Java metas select hypotheses and build applications of the Arend `pm_*`
lemmas. Those applications are typechecked against the goal. The logical
rules live in Arend, including persistent duplication, framing, and mask
transitions. The [registration file](../proofmode-extension/src/main/java/org/arend/iris/proofmode/ProofModeExtension.java)
lists the public operations in the virtual module `iris.proofmode.Meta`.
Build the extension first as described in the [root README](../README.md#build).

A small example using the same syntax as `tests.proofmode`:

```arend
\import Function.Meta
\import iris.algebra.cmra
\import iris.base_logic.upred
\import iris.base_logic.notation
\import iris.proofmode.Meta

\lemma keep_right {M : UCMRA} (P Q : ProperUPred M)
  : (P ∗ Q) ⊢ Q =>
  ipm $ iIntros "HP HQ" $ iExact "HQ"
```

`ipm` starts from an entailment and creates the initial spatial hypothesis
named `""`. `iIntros` names/decomposes it. `$` composes a tactic with its
continuation; operations with multiple branches take separate proof terms.
`iStopProof` returns to an ordinary entailment over `of_envs`.

Quoted labels are converted to UTF-16 code-unit lists (`PMName = List Nat`)
before elaboration. They do not require semantic Arend `String` support and
are distinct from HeapLang's numeric variable names.

## Logical operations

| Operations | Implemented behavior |
| --- | --- |
| `ipm`, `iStopProof` | Enter/leave the environment representation. |
| `iIntros`, `iDestruct` | Introduce or decompose supported connectives, including separation, pure facts, existentials, disjunction, and persistence. |
| `iExact`, `iAssumption`, `iEmpIntro`, `iPureIntro` | Finish from a named hypothesis, search the environment, or prove emp/pure goals. |
| `iClear`, `iRename` | Remove/rename spatial or persistent hypotheses. |
| `iFrame` | Frame named resources or search automatically, including nested separating conjunctions and persistent resources. |
| `iSplitL`, `iSplitR` | Split a separating goal with explicit spatial selection; persistent resources remain reusable. Supported conjunction goals use conjunction introduction. |
| `iLeft`, `iRight`, `iExists` | Select a disjunct or supply an existential witness. |
| `iApply`, `iSpecialize` | Apply entailments/wands and specialize wands or universal hypotheses, including persistent wands. |
| `iAssert`, `iPoseProof` | Prove an intermediate proposition using selected resources; `iPoseProof` is registered as an alias of `iAssert`. |
| `iNext`, `iModIntro`, `iMod` | Later reasoning and supported basic/fancy-update introduction or elimination. |
| `iRewrite`, `iLob` | Rewrite with equality evidence and use Löb induction. |
| `iInv` | Open a selected spatial invariant/accessor around a strongly atomic WP goal. |

Examples of supported patterns from the test suite:

```arend
-- Split a hypothesis into two spatial resources.
iDestruct "Hpair" "HP HQ" $ ...
-- Expose a pure fact as an Arend argument.
iDestruct "Hphi" "%" $ \lam h => ...
-- Move a persistent proposition into the intuitionistic context.
iDestruct "HU" "#HP" $ ...
-- Existential witness becomes an Arend argument.
iDestruct "Hex" "HPhi" $ \lam x => ...
-- Disjunction has two proof continuations.
iDestruct "Hcase" "HP | HQ" leftProof rightProof
-- Select the spatial resources for an intermediate assertion.
iAssert "HR" "HP" P proofOfP continuation
```

These fragments illustrate argument order; `...` denotes the remaining proof.
They are not the full Rocq introduction/selection-pattern language.

## Evidence classes

The core exposes `PMFromAssumption`, `PMIntoPure`, `PMFromPure`,
`PMIntoPersistent`, `PMFromSep`, `PMIntoAnd`, `PMIntoOr`, `PMIntoWand`,
`PMIntoLater`, `PMFromLater`, `PMTimeless`, `PMFromExist`/`PMIntoExist`, their
`Set1` variants, `PMIntoForall`/`PMFromForall`, `PMFrame`, `PMIntoUpdate`,
`PMIntoInvariant`, and `PMIntoAccessor`.

Each packages an entailment or logical rule. Tactics recognize direct
connectives and accept explicit evidence for wrapped propositions. For
example, `PMIntoWand M R P Q` contains `R ⊢ (P -∗ Q)`; `PMFrame M R P Q`
contains `(R ∗ Q) ⊢ P`. Despite its name, this implementation's `PMFromSep`
contains `P ⊢ (Q ∗ R)` and is used for destructing a hypothesis. Its direction
corresponds to Rocq `IntoSep`.

[`tests.proofmode_custom_instances`](../src/tests/proofmode_custom_instances.ard)
shows how a client supplies these records without changing the Java metas.
[`tests.proofmode`](../src/tests/proofmode.ard) exercises their dispatch,
aliases, persistent operations, and rejection cases. These classes cover
the native implementation's supported operations; they are not a complete
copy of Rocq's proof-mode instance system.

## HeapLang automation

Term-level rules and metas share names such as `wp_value`, `wp_bind`, and
`wp_fork`. Use selective imports or qualify a colliding name, as in
[`tests.proofmode_wp_primitives`](../src/tests/proofmode_wp_primitives.ard).

| Operations | Behavior |
| --- | --- |
| `wp_pures`, `wp_pure` | Evaluate supported pure redexes, repeatedly or for one step. |
| `wp_lam`, `wp_let`, `wp_rec` | Pure evaluation through the requested lambda/let or recursive beta step. |
| `wp_bind`, `wp_value`, `wp_if` | Focus a context, discharge a value WP, or select a Boolean branch. |
| `wp_apply`, `iEval` | Apply a supplied WP/entailment rule; `iEval` is an alias of `wp_apply`, not Rocq's general reduction-expression language. |
| `wp_smart_apply` | Apply a supplied specification under supported evaluation contexts and let sequencing. |
| `wp_alloc`, `wp_allocN`, `wp_load`, `wp_store`, `wp_faa`, `wp_fork`, `wp_new_proph`, `wp_resolve` | Primitive-named aliases of `wp_smart_apply`; callers provide the rule and postcondition continuation. |

The primitive aliases do not synthesize a specification just from their
name. For concrete calls, see `proofmode_wp_load_rule` and
`proofmode_wp_load_nested_let` in the primitive suite.
[`iris.proofmode.heap_lang`](../src/iris/proofmode/heap_lang.ard) proves the
bridges `pm_wp_smart_apply`, `pm_wp_let`, `pm_wp_smart_let`,
`pm_wp_smart_bind_item`, `pm_wp_inv`, `pm_wp_accessor`, and
`pm_wp_inv_timeless` used by the metas.

For invariant opening, the usual form is
`iInv "Hinv" "HP Hclose" maskProof atomicityProof continuation`.
Wrapped invariants may supply `PMIntoInvariant` evidence. A `">HP Hclose"`
pattern additionally requires `PMTimeless` evidence. A `PMIntoAccessor`
record supports other mask-changing accessors. `iInv` currently requires a
spatial hypothesis and a WP goal; it does not open a persistent-context
hypothesis directly. The continuation must meet the closing and mask
obligations checked by the bridge theorem.
