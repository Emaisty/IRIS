---
name: iris-prove
description: Prove or refactor separation-logic, ghost-state, invariant, and HeapLang weakest-precondition proofs in the Arend Iris port. Complements arend and arend-prove with Iris resource discipline, native proof-mode usage, and program-logic boundaries.
---

# Proving with Iris in Arend


## Choose the proof layer

- State reusable BI laws over `ProperUPred M`. Use `iProp S` for propositions
  depending on a ghost signature and `H : irisGS cnt S` for HeapLang clients.
  The canonical program goal is `wp H E e Phi`; `H.iris_wsat`,
  `H.iris_gen_heap`, and `H.iris_proph_map` supply its resources.
- Use `iris.program_logic.*` and `iris.base_logic.lib.gen_heap` for new
  clients. The fixed-heap logic in `tests.fact.program_logic` belongs to the
  factorial example; extend it only when working on that example.
- At the assertion/client layer, use public ownership, invariant, and WP
  lemmas with native proof mode. Descend to `upred_holds`, step indices, or
  CMRA carriers when proving a semantic/library rule that needs them. Merely
  rearranging resources should not unfold the recursive `iProp` model.

Before a substantial proof, identify the spatial resources consumed and
returned, persistent facts available to each continuation, the current
mask, and any ghost-state transition. For a program step, identify the
redex and the resources its postcondition must retain. This makes the Iris
part of the inherited proof plan concrete.

## Work with the native proof mode

Import `iris.base_logic.notation` for logical notation and the virtual
`iris.proofmode.Meta` for tactics. The detailed syntax is in
`docs/proofmode.md`; `src/tests/proofmode.ard` provides small usage examples.
For this project, follow `arend.yaml`, the root README, and
`scripts/build-proofmode-extension.sh` for the compatible checker/extension;
generic Arend skill examples may name an older CLI jar. Do not create a
`Meta.ard` file to repair an unresolved virtual-module import.

- `ipm` starts an entailment with an initial hypothesis named `""`.
  Introduce meaningful names with `iIntros`; decompose only the resources the
  next step needs. Quoted proof-mode labels are distinct from HeapLang's
  numeric `Name` binders.
- Use `iFrame`, `iSplitL`/`iSplitR`, and `iAssert` for resource arrangement
  before writing manual associativity/commutativity chains. Splitting shares
  the persistent context, not the spatial resources. Promote a hypothesis
  with `#` only when persistence is available or explicitly proved.
- Destruct pure facts into ordinary Arend arguments and solve the resulting
  arithmetic/equality goal with the ordinary Arend tools. Existential
  witnesses likewise enter a continuation as Arend arguments. Reassemble
  the logical assertion at the boundary instead of mixing semantic resources
  into a pure calculation.
- For wrapped assertions, supply the relevant `PM*` evidence or an explicit
  predicate family. `PMFromSep` is a naming trap: its field is
  `P ⊢ (Q ∗ R)`, so it supports destruction and corresponds to Rocq `IntoSep`.
  `PMFrame M R P Q` means `(R ∗ Q) ⊢ P`. Inspect the field direction instead
  of inferring it from the class name.
- `iPoseProof` is an alias of `iAssert`; `iEval` is an alias of `wp_apply`.
  Their names do not promise the full Rocq tactic interfaces.
- If automation obscures a goal, use `iStopProof` to expose the entailment
  over `of_envs`, then apply a focused public lemma. For reusable wrapped
  propositions, follow `src/tests/proofmode_custom_instances.ard` and provide
  evidence rather than teaching Java metas about a particular client.

Keep logical rules in Arend. A new Java meta should elaborate applications
of proved rules; it must not become the justification for a resource
permutation, duplication, or mask transition.

## Sequence HeapLang proofs

Use `wp_pures` for supported pure evaluation; use `wp_lam`, `wp_let`, or
`wp_rec` when stopping at a particular beta step matters. Expose a contextual
redex with `wp_bind`, or use `wp_smart_apply` and the let/context bridges in
`iris.proofmode.heap_lang`. Name the intermediate postcondition when
inference cannot recover the continuation family.

The primitive-named metas (`wp_load`, `wp_store`, `wp_allocN`, `wp_faa`,
`wp_fork`, `wp_new_proph`, `wp_resolve`, etc.) are aliases of
`wp_smart_apply`: provide the actual specification and its postcondition
continuation. They do not infer a primitive rule solely from the tactic
name. See `src/tests/proofmode_wp_primitives.ard`, especially
`proofmode_wp_load_nested_let`. Selectively import or qualify a colliding
term-level rule, such as `iris.program_logic.lifting.wp_load`.

Fractional load preserves its points-to resource; store and FAA rules need
the appropriate full ownership. For arrays, focus/reinsert a cell with
`pointsto_array_extract`/`pointsto_array_insert`; use
`pointsto_block_replicate` after uniform allocation. For map-indexed
assertions, use `big_sepM_delete`. Keep the untouched array/map part framed
through the step and restore the changed cell before closing the invariant.

Use structural induction for pure list/natural-number facts. For a recursive
HeapLang computation, follow the guarded WP/Löb structure (`iLob`) and make
the program step that justifies later reasoning explicit.

## Updates and invariant opening

Basic updates (`|==>`) and fancy updates (`mkProperFUpd W E1 E2`) have
different obligations. Track both masks before `iMod`; use `wp_bupd`,
`fupd_wp`, or the applicable bridge for moving an update into WP.

For `iInv`, the current implementation requires a **spatial** invariant
hypothesis, a WP goal, `coPSubset (nclose N) E`, and `StronglyAtomic e`.
Focus the atomic redex first. If the invariant is only in the persistent
context, derive an appropriate spatial copy using its persistence rather
than assuming `iInv` can select that context directly.

With `D = coPset_difference E (nclose N)`, ordinary opening provides:

- the delayed invariant body `|> P`;
- a closing resource `(|> P) -∗ mkProperFUpd W D E mkProperEmp`;
- a WP under `D` whose postcondition must restore mask `E`.

Plan the reconstruction and closing update together with the atomic step.
The `">HP Hclose"` form needs `PMTimeless` evidence for the exact body; it
provides `P` and a corresponding closing resource. Timelessness does not
license dropping later arbitrarily. `own_timeless`, `pointsto_timeless`, and
the connective closure lemmas are useful evidence sources.

For an accessor other than an invariant, use `PMIntoAccessor` with
`pm_wp_accessor`. For a non-atomic expression, use the actual term-level
accessor/WP rule and its side conditions rather than asserting atomicity.
Inspect `pm_wp_inv`/`pm_wp_inv_timeless` in
`src/iris/proofmode/heap_lang.ard` when the closing obligation is unclear.

## Ghost protocols and equality

Choose an existing resource by the protocol fact it supports:

| Need | Existing construction and boundary |
| --- | --- |
| Mutable finite ghost map | `ghost_map`; public elements are full ownership and authority uses `Qp`, with the name bundled in `ghost_mapGS`. |
| Monotone snapshots | `mono_nat`; owned fractional authority and persistent lower-bound fragments. |
| Fractional agreement on a model | `frac_auth`, often over `agree`; its public authority is exclusive and fragments use owned fractions. |
| A stored logical continuation | `saved_pred`; discarded ownership is persistent and agreement is delayed internal equality. |

Prove the algebraic update/validity fact at its CMRA, then lift it with
`own_update`, `own_updateP`, `own_op_valid`, or the existing library wrapper.
When adding a resource to a closed client, package its functor and propagate
the `subG`/`inG` witnesses through the signature; keep allocation and use on
the same selected ghost name.

Distinguish Arend paths, OFE distance/equivalence, and internal logical
equality. For example, `saved_pred_agree` yields later internal equality,
not an Arend path available to an ordinary `rewrite`. Apply internal-equality
elimination at the logical layer and respect the later modality.

## Forks, prophecies, and closing a client

For spawn/join/par, start from `src/iris_heap_lang/lib/spawn_proof.ard`.
Preserve the child WP, join token, result resources, and required
`fork_post_inhabited` witness. A proof of the parent's return alone does not
establish safety of the spawned pool.

For prophecy steps, track the predicted resolution list and the exact
observation consumed. Select the real lifting rule (`wp_new_proph`,
`wp_resolve_store`, or `wp_resolve_skip`); `wp_resolve` is only the meta
wrapper. The counter's pending/done read protocol in
`src/examples/parallel_counter_proof.ard` is the substantial example.

To obtain a closed operational result, assemble the concrete ghost
signature and initial state, prove the closed WP, and apply `wp_adequacy`
or `wp_adequacy_with_fork`. Follow `msc_closed_client_wp` and
`msc_closed_client_adequate` in `src/examples/parallel_counter_client.ard`.
`Adequate` establishes return-value correctness and safety of every reachable
thread pool; it does not assert termination or fairness.

When changing a shared proof-mode rule or evidence interface, check its
closest existing `tests.proofmode*` consumers, including applicable `fails`
cases for invalid evidence/resource use. Rebuild the extension after Java
changes. Inspect actual goal/error diagnostics: `scripts/typecheck-all.sh`
reports holes separately, and its successful exit alone is not a proof
completion criterion.
