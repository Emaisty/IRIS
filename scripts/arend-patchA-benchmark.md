# Arend typechecker patch A — benchmark comparison (RESULT: A ineffective)

Patch A: CompareVisitor.nonNormalizingCompare now sees through \let-clause
references (EvaluatingBinding) so the congruence fast-path can match
structurally-equal transparent \func applications (mkProperExist, own, ...).

Both jars built from the same base commit (HEAD May 29); differ only by patch A.
Baseline jar 9288221 B, patched jar 9288290 B (CompareVisitor recompiled).
Times: `time -p`, java -Xmx16g --no-daemon <module>, per-file (deps mostly cached).

| Module                         | Baseline (real) | Patched A (real) | Effect        |
|--------------------------------|-----------------|------------------|---------------|
| iris.base_logic.lib.own                            | 5m25s (333.1s)  | 5m22s (329.8s)   | none (noise)  |
| bench_repro (bupd_mono∘own)    | diverges >15m   | diverges (killed 21m) | none     |
| tests.fact                   | 27m16s (1644s)  | not run*         | —             |

*fact.ard not re-run: A showed zero effect on the guaranteed-pattern reproducer
 and on own, so the 27-min run was very unlikely to differ.

## Conclusion
Patch A is correct and safe (no correctness change) but does NOT help this
workload. The bottleneck is NORMALIZATION during elaboration, not the congruence
comparison A optimizes: elaborating types such as `properUPred_ent A_I A_I`
repeatedly unfolds `A_I -> mkProperExist -> own -> iRes_singleton` into the
`iResUR` structure with no memoization. The compare-side change can't touch that.

## Real fixes (next)
- Approach B: normalization memoization — cache WHNF on inference-free
  Expressions (NormalizeVisitor currently has zero result caching; confirmed).
  Directly attacks the redundant re-normalization. Bigger change; needs an
  inference-freeness guard for soundness.
- User-side: \sfunc-seal iRes_singleton / own so normalization stops unfolding
  into the recursive domain (stops the cost at the source, no Arend change).
