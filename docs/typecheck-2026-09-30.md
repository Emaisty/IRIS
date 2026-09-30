# Official and patched Arend typecheck — 2026-09-30

The patched checker completed the full source check: **80 of 82 modules passed,
two failed, and no unfilled goals were reported**. Both failures are in the
legacy factorial tests. The current Iris core, native proof mode, HeapLang
libraries, and parallel counter client passed. The official whole-project
check exceeded a 900-second process deadline while processing
`iris.base_logic.lib.saved_pred`. A subsequent source-only sweep attempted
every module individually: **63 passed and 19 exceeded a 120-second deadline**.
The official checker did not establish a whole-project pass.

This audit checks the unchanged Arend and Java extension sources at IRIS merge
`e00f2867886b928e6cd420959cf39e0d3975cb8e`. The two checkers used independent
project copies, standard-library extensions, and binary caches. The
[source manifest](typecheck-evidence/source-manifest.json) records every input.

## Toolchains

| Component | Revision |
| --- | --- |
| Official Arend | `c51e285e063dff8d7bdb8c2a82bf454059b2537b` |
| Patched Arend | `7734ae6eeb5d2c0fade4991601332d2199700e36` |
| Standard library | The `arend-lib` directory bundled with each checker revision |
| Java | Temurin `25.0.4.1+1`, macOS aarch64 |
| Gradle | The upstream wrapper, `9.6.1` |
| IRIS process limits | `-Xmx12g -Xss16m` |

GitHub's official `master` was queried afresh and still pointed to `c51e285e0`.
The patched build uses that same base with the current feature changes from
[PR #131, Implement String](https://github.com/arend-lang/Arend/pull/131), and
[PR #132, Compare function arguments before unfolding calls](https://github.com/arend-lang/Arend/pull/132).
At the audit, #131 was open; #132 was closed without merging.

The local rebase consists of `84c291484`, `59e60bdf3`, `b1a256cb6`, and
`7734ae6ee`. Its string patch matches PR #131's current feature commit
`062a2ac54`; its guarded conversion patch matches PR #132's `b67bd9594` and
`82a633b56`, with API adaptations for master. It does not import the PR
branches' unrelated staging changes. The conversion optimization compares
arguments before unfolding function calls; it does not disable termination
checking. The guarded version includes checks for inference variables and
recursive re-entry.

The [combined patch](typecheck-evidence/arend-1.12-iris.patch) applies to the
official revision. [Toolchain metadata](typecheck-evidence/toolchains.json)
includes complete revisions, standard-library tree IDs, jar hashes, and
regression-test counts. Both jars and both standard-library Java extensions
were rebuilt, as was IRIS's extension against each corresponding jar.

Java 27 could not build the upstream Gradle Groovy task: it reported
`Unsupported class file major version 71`. Java 25 built both variants
successfully. This was a build-tool compatibility issue, before Arend checked
any proofs.

## Results and failures

| Check | Result |
| --- | --- |
| Official, full source run | Timed out; no errors or goals before the deadline; last progress marker was module 10/82, `saved_pred` |
| Official, all 82 targets checked individually from source | 63 passed, 19 timed out at 120 seconds each; no errors or goals reported before the deadlines |
| Patched, full source run | 80 passed, 2 failed; 164 errors, 0 goals; process exit 1 |
| Patched, fresh-process cache run | Loaded 80/80 available IRIS caches; reproduced the same 164 errors in the two uncached factorial modules |
| Patched, counter client cache run | Passed; 63 modules loaded, 0 errors, 0 goals, process exit 0 |
| Targeted `saved_pred` source check, 120-second deadline | Patched passed; official timed out |
| Patched checker regression suites | 51 passed, 0 failed, 0 skipped |

The [per-module comparison](typecheck-evidence/modules.csv) lists all 82
targets. [Official process records](typecheck-evidence/official-source-modules.json)
and [complete per-module logs](typecheck-evidence/official-source-module-logs.zip)
retain the source-only commands and outcomes. These checks used `-r`, with
no cache reads or writes, and a separate process for each target. Parallel
workers shared only immutable source/extension inputs and completed-result
checkpoints. The [summary](typecheck-evidence/summary.json) records the totals.

Official timeouts include the counter proof/client, several ghost-state and
program-logic modules, spawn proofs, and associated tests. Both factorial
targets also timed out before producing error diagnostics, so the official
run did not independently reach the patched run's factorial failures.
The official `saved_pred` deadline dump shows its main thread working in
normalization and substitution. The [patched targeted run](typecheck-evidence/patched-conversion-control.log)
completed the same module from source within the 120-second budget.

An initial incremental official sweep encountered binary-deserialization
warnings and nonzero process exits, for example in the
[`dfrac` reload](typecheck-evidence/official-cache-dfrac.log). Its results are
excluded from the source totals above; every target was subsequently checked
with caches disabled.

The regression suites were `StringLibraryTest` (17), `ComparisonTest` (26),
and `LibraryLoadOrderTest` (8), invoked through the root `:test` task. The
String tests exercise literal elaboration, record relevance, equality,
Unicode, and rejected invalid uses. The conversion tests include the
same-function optimization and its inference-state guards.

HeapLang binders and proof-mode context names use numeric representations in
this IRIS snapshot. Passing its modules alone would not exercise the new
semantic `String` type; that feature is covered by the dedicated String
regression suite. The [build and regression logs](typecheck-evidence/build-and-regression-logs.zip)
include the test reports.

The failing IRIS modules are:

- `tests.fact.program_logic`: 135 diagnostics. The first failures are at
  lines 137, 141, 187, and 194: `State` records implement `heap` but omit
  the newer `usedProph` field. Later failures include outdated primitive-step
  arguments and cascading type/coverage errors.
- `tests.fact`: 29 diagnostics. The first is a failed definitional equality
  in the factorial normalization proof at line 240. Further failures include
  outdated primitive-step applications and dependencies on the failing
  factorial program-logic module.

These failures remain in the source tree. This audit does not claim that
adding `usedProph` alone would repair all 164 diagnostics. In particular,
the patched toolchain is compatible with the current core/client, but a
claim that the entire repository typechecks is false until these tests are
updated and rechecked.

Complete outputs and process metadata are available for the
[official source run](typecheck-evidence/official-full-clean.log),
[patched source run](typecheck-evidence/patched-full-clean.log),
[patched cache run](typecheck-evidence/patched-full-cache.log), and
[counter reload](typecheck-evidence/patched-counter-cache.log).
Timing output is diagnostic, not a controlled performance comparison;
processes overlapped and JVM wall-clock timings differed from the runner's
monotonic elapsed measurements. Timeouts are incomplete checks, not proof
rejections.

## Reproduce

Use two clean Arend checkouts at the official commit above. Apply the saved
patch to one checkout. Keep their bundled `arend-lib` directories and all
IRIS `bin/` and `ext/` outputs separate; the String patch changes the binary
serialization version. Set `JAVA_HOME` to a compatible JDK and prepend its
`bin` directory to `PATH`.

From each checker checkout, build:

```sh
./gradlew --no-daemon :cli:jarDep :arend-lib:meta:classes
```

From a separate, initially cache-free copy of IRIS for each checker, run:

```sh
export AREND_JAR=/absolute/path/to/checker/cli/build/libs/cli-1.12.0-full.jar
export AREND_LIBDIR=/absolute/path/to/checker
./scripts/build-proofmode-extension.sh
java -Xmx12g -Xss16m -jar "$AREND_JAR" -L "$AREND_LIBDIR" -r --serialize
java -Xmx12g -Xss16m -jar "$AREND_JAR" -L "$AREND_LIBDIR" --serialize
```

The JSON evidence files record commands, exit codes, diagnostics, completion
markers, and deadlines. The original audit workspace is
`/private/tmp/iris-arend-20260930`, including the JDK, both built checkers,
isolated IRIS copies, process runners, and full logs. The runners' module
checkpoints are specific to these immutable input copies; use fresh copies
and result directories when checking changed sources.

The repository's `scripts/typecheck-all.sh` was also corrected: a nonzero
Java exit, a missing completion marker, or an unfilled goal now fails the
check. It handles empty flag arrays on macOS Bash 3.2 and reports the actual
number of attempted modules after an early stop or resume. Temporary stub
checks verified success, errors, goals, crashes, incomplete execution,
early-stop counts, and forwarding of recompilation/serialization flags.
