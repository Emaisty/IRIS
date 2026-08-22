---
name: arend
description: Use whenever working with Arend code — proving, formalizing, refactoring, debugging, exploring arend-lib, or answering questions about Arend definitions. Provides CLI conventions (the `arend` console app), search workflow, and error-handling priorities. The proving-specific arend-prove and the local-error catalog arend-debug build on this base.
---

# Arend Workflow Basics

These rules apply to **any** Arend work — proving, refactoring, exploration, debugging, lookups.

## Library access goes through the Arend CLI

**Never search arend-lib with `find` or `grep`.** All access to library code goes through the Arend console CLI (`ConsoleMain`). The arend-lib source tree is large and ranking on the filesystem is poor; the CLI maintains an on-disk symbol index and pretty-prints definitions in their resolved form.

### Invocation template

The project ships the CLI as `cli-1.11.0-full.jar` at the project root. Use `~/.arend/libs` as the libdir — that's where library zips (e.g. `arend-lib.zip`) are installed:

```sh
java -jar cli-1.11.0-full.jar -L ~/.arend/libs <FLAGS...>
```

- `-L <dir>` points at a directory **containing** libraries — each library is either a directory (`<libdir>/<name>/arend.yaml`) or a zip (`<libdir>/<name>.zip`). Zip-form and directory-form libraries are interchangeable.
- With no positional args and an `arend.yaml` in the working directory, the current project is loaded automatically along with its declared dependencies (transitively — no need to also pass dep names).
- Append a positional library name (e.g. `arend-lib`) or module path (e.g. `Algebra.Monoid`) to scope a command to just that library/module.
- If you edit a dependency library's sources directly (rather than via its zip), rebuild its zip so the CLI (and IntelliJ) pick up the changes: `(cd <lib-source-dir> && zip -qr ~/.arend/libs/<lib-name>.zip arend.yaml src)`.

### CLI commands (replace the old MCP tools)

| Purpose                            | Old MCP tool                    | CLI flag                              |
|------------------------------------|---------------------------------|---------------------------------------|
| Typecheck modules                  | `Typecheck_module`              | positional `MODULE` args (no flag); plain `arend` rebuilds everything |
| Find by signature shape            | `Proof_search`                  | `-ps <pattern>`                       |
| Find by short name                 | `SearchSymbols`                 | `-ss <pattern>`                       |
| Pretty-print a definition          | `ShowDefinition`                | `-p Module.Path:DefinitionName`       |
| Show AI guide markdown             | `ShowAiGuide`                   | `-ag [Module.Path]`                   |
| Resolve unresolved refs / imports  | `FixImports`                    | `-ai` (suggest-only — see notes)      |
| List modules                       | `List_modules`                  | positional library name + `--show-modules` / browse `.aiGuide/` via `-ag` |
| Find every usage of a definition   | *(none — new)*                  | `-fu Module.Path:DefName`             |
| Class hierarchy + instances        | *(none — new)*                  | `-ch ClassName` or `-ch M.P:Class`    |
| Dump ambient scope at a referable  | *(none — new)*                  | `-sc M.P:Name [pattern]`              |
| Rebuild the symbol index           | *(none — new)*                  | `-rx`                                 |

Each flag accepts `help` as its value to print the full grammar — e.g. `-ss help`, `-ps help`, `-ai help`, `-fu help`, `-ch help`, `-sc help`, `-ag help`, `-rx help`. **Reach for that first** when you forget the syntax; the help text is the authoritative reference.

### CLI gotchas

- **Run from the project root.** `arend.yaml` is picked up from the current working directory, so the simplest invocations assume you're at the project root.
- **`-L` points at a *directory containing* libraries, not at a library itself.** `-L ~/.arend/libs` works when e.g. `~/.arend/libs/arend-lib.zip` exists; pointing `-L` at the zip itself does not.
- **`-ss` / `-ps` / `-fu` / `-ch` / `-sc` / `-rx` accept multiple sub-tokens, each as a separate flag occurrence.** Example: `-ss Monoid -ss limit=20 -ss kind=lemma,func -ss only=arend-lib`. Don't try to pack them into one quoted string.
- **Positional args vs. option values.** Options with multi-value flags (`-ss`, `-ps`, `-fu`, `-ch`, `-sc`) can swallow following tokens. Put options **before** positional library/module names, or use `--` to mark the end of options: `arend ... -ss Monoid -- arend-lib`.
- **Dots in fully-qualified names.** `-p`, `-fu`, `-ch`, `-sc` all use `Module.Path:DefinitionName` (dot between module segments, colon before the in-module name). The symbol search output (`-ss`) prints names as `library::module.path:name`; convert `library::M.P:N` to `M.P:N` for `-p` / `-fu` / `-ch`.
- **Daemon routing is keyed to a single library.** `DaemonRpc.tryRouteCli` looks for the **first positional that resolves to a library**; failing that, it uses cwd's `arend.yaml`. The daemon you start is keyed to the current project, so passing `arend-lib` (or any other lib) as a positional **silently bypasses your daemon** and forces in-process reload. To stay on the warm context, run from the project root and omit foreign library positionals. To restrict the *scope* of a search to a single library, use the `only=<libname>` token instead, e.g. `-ss only=arend-lib`. `-ss` / `-ps` / `-fu` / `-ch` / `-sc` all search every loaded library (including transitive deps + prelude) by default, so the project daemon already covers dep lookups.
- **Daemon mode for speed.** Reloading the library on every invocation is slow. For a session involving many CLI calls, start a daemon once from the project root: `java -jar cli-1.11.0-full.jar -L ~/.arend/libs -d <project-name>`. Subsequent commands route through the daemon automatically **as long as no other library is given as a positional** (see previous bullet). Stop it with `--daemon-stop <project-name>`. Force in-process with `--no-daemon` if needed. Use `--daemon-refresh <project-name>` after editing source so the warm context picks up changes.
- **Index staleness after edits.** `-ss` / `-fu` / `-ch` / `-sc` read an on-disk index. After significant edits or renames, refresh it: `-rx` (rebuild for all loaded libraries) or `-rx only=<project-name>` (just the project). The `-ai` pipeline also refreshes the index as its last step.
- **No automatic import insertion.** The old `FixImports` MCP tool rewrote sources; the CLI's `-ai` mode is suggest-only — it prints "Candidates for 'X' at ..." blocks listing the qualified name and required imports. You paste the right one yourself. This is a feature, not a bug: it avoids the position-mistake mangling that retired the auto-rewriter.

### Daemon-aware workflow (recommended for sessions)

```sh
# Once per session — run from the project root
java -jar cli-1.11.0-full.jar -L ~/.arend/libs -d <project-name>

# Each lookup / typecheck is then near-instant. NO positional library name —
# cwd's arend.yaml resolves to the project, which routes to the daemon.
# The daemon already has deps loaded, so these search them too:
java -jar cli-1.11.0-full.jar -L ~/.arend/libs -ss '*-comm'
java -jar cli-1.11.0-full.jar -L ~/.arend/libs -p Algebra.Monoid:Monoid

# To scope a search to a single library, use only=<lib> (still routes via daemon):
java -jar cli-1.11.0-full.jar -L ~/.arend/libs -ss Monoid -ss only=arend-lib

# After editing source, push the changes to the daemon's warm context
java -jar cli-1.11.0-full.jar -L ~/.arend/libs --daemon-refresh <project-name>

# Clean up at end of session (optional — the daemon idles cheaply)
java -jar cli-1.11.0-full.jar -L ~/.arend/libs --daemon-stop <project-name>
```

## Search before writing

Before writing a non-trivial term, lemma, or proof step:

1. `-ps '<goal-type-pattern>'` — surfaces existing lemmas of that signature shape. Examples: `-ps 'Fin -> Nat'`, `-ps '_ <= _ -> _ <= _'`, `-ps 'Monoid -> _ = _'`.
2. `-ss <keyword>` — finds definitions by name pattern. Examples: `-ss mod`, `-ss negative`, `-ss disjoint`. Use prefixed forms (`eq:`, `glob:`, `re:`, `hb:`) for stricter matches; see `-ss help`.
3. `-ag <Module.Path>` for the module that "ought to" contain the fact — see what's already there. `-ag` with no arg prints the library's `.aiGuide/README.md`.

A lot of arend-lib already exists. Reinventing wastes time and produces less reusable code.

## Error priority

When the typechecker complains, fix in this order — higher-priority errors make lower-priority ones unreliable:

1. **Syntax errors**
2. **Unresolved references** — run `-ai` for the affected module to get candidate suggestions.
3. **Type errors**
4. **Termination errors**
5. **Universe-level errors**

Stop addressing lower-priority items while higher ones remain.

## Naming: prefer `\open` over qualified names

When you write or edit Arend code, **prefer bare names over fully-qualified ones** like `NatSemiring.<=`, `Monoid.BigProd`, `AddMonoid.BigSum`, `Nat.+`. Add a selective `\open` at the top of the file instead:

```arend
\open Monoid (pow, BigProd)
\open AbMonoid (FinSum)
\open CMonoid (FinProd)
\open NatSemiring (<=-refl, <=-transitive, <=-less, decideEq, trichotomy, *-comm)
\open Nat              -- brings div, mod, + (when no conflict)
\open LinearOrder      -- brings bare <=, <
```

Then use `<=`, `<`, `BigSum`, `FinProd`, `decideEq`, etc. everywhere. The result is dramatically more readable, and most "qualified" forms like `NatSemiring.<=` and `LinearOrder.<=` refer to the same operator anyway — the prefix is just noise.

When NOT to drop the prefix:
- **Genuine ambiguity** at a use site (rare). If `+` could mean two different operators in scope and inference can't pick, qualify the relevant one (e.g. `Nat.+` to force the natural-number version). Confirm by re-typechecking rather than guessing.
- **Constructors of nested data types** (e.g. `Tri.less`, `Or.inl`) — these are usually best left qualified for readability.

The default rule: write bare names; qualify only when the typechecker actually complains.

## Subskills

When the task narrows, escalate to the appropriate subskill — they assume the conventions on this page:

- **`arend-prove`** — interactive proof writing: one-hole-at-a-time discipline, checkpoints with the user, hardest-case-first ordering, common proof patterns. Invoke when asked to prove a specific lemma or fill in `{?}` holes.
- **`arend-debug`** — catalog of recurring local-error patterns (mcases shape mismatches, `\cowith`-vs-`unfold`, Fin↔Nat coercion, dependent Σ-paths, `Dec.rec` vs `\case`). Invoke when a single hole has been fought for more than 1–2 attempts and the error matches one of the catalog entries.
