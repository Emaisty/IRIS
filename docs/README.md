# Documentation and porting status

The [implementation audit](implementation.md) describes the merged source
and its public APIs. The [proof-mode guide](proofmode.md) documents the native
extension. The dashboard in `index.html` compares individual declarations
with the pinned Rocq Iris snapshot `b9b6cf04478a3088aef800497cdd275d2bce0967`.
It is an API coverage inventory, not a measure of theorem correctness or
completion of the counter client.

The [toolchain audit](typecheck-2026-09-30.md) records fresh official and
patched checker results, including the two failing legacy factorial modules.
Its evidence files preserve revisions, process outcomes, logs, and the
combined checker patch.

## View the dashboard

From the repository root:

```sh
python3 -m http.server 8000 --directory docs
```

Open `http://localhost:8000/`. HTTP is required because `app.js` fetches the
tab-separated data files. Search matches Rocq names, Arend mappings, and
comments; status and role filters can be combined.

The guides have committed HTML versions for the static website. Edit the
Markdown sources (including the root README), then regenerate them with:

```sh
python3 scripts/build-docs.py
```

The dependency-free renderer supports the headings, paragraphs, flat lists,
tables, links, inline formatting, and fenced code used here. It rewrites
guide links to HTML and source-code links to the audited Git revision.

## Maintain the data

Each nonempty row in `rocq-data/**/*.v.txt` has four or five tab-separated
fields: Rocq name, Arend mapping, relationship, role, and optional comment.
Mappings use `module.path:definition`; multiple supporting definitions may
be separated with `; `. A definition in the virtual `iris.proofmode.Meta`
module must be registered in `ProofModeExtension.java`.

| Relationship | Meaning |
| --- | --- |
| `direct` | Corresponding public definition/theorem is present with the relevant semantics. |
| `analogue` | Arend provides related functionality with a different representation, interface, or narrower scope; the comment states the difference. |
| `not-needed` | Rocq-specific scaffolding, such as a sealing wrapper, is unnecessary in this implementation. |
| `missing` | No mapped implementation has been established. The role is `foundational` or `qol`. |
| `ignored` | Explicitly outside the selected porting scope. |

`rocq-manifest.js` lists the files and pinned upstream source links. Counts
are computed from rows by `app.js`; the manifest does not maintain duplicate
totals. Some Rocq-only parser files remain marked `ignored`, while native
proof-mode classes, environments, and logical tactic rules are now counted.
Their missing rows remain visible; native proof mode does not imply every
Rocq instance has been ported.

When updating a mapping, read both definitions. Matching names alone are not
enough: for example, `ghost_map_elem` only exposes full ownership, and
`PMFromSep` has the direction of Rocq `IntoSep`. New Arend-only APIs and
HeapLang/client modules outside the original dashboard inventory belong in
the implementation guide rather than being fabricated as Rocq rows.

After edits, check row schemas, duplicate names, mapped source declarations,
manifest paths, and local documentation links. Serve the page and check
loading, category totals, search, and combined filters. A source-name check
does not validate theorem equivalence or substitute for typechecking.
