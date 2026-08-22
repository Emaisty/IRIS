# IRIS Arend module layout and dependencies

Last audited: 2026-08-16.

The source hierarchy now follows the original Rocq repository. Arend module
names are obtained directly from these paths, for example
`src/iris/algebra/cmra.ard` is imported as `iris.algebra.cmra`.

## Source hierarchy

```text
src/
├── iris/
│   ├── algebra/             OFEs, CMRAs, algebraic constructions
│   │   └── lib/             reusable composite constructions such as gmap_view
│   ├── bi/                  BI interface, laws, modalities, and big operators
│   ├── base_logic/
│   │   ├── upred.ard        the uPred model
│   │   └── lib/             iProp, ownership, wsat, fancy updates, invariants
│   └── program_logic/       weakest preconditions, lifting, and adequacy
├── iris_heap_lang/          concrete language, contexts, and substitution
├── iris_deprecated/
│   └── program_logic/       the Rocq-compatible Hoare surface
├── stdpp/                   local ports of required stdpp maps and namespaces
└── tests/                   factorial and binder-free generic-heap clients
```

Arend-specific compilation boundaries remain next to their Rocq parent:

- `iris.base_logic.lib.fancy_updates_mask` extends `fancy_updates`.
- `iris.base_logic.lib.wsat_alloc` and `wsat_sigma` extend `wsat`.
- `iris.algebra.gmap_functor` and `gmap_updates` extend `gmap`.
- `iris.algebra.lib.gmap_view_functor` extends `gmap_view`.

These are semantic and caching boundaries, not temporary numbered fragments.

## Dependency layers

```text
stdpp.pmap
   ├── stdpp.coPset ───────────────┐
   ├── iris.algebra.gmap           │
   └── iris.algebra.gset           ├── stdpp.namespaces
                                   └── stdpp.finite_coPset

iris.algebra.ofe
   └── iris.algebra.cmra
          ├── algebra constructions
          └── iris.base_logic.lib.gfunctors
                    ├── iris.base_logic.upred
                    │      ├── iris.bi.updates
                    │      └── iris.bi.big_op
                    └── iris.base_logic.lib.iprop
                              └── iris.base_logic.lib.own
                                      └── iris.base_logic.lib.wsat
                                             ├── fancy_updates
                                             ├── wsat_alloc / wsat_sigma
                                             └── invariants

iris_heap_lang.lang
   └── iris.program_logic.weakestpre
          ├── iris.program_logic.lifting
          ├── iris_deprecated.program_logic.hoare
          └── iris.program_logic.adequacy
```

The recursive proposition construction additionally uses
`iris.algebra.cofe_solver`, `iris.algebra.functions`, and the gmap functor.
The concrete program logic combines `wsatGS` with
`iris.base_logic.lib.gen_heap`.

## Client boundary

Library modules under `iris`, `iris_heap_lang`, `iris_deprecated`, and
`stdpp` do not import from `tests`. The factorial-only fixed-heap CMRA and
compatibility WP stack live in:

- `tests.fact.heap`
- `tests.fact.program_logic`
- `tests.fact`

The binder-free canonical client is `tests.generic_heap`. New non-String
developments should use `iris.program_logic.*` and
`iris.base_logic.lib.gen_heap`, not the factorial compatibility stack.

## Current verification boundary

All non-String library modules typecheck and serialize with the guarded Arend
conversion checker. The only intentionally deferred diagnostics are String
support in `iris_heap_lang.lang` / `iris_heap_lang.lang_subst` and the
dependent `tests.fact` client.
