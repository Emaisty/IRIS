# Idea: Complex Meta Aliases in Arend

## Goal

Allow a meta to have a mixfix surface syntax, so IRIS propositions can be written in a notation close to the Rocq version. In particular, this should make syntax such as

```arend
{ P } e { Q }
```

expand to an ordinary meta application, for example

```arend
hoare P e Q
```

This is a parser and name-resolution feature. It should not require any change to the Arend kernel or to the meaning of metas.

## Why the current alias mechanism is insufficient

An Arend alias is currently one identifier with an optional precedence:

```arend
\meta entails \alias \infix 2 ⊢ ...
```

The lexer accepts `⊢` as an identifier, the parser puts it into a normal operator sequence, and `MetaBinOpParser` invokes the meta after name resolution. This works for prefix, infix, and postfix applications because the whole notation is represented by one name.

`{ P } e { Q }` is different:

- it has several fixed tokens instead of one alias token;
- it begins with `{`, which cannot currently begin an expression;
- the final `{ Q }` can also look like an implicit argument of `e`;
- there is no identifier at the use site that the current name resolver can resolve to `hoare`.

Consequently, a Java meta alone cannot implement this notation: the input must first be accepted and grouped by the parser.

## Proposed surface declaration

Keep `\alias` unchanged and introduce a separate `\syntax` clause for metas. Overloading `\alias` would blur the distinction between an alternative name and a grammar pattern.

A possible declaration is:

```arend
\meta hoare
  (P : IProp M) (e : Expr) (Q : IProp M)
  \syntax \fix 2 "{" P "}" e "{" Q "}"
  => P ⊢ wp e (\lam _ => Q)
```

The rules of a syntax template would be:

- quoted items are literal token sequences;
- parameter names are expression holes;
- holes correspond to explicit meta parameters;
- the existing precedence and associativity model is reused;
- the template must contain at least one literal token;
- phase one does not allow binders inside a hole.

The exact spelling of `\syntax` is not important for the prototype. Its semantics and ambiguity rules are the important parts.

For a less ambiguous first IRIS notation, use an identifier as an anchor:

```arend
\meta wpNotation
  (e : Expr) (Q : Value -> IProp M)
  \syntax \fix 2 "WP" e "{{" Q "}}"
  => wp e Q
```

with use-site syntax such as:

```arend
WP e {{ Q }}
```

## Proposed compilation pipeline

The feature should lower to the existing concrete syntax before typechecking:

```text
source tokens
  -> raw expression/token sequence
  -> scoped mixfix-pattern matching
  -> ordinary Concrete meta application
  -> existing meta resolution and typechecking
```

The mixfix matcher should not invoke the typechecker to choose a parse. A source phrase must have one syntactic interpretation before elaboration.

### 1. Store a syntax pattern

Attach zero or more syntax patterns to `MetaReferable`. A minimal representation is conceptually:

```text
SyntaxPattern
  owner: MetaReferable
  parts: LiteralTokenSequence | Hole(parameterIndex, bindingPower)
  precedence: Precedence
```

The pattern must be available through scopes and imports just like the meta itself. Imported patterns therefore need to be included in module serialization.

### 2. Preserve enough unparsed syntax

The current grammar turns application syntax into `Concrete.BinOpSequenceExpression`. This representation is a good model, but it cannot represent a leading brace group as an expression atom.

For the general feature, add a raw expression sequence whose elements can be:

- an already parsed expression atom;
- a literal identifier/operator token;
- a balanced delimiter group with its source range.

Then run a new `MixfixParser` before `MetaBinOpParser`. Once a pattern is matched, replace it with a normal reference/application headed by its `MetaReferable`. All later passes can remain unchanged.

Do not try to generate a new ANTLR grammar for every imported notation. The grammar should accept a stable token-tree-like representation; the scoped matcher should interpret it.

### 3. Discover visible patterns before matching

Mixfix resolution needs the patterns declared in the current module and imported modules. There are two reasonable policies:

- syntax is available only after its declaration; or
- declaration headers are collected before expression bodies are parsed.

The second policy is closer to ordinary Arend name resolution, but it requires a header-discovery pass. The prototype can start with imported and earlier declarations only, provided this limitation is explicit.

### 4. Lower to an existing meta call

For example, the matcher should turn

```arend
{ P } e { Q }
```

into the concrete equivalent of

```arend
hoare P e Q
```

This preserves the existing `MetaResolver` and `MetaDefinition` APIs. Source ranges for every hole should be retained so that errors point to `P`, `e`, or `Q`, rather than only to the complete notation.

## Ambiguity policy

This part must be specified before implementing the general feature.

### Braces

At an expression boundary, `{` is currently not a valid expression starter, so recognizing `{ P } e { Q }` there is backward-compatible. After a function expression, however, `{ P }` already means an implicit argument. Therefore:

- try a leading-brace mixfix pattern only at an expression boundary;
- preserve the old interpretation of `f {P} e {Q}`;
- require parentheses when the middle expression ends in implicit arguments and the split is ambiguous;
- consider `{{{ P }}} e {{{ Q }}}` as a safer IRIS spelling if exact single braces cause poor error recovery.

### Competing patterns

When several visible patterns match:

1. prefer the match with the longest literal skeleton;
2. apply precedence and associativity;
3. if candidates still tie, report an ambiguity listing their qualified meta names.

Import order and inferred types must not silently break a tie.

### Scope

Opening a namespace should make its syntax patterns visible. Hiding or renaming the underlying meta should have a defined effect on its patterns; the simplest rule is that a pattern is visible exactly when its owner meta is visible under the same namespace command.

## Minimal implementation plan

### Phase 0: validate the IRIS use case

Hard-code one experimental concrete form, preferably the anchored form:

```arend
WP e {{ Q }}
```

Lower it to a normal `wpNotation e Q` meta call. This validates expression boundaries, source positions, error recovery, and the interaction with ordinary operators without first building a general notation language.

### Phase 1: expression-only mixfix patterns

- add `\syntax` to meta declarations;
- support literal tokens and expression holes;
- attach patterns to `MetaReferable`;
- match patterns before ordinary binary-operator parsing;
- serialize patterns for imports;
- reject ambiguous patterns with a dedicated error;
- keep all existing `\alias` behavior unchanged.

### Phase 2: exact Hoare syntax

- admit balanced brace groups at expression boundaries;
- support `{ P } e { Q }`;
- test nested notations and middle expressions containing applications;
- settle the single-brace versus triple-brace spelling from actual IRIS examples.

### Phase 3: binders, only if needed

A notation such as

```arend
WP e {{ x => Q }}
```

needs a binder hole whose scope includes `Q`. This is substantially more than expression substitution. Add an explicit binder marker to syntax templates and lower it to a `Concrete.LamExpression`. Do not infer binders merely because a hole happens to contain an identifier.

## Likely Arend source locations

In the current Arend checkout, the relevant starting points are:

- `buildSrc/src/main/antlr/org/arend/frontend/parser/Arend.g4`: command-line parser grammar; `alias`, `definition`, `expr`, `argument`, and `atom`;
- `cli/src/main/java/org/arend/frontend/parser/BuildVisitor.java`: builds `MetaReferable`, aliases, and `Concrete.BinOpSequenceExpression`;
- `base/src/main/java/org/arend/term/concrete/Concrete.java`: concrete expression nodes and binary-operator sequences;
- `base/src/main/java/org/arend/naming/binOp/MetaBinOpParser.java`: resolves prefix/infix/postfix metas inside operator sequences;
- `base/src/main/java/org/arend/naming/resolving/visitor/ExpressionResolveNameVisitor.java`: resolves sequence references and invokes `MetaBinOpParser`;
- `base/src/main/java/org/arend/naming/reference/MetaReferable.java`: natural owner for syntax-pattern metadata;
- `proto/src/main/proto/Definition.proto`: serialized referable information;
- `base/src/main/java/org/arend/module/serialization/ModuleSerialization.java` and `ModuleDeserialization.java`: imported pattern persistence;
- `intellij/src/main/grammars/ArendParser.bnf` and `ArendLexer.flex`: IDE parser/highlighting support.

Both the command-line grammar and the IntelliJ grammar must eventually agree. Updating only `Arend.g4` would make the CLI accept syntax that the IDE still marks as invalid.

## Tests

Add focused cases to the existing parser, name-resolution, and meta-resolver test suites:

- a syntax declaration parses and is attached to its meta;
- the notation lowers to the same concrete call as the plain meta name;
- precedence works when the notation is nested under `⊢`, `∗`, and `-∗`;
- notation imported from another module is visible;
- `\hiding` removes it according to the chosen scope rule;
- two matching patterns produce a deterministic ambiguity error;
- old implicit arguments such as `f {P}` parse exactly as before;
- malformed or incomplete notation has a local, useful parser error;
- command-line and IntelliJ parsers accept the same examples.

The IRIS acceptance test should contain the plain and notated versions of the same lemma and verify that both typecheck.

## Non-goals

- changing the kernel;
- type-directed parsing;
- arbitrary lexer macros;
- a complete tactic or proof-mode language;
- binder-aware notation in the first implementation;
- rewriting the existing IRIS development before the notation is stable.

## Recommended first experiment

Implement only `WP e {{ Q }}` with a fixed parser rule and lower it immediately to the existing `WP` meta/application. If that prototype preserves source locations and composes correctly with the current `BinOpSequenceExpression` and `MetaBinOpParser`, generalize the fixed rule into `SyntaxPattern` and `MixfixParser`. Try exact `{ P } e { Q }` only after the matcher has a clear expression-boundary and ambiguity policy.

This keeps the first change small while testing the one architectural question that matters: whether mixfix matching can be inserted before the existing meta/operator resolver without disturbing the rest of Arend.
