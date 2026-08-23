package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;

final class DestructMeta extends ExactMeta {
  @Dependency(name = "pm_destruct_sep")
  private ArendRef pmDestructSep;

  @Dependency(name = "pm_destruct_persistent")
  private ArendRef pmDestructPersistent;
  @Dependency(name = "pm_destruct_persistent_copy")
  private ArendRef pmDestructPersistentCopy;

  @Dependency(name = "pm_destruct_exist")
  private ArendRef pmDestructExist;
  @Dependency(name = "pm_destruct_exist1")
  private ArendRef pmDestructExist1;
  @Dependency(name = "pm_destruct_exist_intuitionistic")
  private ArendRef pmDestructExistIntuitionistic;

  @Dependency(name = "pm_destruct_pure")
  private ArendRef pmDestructPure;

  @Dependency(name = "pm_destruct_and_pure_l")
  private ArendRef pmDestructAndPureLeft;

  @Dependency(name = "pm_destruct_or")
  private ArendRef pmDestructOr;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Dependency(name = "mkProperPersistently")
  private CoreFunctionDefinition mkProperPersistently;

  @Dependency(name = "mkProperExist")
  private CoreFunctionDefinition mkProperExist;
  @Dependency(name = "mkProperExist1")
  private CoreFunctionDefinition mkProperExist1;

  @Dependency(name = "mkProperPure")
  private CoreFunctionDefinition mkProperPure;

  @Dependency(name = "mkProperAnd")
  private CoreFunctionDefinition mkProperAnd;

  @Dependency(name = "mkProperOr")
  private CoreFunctionDefinition mkProperOr;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    var explicit = explicitArguments(contextData);
    if (explicit.size() < 3 || explicit.size() > 6) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected 3 to 6 arguments", contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    String pattern = stringArgument(typechecker, contextData, 1);
    if (requested == null || pattern == null) return null;
    String trimmedPattern = pattern.trim();
    ConcreteExpression explicitShape = explicit.size() >= 4 ? explicit.get(2) : null;
    ConcreteExpression explicitRight = explicit.size() == 5 ? explicit.get(3) : null;
    ConcreteExpression continuation = explicit.get(explicit.size() - 1);
    if (trimmedPattern.startsWith("#")) {
      if (explicit.size() != 3 && explicit.size() != 4) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Persistent iDestruct expects a name pattern, optional persistence rule, and a continuation",
            contextData.getMarker()));
        return null;
      }
      return destructPersistent(typechecker, contextData, requested,
          trimmedPattern.substring(1).trim());
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (resolved.persistent()) {
      if (proposition instanceof CoreFunCallExpression exists
          && exists.getDefinition() == mkProperExist
          && exists.getDefCallArguments().size() >= 3) {
        return destructExist(typechecker, contextData, resolved, proposition,
            exists, requested, trimmedPattern, explicitShape, continuation);
      }
      String[] names = trimmedPattern.split("\\s+");
      if (names.length == 1 && !trimmedPattern.isEmpty()) {
        return destructExist(typechecker, contextData, resolved, proposition,
            null, requested, trimmedPattern, explicitShape, continuation);
      }
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Only existential intuitionistic hypotheses can currently be destructed",
          contextData.getMarker()));
      return null;
    }
    String[] branchNames = trimmedPattern.split("\\|", -1);
    if (branchNames.length == 2) {
      if (explicit.size() != 4 && explicit.size() != 6) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Disjunction iDestruct expects two branch continuations and optional propositions",
            contextData.getMarker()));
        return null;
      }
      CoreFunCallExpression or = proposition instanceof CoreFunCallExpression call
          && call.getDefinition() == mkProperOr
          && call.getDefCallArguments().size() >= 3 ? call : null;
      return destructOr(typechecker, contextData, resolved, proposition, or,
          requested, branchNames[0].trim(), branchNames[1].trim(), explicit);
    }
    if (proposition instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist
        && exists.getDefCallArguments().size() >= 3) {
      return destructExist(typechecker, contextData, resolved, proposition,
          exists, requested, trimmedPattern, explicitShape, continuation);
    }
    if (proposition instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist1
        && exists.getDefCallArguments().size() >= 3) {
      return destructExist(typechecker, contextData, resolved, proposition,
          exists, requested, trimmedPattern, explicitShape, continuation, true);
    }
    if (proposition instanceof CoreFunCallExpression pure
        && pure.getDefinition() == mkProperPure
        && pure.getDefCallArguments().size() >= 2) {
      return destructPure(typechecker, contextData, resolved, proposition,
          pure, trimmedPattern, explicitShape, continuation);
    }
    if (proposition instanceof CoreFunCallExpression and
        && and.getDefinition() == mkProperAnd
        && and.getDefCallArguments().size() >= 3) {
      CoreExpression left = weakHead(typechecker,
          and.getDefCallArguments().get(and.getDefCallArguments().size() - 2));
      if (left instanceof CoreFunCallExpression pure
          && pure.getDefinition() == mkProperPure
          && pure.getDefCallArguments().size() >= 2) {
        return destructAndPureLeft(typechecker, contextData, resolved,
            proposition, and, pure, requested, trimmedPattern, continuation);
      }
    }
    if (proposition instanceof CoreFunCallExpression sep
        && sep.getDefinition() == mkProperSep
        && sep.getDefCallArguments().size() >= 3) {
      return destructSep(typechecker, contextData, resolved, proposition,
          sep, requested, trimmedPattern, explicitShape, explicitRight, continuation);
    }
    if (trimmedPattern.equals("%")) {
      return destructPure(typechecker, contextData, resolved, proposition,
          null, trimmedPattern, explicitShape, continuation);
    }
    String[] inferredNames = trimmedPattern.split("\\s+");
    if (inferredNames.length == 1 && !trimmedPattern.isEmpty()) {
      return destructExist(typechecker, contextData, resolved, proposition,
          null, requested, trimmedPattern, explicitShape, continuation);
    }
    if (inferredNames.length == 2) {
      return destructSep(typechecker, contextData, resolved, proposition,
          null, requested, trimmedPattern, explicitShape, explicitRight, continuation);
    }
    typechecker.getErrorReporter().report(new TypecheckingError(
        "iDestruct expected a separating conjunction, existential, pure, or persistent proposition",
        contextData.getMarker()));
    return null;
  }

  private @Nullable TypedExpression destructAndPureLeft(
      ExpressionTypechecker typechecker, ContextData contextData,
      ResolvedSelection resolved, CoreExpression proposition,
      CoreFunCallExpression and, CoreFunCallExpression pure,
      String requested, String pattern, ConcreteExpression continuation) {
    if (explicitArguments(contextData).size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure conjunction iDestruct expects a pattern and continuation",
          contextData.getMarker()));
      return null;
    }
    String[] names = pattern.split("\\s+");
    if (names.length != 2 || !names[0].equals("%") || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure conjunction iDestruct expects the pattern '% Hrest'",
          contextData.getMarker()));
      return null;
    }
    String introduced = names[1];
    if (!introduced.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + introduced + "'",
          contextData.getMarker()));
      return null;
    }
    CoreExpression fact = pure.getDefCallArguments().getLast();
    CoreExpression right = and.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression into = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(fact.computeTyped()), false));
    args.add(factory.arg(factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(continuation, true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructAndPureLeft), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructOr(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved, CoreExpression proposition,
      @Nullable CoreFunCallExpression or, String requested, String leftName,
      String rightName, java.util.List<ConcreteExpression> explicit) {
    if (leftName.isEmpty() || rightName.isEmpty()
        || leftName.contains(" ") || rightName.contains(" ")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Disjunction iDestruct expects one name in each branch",
          contextData.getMarker()));
      return null;
    }
    if ((!leftName.equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), leftName))
        || (!rightName.equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), rightName))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iDestruct would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    CoreExpression left = or == null ? null
        : or.getDefCallArguments().get(or.getDefCallArguments().size() - 2);
    CoreExpression right = or == null ? null : or.getDefCallArguments().getLast();
    ConcreteExpression explicitLeft = explicit.size() == 6 ? explicit.get(2) : null;
    ConcreteExpression explicitRight = explicit.size() == 6 ? explicit.get(3) : null;
    ConcreteExpression leftContinuation = explicit.get(explicit.size() - 2);
    ConcreteExpression rightContinuation = explicit.getLast();

    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression into = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, leftName), true));
    args.add(factory.arg(name(contextData, rightName), true));
    args.add(factory.arg(explicitLeft != null ? explicitLeft : left == null
        ? factory.hole() : factory.core(left.computeTyped()), false));
    args.add(factory.arg(explicitRight != null ? explicitRight : right == null
        ? factory.hole() : factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(leftContinuation, true));
    args.add(factory.arg(rightContinuation, true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructOr), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructSep(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression sep,
      String requested, String pattern, @Nullable ConcreteExpression explicitLeft,
      @Nullable ConcreteExpression explicitRight, ConcreteExpression continuation) {
    String[] names = pattern.split("\\s+");
    if (names.length != 2 || names[0].isEmpty() || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Separating-conjunction iDestruct expects exactly two names",
          contextData.getMarker()));
      return null;
    }
    if (names[0].equals(names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + names[0] + "'",
          contextData.getMarker()));
      return null;
    }
    if ((!names[0].equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), names[0]))
        || (!names[1].equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), names[1]))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iDestruct would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }
    if ((explicitLeft == null) != (explicitRight == null)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Explicit separating-conjunction iDestruct expects both propositions",
          contextData.getMarker()));
      return null;
    }
    CoreExpression left = sep == null ? null
        : sep.getDefCallArguments().get(sep.getDefCallArguments().size() - 2);
    CoreExpression right = sep == null ? null : sep.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression split = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, names[0]), true));
    args.add(factory.arg(name(contextData, names[1]), true));
    args.add(factory.arg(explicitLeft != null ? explicitLeft : left == null
        ? factory.hole() : factory.core(left.computeTyped()), false));
    args.add(factory.arg(explicitRight != null ? explicitRight : right == null
        ? factory.hole() : factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(split, true));
    args.add(factory.arg(continuation, true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructSep), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructExist(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression exists,
      String requested, String introduced, @Nullable ConcreteExpression explicitFamily,
      ConcreteExpression continuation) {
    return destructExist(typechecker, contextData, resolved, proposition, exists,
        requested, introduced, explicitFamily, continuation, false);
  }

  private @Nullable TypedExpression destructExist(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression exists,
      String requested, String introduced, @Nullable ConcreteExpression explicitFamily,
      ConcreteExpression continuation, boolean universeOne) {
    if (explicitArguments(contextData).size() > 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Existential iDestruct accepts at most one explicit family",
          contextData.getMarker()));
      return null;
    }
    if (introduced.isEmpty() || introduced.contains(" ") || introduced.equals("%")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Existential iDestruct expects one proof-mode name",
          contextData.getMarker()));
      return null;
    }
    if (!introduced.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + introduced + "'",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    CoreExpression carrier = exists == null ? null
        : exists.getDefCallArguments().get(exists.getDefCallArguments().size() - 2);
    CoreExpression family = exists == null ? null
        : exists.getDefCallArguments().getLast();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression into = factory.app(factory.ref(entailmentRefl), reflArgs);
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(carrier == null ? factory.hole()
        : factory.core(carrier.computeTyped()), false));
    args.add(factory.arg(explicitFamily != null ? explicitFamily : family == null
        ? factory.hole() : factory.core(family.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(continuation, true));
    ArendRef lemma = resolved.persistent() ? pmDestructExistIntuitionistic
        : universeOne ? pmDestructExist1 : pmDestructExist;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructPure(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression pure,
      String pattern, @Nullable ConcreteExpression explicitFact,
      ConcreteExpression continuation) {
    if (explicitArguments(contextData).size() > 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure iDestruct accepts at most one explicit fact",
          contextData.getMarker()));
      return null;
    }
    if (!pattern.equals("%")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure iDestruct expects the '%' pattern", contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    CoreExpression fact = pure == null ? null : pure.getDefCallArguments().getLast();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression into = factory.app(factory.ref(entailmentRefl), reflArgs);
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(explicitFact != null ? explicitFact : fact == null
        ? factory.hole() : factory.core(fact.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(continuation, true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructPure), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructPersistent(
      ExpressionTypechecker typechecker, ContextData contextData,
      String requested, String introducedPattern) {
    String[] introduced = introducedPattern.trim().split("\\s+");
    if (introduced.length < 1 || introduced.length > 2
        || introduced[0].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Persistent iDestruct expects one persistent name and an optional spatial-copy name after '#'",
          contextData.getMarker()));
      return null;
    }
    String persistentName = introduced[0];
    String copyName = introduced.length == 2 ? introduced[1] : null;
    if (copyName != null && (copyName.isEmpty()
        || copyName.equals(persistentName))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Persistent and spatial-copy names must be distinct",
          contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "The hypothesis '" + requested + "' is already intuitionistic",
          contextData.getMarker()));
      return null;
    }
    if (!persistentName.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), persistentName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + persistentName + "'",
          contextData.getMarker()));
      return null;
    }
    if (copyName != null && !copyName.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), copyName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + copyName + "'",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var explicit = explicitArguments(contextData);
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    CoreExpression body = null;
    ConcreteExpression persistent;
    if (explicit.size() == 4) {
      TypedExpression typedPersistent = typechecker.typecheck(explicit.get(2), null);
      if (typedPersistent == null) return null;
      CoreExpression persistentType = weakHead(typechecker,
          typedPersistent.getType());
      if (!(persistentType instanceof CoreFunCallExpression entailment)
          || !entailment.getDefinition().getName().equals("properUPred_ent")
          || entailment.getDefCallArguments().size() < 3) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Explicit persistence rule must be an entailment",
            contextData.getMarker()));
        return null;
      }
      CoreExpression conclusion = weakHead(typechecker,
          entailment.getDefCallArguments().getLast());
      if (!(conclusion instanceof CoreFunCallExpression persistently)
          || !persistently.getDefinition().getName().equals(mkProperPersistently.getName())
          || persistently.getDefCallArguments().size() < 2) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Explicit persistence rule must conclude a persistently proposition",
            contextData.getMarker()));
        return null;
      }
      body = persistently.getDefCallArguments().getLast();
      persistent = factory.core(typedPersistent);
    } else {
      if (!(proposition instanceof CoreFunCallExpression persistently)
          || !persistently.getDefinition().getName().equals(mkProperPersistently.getName())
          || persistently.getDefCallArguments().size() < 2) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Persistent iDestruct expected a persistently proposition or an explicit persistence rule",
            contextData.getMarker()));
        return null;
      }
      body = persistently.getDefCallArguments().getLast();
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      persistent = factory.app(factory.ref(entailmentRefl), reflArgs);
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, persistentName), true));
    if (copyName != null) {
      args.add(factory.arg(name(contextData, copyName), true));
    }
    args.add(factory.arg(body == null ? factory.hole()
        : factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(persistent, true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(copyName == null
        ? pmDestructPersistent : pmDestructPersistentCopy), args),
        contextData.getExpectedType());
  }
}
