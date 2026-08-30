package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.core.expr.CoreIntegerExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

class ExactMeta extends ProofModeMeta {
  @Dependency(name = "pm_exact_spatial")
  protected ArendRef pmExactSpatial;

  @Dependency(name = "pm_exact_intuitionistic")
  protected ArendRef pmExactIntuitionistic;

  @Dependency(name = "pm_select_here")
  protected ArendRef pmSelectHere;

  @Dependency(name = "pm_select_there")
  protected ArendRef pmSelectThere;

  @Dependency(name = "pm_persistent_select_here")
  protected ArendRef pmPersistentSelectHere;

  @Dependency(name = "pm_persistent_select_there")
  protected ArendRef pmPersistentSelectThere;

  @Dependency(name = "envs_entails")
  protected CoreFunctionDefinition envsEntails;

  @Dependency(name = "pm_empty")
  protected CoreConstructor pmEmpty;

  @Dependency(name = "pm_snoc")
  protected CoreConstructor pmSnoc;

  @Dependency(name = "nil")
  protected CoreConstructor nilConstructor;

  @Dependency(name = "::")
  protected CoreConstructor consConstructor;

  @Dependency(name = "intuitionistic")
  protected CoreClassField intuitionisticField;

  @Dependency(name = "spatial")
  protected CoreClassField spatialField;

  protected @Nullable String decodeName(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    StringBuilder result = new StringBuilder();
    CoreExpression current = dereference(typechecker, expression);
    while (current instanceof CoreConCallExpression call
        && call.getDefinition().getName().equals(consConstructor.getName())) {
      List<? extends CoreExpression> args = call.getDefCallArguments();
      if (args.size() < 2) return null;
      CoreExpression head = dereference(typechecker, args.get(args.size() - 2));
      if (!(head instanceof CoreIntegerExpression integer)) return null;
      result.appendCodePoint(integer.getBigInteger().intValueExact());
      current = dereference(typechecker, args.getLast());
    }
    return current instanceof CoreConCallExpression call
        && call.getDefinition().getName().equals(nilConstructor.getName())
        ? result.toString() : null;
  }

  protected record BuiltSelection(ConcreteExpression term, CoreExpression proposition) {}

  protected @Nullable BuiltSelection selection(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression environment, String requested,
      boolean persistent) {
    CoreExpression current = dereference(typechecker, environment);
    if (!(current instanceof CoreConCallExpression)) {
      current = dereference(typechecker, current.normalize(NormalizationMode.WHNF));
    }
    if (current instanceof CoreConCallExpression empty
        && empty.getDefinition().getName().equals(pmEmpty.getName())) {
      return null;
    }
    if (!(current instanceof CoreConCallExpression snoc)
        || !snoc.getDefinition().getName().equals(pmSnoc.getName())
        || snoc.getDefCallArguments().size() < 3) {
      return null;
    }
    List<? extends CoreExpression> args = snoc.getDefCallArguments();
    CoreExpression tail = args.get(args.size() - 3);
    CoreExpression storedName = args.get(args.size() - 2);
    CoreExpression proposition = args.getLast();
    String decoded = decodeName(typechecker, storedName);
    var factory = contextData.getFactory();

    if (requested.equals(decoded)) {
      List<ConcreteArgument> callArgs = new ArrayList<>();
      callArgs.add(factory.arg(factory.hole(), false));
      callArgs.add(factory.arg(factory.core(tail.computeTyped()), true));
      callArgs.add(factory.arg(factory.core(storedName.computeTyped()), true));
      callArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      return new BuiltSelection(factory.app(factory.ref(persistent
          ? pmPersistentSelectHere : pmSelectHere), callArgs), proposition);
    }

    BuiltSelection inner = selection(typechecker, contextData, tail,
        requested, persistent);
    if (inner == null) return null;
    List<ConcreteArgument> callArgs = new ArrayList<>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(tail.computeTyped()), true));
    callArgs.add(factory.arg(factory.core(storedName.computeTyped()), true));
    callArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    callArgs.add(factory.arg(inner.term(), true));
    return new BuiltSelection(factory.app(factory.ref(persistent
        ? pmPersistentSelectThere : pmSelectThere), callArgs), inner.proposition());
  }

  protected @Nullable String findMatchingName(ExpressionTypechecker typechecker,
      CoreExpression environment, CoreExpression target) {
    CoreExpression current = dereference(typechecker, environment);
    if (!(current instanceof CoreConCallExpression)) {
      current = dereference(typechecker, current.normalize(NormalizationMode.WHNF));
    }
    if (current instanceof CoreConCallExpression empty
        && empty.getDefinition().getName().equals(pmEmpty.getName())) return null;
    if (!(current instanceof CoreConCallExpression snoc)
        || !snoc.getDefinition().getName().equals(pmSnoc.getName())
        || snoc.getDefCallArguments().size() < 3) return null;
    var args = snoc.getDefCallArguments();
    CoreExpression proposition = dereference(typechecker, args.getLast());
    if (proposition.compare(dereference(typechecker, target), CMP.EQ)) {
      return decodeName(typechecker, args.get(args.size() - 2));
    }
    return findMatchingName(typechecker, args.get(args.size() - 3), target);
  }

  protected boolean containsName(ExpressionTypechecker typechecker,
      CoreExpression environment, String requested) {
    CoreExpression current = dereference(typechecker, environment);
    if (!(current instanceof CoreConCallExpression)) {
      current = dereference(typechecker, current.normalize(NormalizationMode.WHNF));
    }
    if (!(current instanceof CoreConCallExpression snoc)
        || !snoc.getDefinition().getName().equals(pmSnoc.getName())
        || snoc.getDefCallArguments().size() < 3) return false;
    var args = snoc.getDefCallArguments();
    String decoded = decodeName(typechecker, args.get(args.size() - 2));
    return requested.equals(decoded)
        || containsName(typechecker, args.get(args.size() - 3), requested);
  }

  protected boolean environmentContainsName(ExpressionTypechecker typechecker,
      CoreExpression environment, String requested) {
    CoreExpression value = dereference(typechecker, environment);
    CoreClassCallExpression envClass = value instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : value instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) return false;
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    return spatial != null && containsName(typechecker, spatial, requested)
        || intuitionistic != null && containsName(typechecker, intuitionistic, requested);
  }

  protected String freshName(ExpressionTypechecker typechecker,
      CoreExpression environment, String prefix, String... reserved) {
    for (int index = 0; ; index++) {
      String candidate = prefix + index;
      boolean isReserved = false;
      for (String name : reserved) {
        if (candidate.equals(name)) {
          isReserved = true;
          break;
        }
      }
      if (!isReserved
          && !environmentContainsName(typechecker, environment, candidate)) {
        return candidate;
      }
    }
  }

  protected record ResolvedSelection(CoreExpression environment,
      BuiltSelection selection, boolean persistent, CoreExpression target) {}

  protected record GoalData(CoreExpression environment, CoreExpression target) {}

  protected @Nullable GoalData resolveGoal(ExpressionTypechecker typechecker,
      ContextData contextData) {
    if (contextData.getExpectedType() == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode tactic has no expected goal", contextData.getMarker()));
      return null;
    }
    CoreExpression expected = dereference(typechecker, contextData.getExpectedType());
    if (!(expected instanceof CoreFunCallExpression goal)
        || !goal.getDefinition().getName().equals(envsEntails.getName())
        || goal.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode tactic must run inside ipm", contextData.getMarker()));
      return null;
    }
    return new GoalData(dereference(typechecker,
        goal.getDefCallArguments().get(1)), goal.getDefCallArguments().getLast());
  }

  protected @Nullable ResolvedSelection resolveNamed(ExpressionTypechecker typechecker,
      ContextData contextData, String requested) {
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression environment = goal.environment();
    CoreClassCallExpression envClass = environment instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : environment instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect the proof-mode environment", contextData.getMarker()));
      return null;
    }
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    if (spatial == null || intuitionistic == null) return null;

    BuiltSelection selected = selection(typechecker, contextData, spatial,
        requested, false);
    boolean persistent = false;
    if (selected == null) {
      selected = selection(typechecker, contextData, intuitionistic, requested, true);
      persistent = true;
    }
    if (selected == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "No proof-mode hypothesis named '" + requested + "'",
          contextData.getMarker()));
      return null;
    }
    return new ResolvedSelection(environment, selected, persistent,
        goal.target());
  }

  protected @Nullable TypedExpression finishExact(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved) {
    var factory = contextData.getFactory();
    List<ConcreteArgument> callArgs = new ArrayList<>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(resolved.environment().computeTyped()), true));
    callArgs.add(factory.arg(resolved.selection().term(), true));
    return typechecker.typecheck(factory.app(factory.ref(resolved.persistent()
        ? pmExactIntuitionistic : pmExactSpatial), callArgs),
        contextData.getExpectedType());
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;

    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;

    return finishExact(typechecker, contextData, resolved);
  }
}
