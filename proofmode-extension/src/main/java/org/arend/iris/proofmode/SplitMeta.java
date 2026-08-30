package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

abstract class SplitMeta extends ExactMeta {
  @Dependency(name = "pm_split_empty")
  private ArendRef pmSplitEmpty;
  @Dependency(name = "pm_split_put_left")
  private ArendRef pmSplitPutLeft;
  @Dependency(name = "pm_split_put_right")
  private ArendRef pmSplitPutRight;
  @Dependency(name = "pm_split_sep")
  private ArendRef pmSplitSep;
  @Dependency(name = "pm_split_and")
  private ArendRef pmSplitAnd;
  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;
  @Dependency(name = "mkProperAnd")
  private CoreFunctionDefinition mkProperAnd;

  protected abstract boolean selectedGoLeft();

  protected record BuiltSplit(ConcreteExpression term, Set<String> found) {}

  private boolean accepts(ExpressionTypechecker typechecker,
      ConcreteExpression expression, CoreExpression expectedType) {
    return Boolean.TRUE.equals(typechecker.withCurrentState(tc -> {
      boolean[] hasError = { false };
      TypedExpression result = tc.withErrorReporter(error -> hasError[0] = true,
          checker -> checker.typecheck(expression, expectedType));
      return result != null && !hasError[0];
    }));
  }

  protected @Nullable BuiltSplit buildSplit(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression environment, Set<String> selected) {
    CoreExpression current = dereference(typechecker, environment);
    if (!(current instanceof CoreConCallExpression)) {
      current = dereference(typechecker, current.normalize(NormalizationMode.WHNF));
    }
    var factory = contextData.getFactory();
    if (current instanceof CoreConCallExpression empty
        && empty.getDefinition().getName().equals(pmEmpty.getName())) {
      List<ConcreteArgument> args = new ArrayList<>();
      args.add(factory.arg(factory.hole(), false));
      return new BuiltSplit(factory.app(factory.ref(pmSplitEmpty), args),
          new HashSet<>());
    }
    if (!(current instanceof CoreConCallExpression snoc)
        || !snoc.getDefinition().getName().equals(pmSnoc.getName())
        || snoc.getDefCallArguments().size() < 3) {
      return null;
    }
    var args = snoc.getDefCallArguments();
    CoreExpression tail = args.get(args.size() - 3);
    CoreExpression storedName = args.get(args.size() - 2);
    CoreExpression proposition = args.getLast();
    String decoded = decodeName(typechecker, storedName);
    if (decoded == null) return null;
    BuiltSplit prefix = buildSplit(typechecker, contextData, tail, selected);
    if (prefix == null) return null;
    boolean requested = selected.contains(decoded);
    if (requested) prefix.found().add(decoded);
    boolean putLeft = requested == selectedGoLeft();
    List<ConcreteArgument> callArgs = new ArrayList<>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(tail.computeTyped()), false));
    callArgs.add(factory.arg(prefix.term(), true));
    callArgs.add(factory.arg(factory.core(storedName.computeTyped()), true));
    callArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    return new BuiltSplit(factory.app(factory.ref(putLeft
        ? pmSplitPutLeft : pmSplitPutRight), callArgs), prefix.found());
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 3)) return null;
    String pattern = stringArgument(typechecker, contextData, 0);
    if (pattern == null) return null;
    List<String> names = pattern.trim().isEmpty() ? List.of()
        : Arrays.asList(pattern.trim().split("\\s+"));
    Set<String> selected = new HashSet<>(names);
    if (selected.size() != names.size()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate name in proof-mode split pattern", contextData.getMarker()));
      return null;
    }

    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    List<ConcreteExpression> arguments = explicitArguments(contextData);
    var factory = contextData.getFactory();
    List<ConcreteArgument> andArgs = new ArrayList<>();
    andArgs.add(factory.arg(factory.hole(), false));
    andArgs.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    andArgs.add(factory.arg(arguments.get(1), true));
    andArgs.add(factory.arg(arguments.get(2), true));
    ConcreteExpression andCall = factory.app(factory.ref(pmSplitAnd), andArgs);
    boolean directAnd = target instanceof CoreFunCallExpression conjunction
        && conjunction.getDefinition() == mkProperAnd;
    boolean directSep = target instanceof CoreFunCallExpression separation
        && separation.getDefinition() == mkProperSep;
    if (directAnd || !directSep && selected.isEmpty()
        && accepts(typechecker, andCall, contextData.getExpectedType())) {
      if (!selected.isEmpty()) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Ordinary conjunction duplicates the whole context; use an empty split pattern",
            contextData.getMarker()));
        return null;
      }
      return typechecker.typecheck(andCall, contextData.getExpectedType());
    }

    CoreExpression environment = goal.environment();
    CoreClassCallExpression envClass = environment instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : environment instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) return null;
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    if (spatial == null) return null;
    BuiltSplit split = buildSplit(typechecker, contextData, spatial, selected);
    if (split == null) return null;
    selected.removeAll(split.found());
    if (!selected.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "No spatial proof-mode hypothesis named '" + selected.iterator().next() + "'",
          contextData.getMarker()));
      return null;
    }

    List<ConcreteArgument> callArgs = new ArrayList<>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(environment.computeTyped()), false));
    callArgs.add(factory.arg(split.term(), true));
    CoreExpression leftTarget = directSep
        ? ((CoreFunCallExpression) target).getDefCallArguments().get(
            ((CoreFunCallExpression) target).getDefCallArguments().size() - 2)
        : null;
    CoreExpression rightTarget = directSep
        ? ((CoreFunCallExpression) target).getDefCallArguments().getLast()
        : null;
    callArgs.add(factory.arg(leftTarget == null ? factory.hole()
        : factory.core(leftTarget.computeTyped()), false));
    callArgs.add(factory.arg(rightTarget == null ? factory.hole()
        : factory.core(rightTarget.computeTyped()), false));
    callArgs.add(factory.arg(arguments.get(1), true));
    callArgs.add(factory.arg(arguments.get(2), true));
    return typechecker.typecheck(factory.app(factory.ref(pmSplitSep), callArgs),
        contextData.getExpectedType());
  }
}

final class SplitLeftMeta extends SplitMeta {
  @Override protected boolean selectedGoLeft() { return true; }
}

final class SplitRightMeta extends SplitMeta {
  @Override protected boolean selectedGoLeft() { return false; }
}
