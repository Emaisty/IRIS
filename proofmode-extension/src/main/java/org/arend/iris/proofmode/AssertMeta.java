package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreNewExpression;
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

final class AssertMeta extends SplitMeta {
  @Dependency(name = "pm_assert")
  private ArendRef pmAssert;

  @Override protected boolean selectedGoLeft() { return true; }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 5)) return null;
    String newName = stringArgument(typechecker, contextData, 0);
    String pattern = stringArgument(typechecker, contextData, 1);
    if (newName == null || pattern == null) return null;
    if (newName.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode hypothesis names cannot be empty", contextData.getMarker()));
      return null;
    }
    List<String> names = pattern.trim().isEmpty() ? List.of()
        : Arrays.asList(pattern.trim().split("\\s+"));
    Set<String> selected = new HashSet<>(names);
    if (selected.size() != names.size()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate name in iAssert resource pattern", contextData.getMarker()));
      return null;
    }

    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    if (!selected.contains(newName)
        && environmentContainsName(typechecker, goal.environment(), newName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode hypothesis '" + newName + "' already exists",
          contextData.getMarker()));
      return null;
    }
    CoreExpression value = dereference(typechecker, goal.environment());
    CoreClassCallExpression envClass = value instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : value instanceof CoreClassCallExpression classCall ? classCall : null;
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

    var arguments = explicitArguments(contextData);
    var factory = contextData.getFactory();
    var callArgs = new ArrayList<ConcreteArgument>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    callArgs.add(factory.arg(split.term(), true));
    callArgs.add(factory.arg(name(contextData, newName), true));
    callArgs.add(factory.arg(arguments.get(2), false));
    callArgs.add(factory.arg(factory.core(goal.target().computeTyped()), false));
    callArgs.add(factory.arg(arguments.get(3), true));
    callArgs.add(factory.arg(arguments.get(4), true));
    return typechecker.typecheck(factory.app(factory.ref(pmAssert), callArgs),
        contextData.getExpectedType());
  }
}
