package org.arend.iris.proofmode;

import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

final class AssumptionMeta extends ExactMeta {
  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 0)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression environment = dereference(typechecker, goal.environment());
    CoreClassCallExpression envClass = environment instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : environment instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) return null;
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    if (spatial == null || intuitionistic == null) return null;
    String name = findMatchingName(typechecker, spatial, goal.target());
    if (name == null) name = findMatchingName(typechecker, intuitionistic, goal.target());
    if (name == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "No proof-mode assumption matches the goal", contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, name);
    return resolved == null ? null : finishExact(typechecker, contextData, resolved);
  }
}
