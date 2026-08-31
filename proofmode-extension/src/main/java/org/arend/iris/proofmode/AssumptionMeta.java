package org.arend.iris.proofmode;

import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

final class AssumptionMeta extends ExactMeta {
  private record AssumptionEvidence(CoreExpression source,
      CoreExpression target, ConcreteExpression term) {}

  private @Nullable AssumptionEvidence evidence(ExpressionTypechecker typechecker,
      ContextData contextData, ConcreteExpression expression) {
    ClassEvidence checked = classEvidence(typechecker, contextData,
        expression, pmFromAssumption, "PMFromAssumption");
    if (checked == null) return null;
    CoreExpression source = classField(checked, "P");
    CoreExpression target = classField(checked, "Q");
    if (source == null || target == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMFromAssumption evidence",
          contextData.getMarker()));
      return null;
    }
    return new AssumptionEvidence(source, target, checked.term());
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> arguments = explicitArguments(contextData);
    if (arguments.size() > 1) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected optional PMFromAssumption evidence",
          contextData.getMarker()));
      return null;
    }
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    AssumptionEvidence evidence = arguments.isEmpty() ? null
        : evidence(typechecker, contextData, arguments.getFirst());
    if (!arguments.isEmpty() && evidence == null) return null;
    if (evidence != null && !evidence.target().compare(
        dereference(typechecker, goal.target()), CMP.EQ)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "PMFromAssumption evidence does not produce the current goal",
          contextData.getMarker()));
      return null;
    }
    CoreExpression environment = dereference(typechecker, goal.environment());
    CoreClassCallExpression envClass = environment instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : environment instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) return null;
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    if (spatial == null || intuitionistic == null) return null;
    CoreExpression source = evidence == null ? goal.target() : evidence.source();
    String name = findMatchingName(typechecker, spatial, source);
    if (name == null) name = findMatchingName(typechecker, intuitionistic, source);
    if (name == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "No proof-mode assumption matches the goal", contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, name);
    return resolved == null ? null : finishExact(typechecker, contextData,
        resolved, evidence == null ? null : evidence.term());
  }
}
