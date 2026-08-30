package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
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
import java.util.List;

final class FrameMeta extends ExactMeta {
  @Dependency(name = "pm_frame_spatial")
  private ArendRef pmFrameSpatial;

  @Dependency(name = "pm_frame_intuitionistic")
  private ArendRef pmFrameIntuitionistic;

  @Dependency(name = "pm_emp_intro")
  private ArendRef pmEmpIntro;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    if (explicit.isEmpty()) return autoFrame(typechecker, contextData);
    if (explicit.size() != 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iFrame expects no arguments or a quoted pattern and continuation",
          contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    String[] names = requested.trim().split("\\s+");
    if (names.length > 1) {
      ConcreteExpression next = explicit.get(1);
      var factory = contextData.getFactory();
      for (int i = names.length - 1; i >= 0; i--) {
        next = factory.app(factory.meta("iFrame", this), true,
            factory.string(names[i]), next);
      }
      return typechecker.typecheck(next, contextData.getExpectedType());
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    var factory = contextData.getFactory();
    CoreExpression target = weakHead(typechecker, resolved.target());
    ConcreteExpression residual = target instanceof CoreFunCallExpression sep
        && sep.getDefinition() == mkProperSep
        && sep.getDefCallArguments().size() >= 3
        ? factory.core(sep.getDefCallArguments().getLast().computeTyped())
        : factory.hole();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(residual, false));
    args.add(factory.arg(explicit.get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(resolved.persistent()
            ? pmFrameIntuitionistic : pmFrameSpatial), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression autoFrame(ExpressionTypechecker typechecker,
      ContextData contextData) {
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;

    String requested = matchingName(typechecker, goal.environment(), goal.target());
    if (requested != null) {
      ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
      return resolved == null ? null : finishExact(typechecker, contextData, resolved);
    }

    CoreExpression target = weakHead(typechecker, goal.target());
    if (target instanceof CoreFunCallExpression sep
        && sep.getDefinition() == mkProperSep
        && sep.getDefCallArguments().size() >= 3) {
      requested = matchingName(typechecker, goal.environment(),
          sep.getDefCallArguments().get(sep.getDefCallArguments().size() - 2));
      if (requested == null) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "iFrame could not match the left separating conjunct",
            contextData.getMarker()));
        return null;
      }
      var factory = contextData.getFactory();
      ConcreteExpression next = factory.meta("iFrame", this);
      ConcreteExpression call = factory.app(factory.meta("iFrame", this), true,
          factory.string(requested), next);
      return typechecker.typecheck(call, contextData.getExpectedType());
    }

    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    return typechecker.typecheck(factory.app(factory.ref(pmEmpIntro), args),
        contextData.getExpectedType());
  }

  private @Nullable String matchingName(ExpressionTypechecker typechecker,
      CoreExpression environment, CoreExpression target) {
    CoreExpression value = dereference(typechecker, environment);
    CoreClassCallExpression envClass = value instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : value instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) return null;
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    String result = spatial == null ? null
        : findMatchingName(typechecker, spatial, target);
    return result != null || intuitionistic == null ? result
        : findMatchingName(typechecker, intuitionistic, target);
  }
}
