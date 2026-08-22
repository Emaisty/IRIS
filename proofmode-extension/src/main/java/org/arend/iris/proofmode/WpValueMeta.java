package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
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
import java.util.List;

final class WpValueMeta extends ExactMeta {
  @Dependency(name = "pm_wp_value_intro")
  private ArendRef wpValueIntro;
  @Dependency(name = "pm_ent_apply")
  private ArendRef pmEntApply;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression wpCall)
        || !(wpCall.getDefinition().getName().equals("wp")
          || wpCall.getDefinition().getName().equals("pm_wp"))
        || wpCall.getDefCallArguments().size() < 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_value requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    var wpArgs = wpCall.getDefCallArguments();
    CoreExpression iris = wpArgs.get(wpArgs.size() - 4);
    CoreExpression mask = wpArgs.get(wpArgs.size() - 3);
    CoreExpression expression = dereference(typechecker, wpArgs.get(wpArgs.size() - 2));
    if (!(expression instanceof CoreConCallExpression)) {
      expression = dereference(typechecker, expression.normalize(NormalizationMode.NF));
    }
    CoreExpression post = wpArgs.getLast();
    if (!(expression instanceof CoreConCallExpression valCall)
        || !valCall.getDefinition().getName().equals("Val")
        || valCall.getDefCallArguments().isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_value requires a value expression", contextData.getMarker()));
      return null;
    }
    CoreExpression value = valCall.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    ConcreteExpression precondition = factory.app(
        factory.core(post.computeTyped()), true,
        factory.core(value.computeTyped()));

    List<ConcreteArgument> theoremArgs = new ArrayList<>();
    theoremArgs.add(factory.arg(factory.hole(), false));
    theoremArgs.add(factory.arg(factory.hole(), false));
    theoremArgs.add(factory.arg(factory.core(iris.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(mask.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(value.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(post.computeTyped()), true));
    ConcreteExpression theorem = factory.app(factory.ref(wpValueIntro), theoremArgs);

    List<ConcreteArgument> applyArgs = new ArrayList<>();
    applyArgs.add(factory.arg(factory.hole(), false));
    applyArgs.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    applyArgs.add(factory.arg(precondition, false));
    applyArgs.add(factory.arg(factory.core(target.computeTyped()), false));
    applyArgs.add(factory.arg(theorem, true));
    applyArgs.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(pmEntApply), applyArgs),
        contextData.getExpectedType());
  }
}
