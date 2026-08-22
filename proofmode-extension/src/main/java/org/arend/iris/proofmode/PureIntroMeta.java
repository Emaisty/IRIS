package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
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

final class PureIntroMeta extends ExactMeta {
  @Dependency(name = "pm_pure_intro")
  private ArendRef pmPureIntro;

  @Dependency(name = "mkProperPure")
  private CoreFunctionDefinition mkProperPure;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression pure)
        || !pure.getDefinition().getName().equals(mkProperPure.getName())
        || pure.getDefCallArguments().size() < 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected a pure goal", contextData.getMarker()));
      return null;
    }
    CoreExpression proposition = pure.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(factory.core(proposition.computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(pmPureIntro), args),
        contextData.getExpectedType());
  }
}
