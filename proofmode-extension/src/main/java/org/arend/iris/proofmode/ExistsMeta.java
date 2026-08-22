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

final class ExistsMeta extends ExactMeta {
  @Dependency(name = "pm_exists")
  private ArendRef pmExists;

  @Dependency(name = "mkProperExist")
  private CoreFunctionDefinition mkProperExist;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression exists)
        || !exists.getDefinition().getName().equals(mkProperExist.getName())
        || exists.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected an existential goal", contextData.getMarker()));
      return null;
    }
    var existsArgs = exists.getDefCallArguments();
    CoreExpression carrier = existsArgs.get(existsArgs.size() - 2);
    CoreExpression family = existsArgs.getLast();
    var explicit = explicitArguments(contextData);
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(factory.core(carrier.computeTyped()), false));
    args.add(factory.arg(factory.core(family.computeTyped()), false));
    args.add(factory.arg(explicit.get(0), true));
    args.add(factory.arg(explicit.get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(pmExists), args),
        contextData.getExpectedType());
  }
}
