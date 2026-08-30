package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
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

final class WpApplyMeta extends ExactMeta {
  @Dependency(name = "pm_ent_apply")
  private ArendRef pmEntApply;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    var factory = contextData.getFactory();
    var arguments = explicitArguments(contextData);
    TypedExpression rule = typechecker.typecheck(arguments.get(0), null);
    if (rule == null) return null;
    CoreExpression ruleType = weakHead(typechecker, rule.getType());
    if (!(ruleType instanceof CoreFunCallExpression entailment)
        || !entailment.getDefinition().getName().equals("properUPred_ent")
        || entailment.getDefCallArguments().size() < 3) {
      String actual = ruleType instanceof CoreFunCallExpression call
          ? call.getDefinition().getName()
          : ruleType.getClass().getSimpleName();
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_apply expects an entailment theorem; got " + actual,
          contextData.getMarker()));
      return null;
    }
    var entailmentArgs = entailment.getDefCallArguments();
    CoreExpression source = entailmentArgs.get(entailmentArgs.size() - 2);
    var callArgs = new ArrayList<ConcreteArgument>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    callArgs.add(factory.arg(factory.core(source.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(goal.target().computeTyped()), false));
    callArgs.add(factory.arg(factory.core(rule), true));
    callArgs.add(factory.arg(arguments.get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(pmEntApply), callArgs),
        contextData.getExpectedType());
  }
}
