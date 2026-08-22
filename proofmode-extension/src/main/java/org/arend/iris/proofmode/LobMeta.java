package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.arend.ext.error.TypecheckingError;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;

final class LobMeta extends ExactMeta {
  @Dependency(name = "pm_lob")
  private ArendRef pmLob;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    String introduced = stringArgument(typechecker, contextData, 0);
    if (introduced == null) return null;
    if (introduced.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode hypothesis names cannot be empty", contextData.getMarker()));
      return null;
    }
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    if (environmentContainsName(typechecker, goal.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode hypothesis '" + introduced + "' already exists",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(goal.target().computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(pmLob), args),
        contextData.getExpectedType());
  }
}
