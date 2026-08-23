package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
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
    var explicit = explicitArguments(contextData);
    if (explicit.size() != 2 && explicit.size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iExists expects a witness, an optional family, and a continuation",
          contextData.getMarker()));
      return null;
    }
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    CoreExpression carrier = null;
    CoreExpression family = null;
    if (target instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist
        && exists.getDefCallArguments().size() >= 3) {
      var existsArgs = exists.getDefCallArguments();
      carrier = existsArgs.get(existsArgs.size() - 2);
      family = existsArgs.getLast();
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(carrier == null ? factory.hole()
        : factory.core(carrier.computeTyped()), false));
    ConcreteExpression familyArgument = explicit.size() == 3 ? explicit.get(1)
        : family == null ? factory.hole() : factory.core(family.computeTyped());
    args.add(factory.arg(familyArgument, false));
    args.add(factory.arg(explicit.get(0), true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(pmExists), args),
        contextData.getExpectedType());
  }
}
