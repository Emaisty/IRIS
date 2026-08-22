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

abstract class OrMeta extends ExactMeta {
  @Dependency(name = "mkProperOr")
  private CoreFunctionDefinition mkProperOr;

  protected abstract ArendRef lemma();

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = dereference(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression or)
        || !or.getDefinition().getName().equals(mkProperOr.getName())
        || or.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected a disjunction goal", contextData.getMarker()));
      return null;
    }
    var orArgs = or.getDefCallArguments();
    CoreExpression left = orArgs.get(orArgs.size() - 2);
    CoreExpression right = orArgs.getLast();
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(factory.core(left.computeTyped()), false));
    args.add(factory.arg(factory.core(right.computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(lemma()), args),
        contextData.getExpectedType());
  }
}

final class LeftMeta extends OrMeta {
  @Dependency(name = "pm_left")
  private ArendRef pmLeft;

  @Override protected ArendRef lemma() { return pmLeft; }
}

final class RightMeta extends OrMeta {
  @Dependency(name = "pm_right")
  private ArendRef pmRight;

  @Override protected ArendRef lemma() { return pmRight; }
}
