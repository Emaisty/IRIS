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

abstract class ModalIntroMeta extends ExactMeta {
  protected abstract CoreFunctionDefinition modality();
  protected abstract ArendRef lemma();

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = dereference(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression modal)
        || modal.getDefinition() != modality()
        || modal.getDefCallArguments().size() < 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected the corresponding modal goal", contextData.getMarker()));
      return null;
    }
    CoreExpression body = modal.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(lemma()), args),
        contextData.getExpectedType());
  }
}

final class NextMeta extends ModalIntroMeta {
  @Dependency(name = "mkProperLater")
  private CoreFunctionDefinition mkProperLater;
  @Dependency(name = "pm_next")
  private ArendRef pmNext;
  @Override protected CoreFunctionDefinition modality() { return mkProperLater; }
  @Override protected ArendRef lemma() { return pmNext; }
}

final class ModIntroMeta extends ModalIntroMeta {
  @Dependency(name = "mkProperBUpd")
  private CoreFunctionDefinition mkProperBUpd;
  @Dependency(name = "pm_mod_intro")
  private ArendRef pmModIntro;
  @Override protected CoreFunctionDefinition modality() { return mkProperBUpd; }
  @Override protected ArendRef lemma() { return pmModIntro; }
}
