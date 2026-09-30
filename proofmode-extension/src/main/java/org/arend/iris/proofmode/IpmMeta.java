package org.arend.iris.proofmode;

import org.arend.ext.reference.ArendRef;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;

final class IpmMeta extends ProofModeMeta {
  @Dependency(name = "pm_start")
  private ArendRef pmStart;

  @Dependency(name = "properUPred_ent")
  private CoreFunctionDefinition properUPredEnt;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    CoreExpression expected = weakHead(typechecker, contextData.getExpectedType());
    if (!(expected instanceof CoreFunCallExpression entailment)
        || !entailment.getDefinition().getName().equals(properUPredEnt.getName())
        || entailment.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "ipm expects a ProperUPred entailment", contextData.getMarker()));
      return null;
    }
    var entailmentArgs = entailment.getDefCallArguments();
    CoreExpression source = entailmentArgs.get(entailmentArgs.size() - 2);
    CoreExpression target = entailmentArgs.getLast();
    var factory = contextData.getFactory();
    var callArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(source.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(target.computeTyped()), false));
    callArgs.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(pmStart), callArgs),
        contextData.getExpectedType());
  }
}
