package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteStringExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

abstract class ProofModeMeta extends BaseMetaDefinition {
  @Dependency(name = "nil")
  protected ArendRef nil;

  @Dependency(name = "::")
  protected ArendRef cons;

  protected @Nullable TypedExpression apply(ExpressionTypechecker typechecker,
      ContextData contextData, ArendRef lemma, List<ConcreteExpression> arguments) {
    ConcreteExpression call = contextData.getFactory().app(
        contextData.getFactory().ref(lemma), true, arguments);
    return typechecker.typecheck(call, contextData.getExpectedType());
  }

  protected @Nullable String stringArgument(ExpressionTypechecker typechecker,
      ContextData contextData, int index) {
    List<ConcreteExpression> arguments = explicitArguments(contextData);
    if (index >= arguments.size()
        || !(arguments.get(index) instanceof ConcreteStringExpression string)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected a quoted proof-mode pattern", contextData.getMarker()));
      return null;
    }
    return string.getUnescapedString();
  }

  protected ConcreteExpression name(ContextData contextData, String value) {
    ConcreteExpression result = contextData.getFactory().ref(nil);
    int[] codePoints = value.codePoints().toArray();
    for (int i = codePoints.length - 1; i >= 0; i--) {
      result = contextData.getFactory().app(contextData.getFactory().ref(cons), true,
          contextData.getFactory().number(codePoints[i]), result);
    }
    return result;
  }

  protected List<ConcreteExpression> explicitArguments(ContextData contextData) {
    List<ConcreteExpression> result = new ArrayList<>();
    for (ConcreteArgument argument : contextData.getArguments()) {
      if (argument.isExplicit()) result.add(argument.getExpression());
    }
    return result;
  }

  protected boolean requireCount(ExpressionTypechecker typechecker,
      ContextData contextData, int count) {
    if (explicitArguments(contextData).size() == count) return true;
    typechecker.getErrorReporter().report(new TypecheckingError(
        "Expected " + count + " argument(s)", contextData.getMarker()));
    return false;
  }
}
