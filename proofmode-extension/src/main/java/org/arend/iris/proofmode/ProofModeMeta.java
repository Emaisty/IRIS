package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteStringExpression;
import org.arend.ext.core.context.CoreEvaluatingBinding;
import org.arend.ext.core.expr.CoreAppExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.core.expr.CoreLamExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.expr.CoreReferenceExpression;
import org.arend.ext.core.level.LevelSubstitution;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
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

  protected CoreExpression dereference(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = expression.getUnderlyingExpression();
    while (true) {
      if (result instanceof CoreInferenceReferenceExpression inference) {
        if (inference.getSubstExpression() == null) {
          typechecker.solveEquationsFor(inference.getVariable());
        }
        if (inference.getSubstExpression() == null) break;
        result = inference.getSubstExpression().getUnderlyingExpression();
      } else if (result instanceof CoreReferenceExpression reference
          && reference.getBinding() instanceof CoreEvaluatingBinding binding) {
        result = binding.getExpression().getUnderlyingExpression();
      } else {
        break;
      }
    }
    return result;
  }

  protected CoreExpression weakHead(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = dereference(typechecker, expression);
    if (result instanceof CoreAppExpression application) {
      CoreExpression function = dereference(typechecker, application.getFunction());
      if (function instanceof CoreLamExpression lambda) {
        var parameter = lambda.getParameters();
        CoreExpression body = parameter.getNext().hasNext()
            ? lambda.dropParameters(1) : lambda.getBody();
        CoreExpression reduced = typechecker.substitute(body,
            LevelSubstitution.EMPTY,
            List.of(new SubstitutionPair(parameter.getBinding(),
                typechecker.getFactory().core(
                    application.getArgument().computeTyped()))));
        if (reduced != null) return weakHead(typechecker, reduced);
      }
    }
    if (result instanceof CoreFieldCallExpression fieldCall) {
      CoreExpression argument = dereference(typechecker, fieldCall.getArgument());
      CoreClassCallExpression classCall = argument instanceof CoreNewExpression newExpression
          ? newExpression.getClassCall()
          : argument instanceof CoreClassCallExpression call ? call : null;
      if (classCall != null) {
        CoreExpression implementation = classCall.getClosedImplementation(
            fieldCall.getDefinition());
        if (implementation == null) {
          implementation = classCall.getImplementation(fieldCall.getDefinition(),
              argument.computeTyped());
        }
        if (implementation != null) return weakHead(typechecker, implementation);
      }
    }
    if (result instanceof CoreFunCallExpression
        || result instanceof CoreConCallExpression
        || result instanceof CoreNewExpression
        || result instanceof CoreClassCallExpression) return result;
    return dereference(typechecker, result.normalize(NormalizationMode.WHNF));
  }

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
