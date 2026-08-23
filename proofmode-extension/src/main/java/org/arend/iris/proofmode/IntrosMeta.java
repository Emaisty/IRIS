package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.ArrayList;

final class IntrosMeta extends ExactMeta {
  @Dependency(name = "pm_intros_sep")
  private ArendRef pmIntrosSep;

  @Dependency(name = "pm_rename_spatial")
  private ArendRef pmRenameSpatial;

  @Dependency(name = "envs_entails")
  private CoreFunctionDefinition envsEntails;

  @Dependency(name = "pm_snoc")
  private CoreConstructor pmSnoc;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Dependency(name = "intuitionistic")
  private CoreClassField intuitionisticField;

  @Dependency(name = "spatial")
  private CoreClassField spatialField;

  @Override
  protected CoreExpression dereference(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = expression.getUnderlyingExpression();
    while (result instanceof CoreInferenceReferenceExpression inference) {
      if (inference.getSubstExpression() == null) {
        typechecker.solveEquationsFor(inference.getVariable());
      }
      if (inference.getSubstExpression() == null) break;
      result = inference.getSubstExpression().getUnderlyingExpression();
    }
    return result;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    String pattern = stringArgument(typechecker, contextData, 0);
    if (pattern == null) return null;
    String[] names = pattern.trim().split("\\s+");
    if (names.length == 1 && !names[0].isEmpty()) {
      String introduced = names[0];
      ResolvedSelection resolved = resolveNamed(typechecker, contextData, "");
      if (resolved == null) return null;
      if (resolved.persistent()) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "iIntros expected an anonymous spatial hypothesis",
            contextData.getMarker()));
        return null;
      }
      if (environmentContainsName(typechecker, resolved.environment(), introduced)) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Proof-mode hypothesis '" + introduced + "' already exists",
            contextData.getMarker()));
        return null;
      }
      var factory = contextData.getFactory();
      var callArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
      callArgs.add(factory.arg(factory.hole(), false));
      callArgs.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
      callArgs.add(factory.arg(resolved.selection().term(), true));
      callArgs.add(factory.arg(name(contextData, introduced), true));
      callArgs.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
      callArgs.add(factory.arg(explicitArguments(contextData).get(1), true));
      return typechecker.typecheck(factory.app(factory.ref(pmRenameSpatial), callArgs),
          contextData.getExpectedType());
    }
    if (names.length != 2 || names[0].isEmpty() || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros expects one name or two separating-conjunction names",
          contextData.getMarker()));
      return null;
    }
    if (names[0].equals(names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + names[0] + "'",
          contextData.getMarker()));
      return null;
    }
    var arguments = explicitArguments(contextData);
    ConcreteExpression next = arguments.get(1);

    CoreExpression expected = dereference(typechecker, contextData.getExpectedType());
    if (!(expected instanceof CoreFunCallExpression goal)
        || goal.getDefinition() != envsEntails
        || goal.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros must run inside ipm", contextData.getMarker()));
      return null;
    }

    CoreExpression envExpression = dereference(typechecker, goal.getDefCallArguments().get(1));
    CoreClassCallExpression envClass = envExpression instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : envExpression instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect the proof-mode environment", contextData.getMarker()));
      return null;
    }
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    if (intuitionistic == null || spatial == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Incomplete proof-mode environment", contextData.getMarker()));
      return null;
    }
    if (environmentContainsName(typechecker, envExpression, names[0])
        || environmentContainsName(typechecker, envExpression, names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }

    CoreExpression spatialCore = dereference(typechecker, spatial);
    if (!(spatialCore instanceof CoreConCallExpression snoc)
        || snoc.getDefinition() != pmSnoc
        || snoc.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros expected one spatial hypothesis", contextData.getMarker()));
      return null;
    }
    List<? extends CoreExpression> snocArgs = snoc.getDefCallArguments();
    CoreExpression tail = snocArgs.get(snocArgs.size() - 3);
    CoreExpression anonymous = snocArgs.get(snocArgs.size() - 2);
    CoreExpression proposition = dereference(typechecker, snocArgs.get(snocArgs.size() - 1));
    if (!(proposition instanceof CoreFunCallExpression)) {
      proposition = dereference(typechecker,
          proposition.normalize(NormalizationMode.WHNF));
    }
    if (!(proposition instanceof CoreFunCallExpression sep)
        || !sep.getDefinition().getName().equals(mkProperSep.getName())
        || sep.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros expected a separating conjunction, got "
              + proposition.getClass().getSimpleName(), contextData.getMarker()));
      return null;
    }
    List<? extends CoreExpression> sepArgs = sep.getDefCallArguments();
    CoreExpression left = sepArgs.get(sepArgs.size() - 2);
    CoreExpression right = sepArgs.get(sepArgs.size() - 1);
    CoreExpression target = goal.getDefCallArguments().getLast();

    var factory = contextData.getFactory();
    var callArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(intuitionistic.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(tail.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(anonymous.computeTyped()), false));
    callArgs.add(factory.arg(name(contextData, names[0]), true));
    callArgs.add(factory.arg(name(contextData, names[1]), true));
    callArgs.add(factory.arg(factory.core(left.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(right.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(target.computeTyped()), false));
    callArgs.add(factory.arg(next, true));
    ConcreteExpression call = factory.app(factory.ref(pmIntrosSep), callArgs);
    return typechecker.typecheck(call, contextData.getExpectedType());
  }
}
