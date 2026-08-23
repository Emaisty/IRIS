package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;

final class SpecializeMeta extends ExactMeta {
  @Dependency(name = "pm_specialize")
  private ArendRef pmSpecialize;

  @Dependency(name = "pm_specialize_intuitionistic")
  private ArendRef pmSpecializeIntuitionistic;

  @Dependency(name = "pm_delete")
  private ArendRef pmDelete;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperWand")
  private CoreFunctionDefinition mkProperWand;

  private ConcreteExpression refl(ContextData contextData, CoreExpression proposition) {
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(proposition.computeTyped()), true));
    return factory.app(factory.ref(entailmentRefl), args);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 4)) return null;
    String wandName = stringArgument(typechecker, contextData, 0);
    String argumentName = stringArgument(typechecker, contextData, 1);
    String resultName = stringArgument(typechecker, contextData, 2);
    if (wandName == null || argumentName == null || resultName == null) return null;
    if (wandName.equals(argumentName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize needs two distinct spatial hypotheses", contextData.getMarker()));
      return null;
    }
    if (resultName.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize result name cannot be empty", contextData.getMarker()));
      return null;
    }

    ResolvedSelection wandSelection = resolveNamed(typechecker, contextData, wandName);
    if (wandSelection == null) return null;
    CoreExpression wandProposition = weakHead(typechecker,
        wandSelection.selection().proposition());
    if (!(wandProposition instanceof CoreFunCallExpression wand)
        || !wand.getDefinition().getName().equals(mkProperWand.getName())
        || wand.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize expected a wand hypothesis", contextData.getMarker()));
      return null;
    }
    CoreExpression domain = wand.getDefCallArguments().get(wand.getDefCallArguments().size() - 2);
    CoreExpression codomain = wand.getDefCallArguments().getLast();

    CoreExpression environment = wandSelection.environment();
    CoreClassCallExpression envClass = environment instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : environment instanceof CoreClassCallExpression classCall ? classCall : null;
    CoreExpression spatial = envClass == null ? null
        : envClass.getClosedImplementation(spatialField);
    if (spatial == null) return null;

    var factory = contextData.getFactory();
    CoreExpression argumentEnvironment = spatial;
    if (!wandSelection.persistent()) {
      var deleteArgs = new ArrayList<ConcreteArgument>();
      deleteArgs.add(factory.arg(factory.hole(), false));
      deleteArgs.add(factory.arg(name(contextData, wandName), true));
      deleteArgs.add(factory.arg(factory.core(spatial.computeTyped()), true));
      TypedExpression remaining = typechecker.typecheck(
          factory.app(factory.ref(pmDelete), deleteArgs), null);
      if (remaining == null) return null;
      argumentEnvironment = remaining.getExpression();
    }
    BuiltSelection argumentSelection = selection(typechecker, contextData,
        argumentEnvironment, argumentName, false);
    if (argumentSelection == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "No spatial proof-mode hypothesis named '" + argumentName + "'",
          contextData.getMarker()));
      return null;
    }
    CoreExpression argumentProposition = dereference(typechecker,
        argumentSelection.proposition());
    if (!argumentProposition.compare(dereference(typechecker, domain), CMP.EQ)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize argument does not match the wand domain", contextData.getMarker()));
      return null;
    }
    if (!resultName.equals(wandName) && !resultName.equals(argumentName)
        && environmentContainsName(typechecker, environment, resultName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "A proof-mode hypothesis named '" + resultName + "' already exists",
          contextData.getMarker()));
      return null;
    }
    if (wandSelection.persistent() && resultName.equals(wandName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize cannot replace a reusable intuitionistic wand",
          contextData.getMarker()));
      return null;
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(environment.computeTyped()), false));
    args.add(factory.arg(wandSelection.selection().term(), true));
    args.add(factory.arg(argumentSelection.term(), true));
    args.add(factory.arg(name(contextData, resultName), true));
    args.add(factory.arg(factory.core(domain.computeTyped()), false));
    args.add(factory.arg(factory.core(codomain.computeTyped()), false));
    args.add(factory.arg(factory.core(wandSelection.target().computeTyped()), false));
    args.add(factory.arg(refl(contextData, wandProposition), true));
    args.add(factory.arg(refl(contextData, argumentProposition), true));
    args.add(factory.arg(explicitArguments(contextData).get(3), true));
    return typechecker.typecheck(factory.app(factory.ref(wandSelection.persistent()
            ? pmSpecializeIntuitionistic : pmSpecialize), args),
        contextData.getExpectedType());
  }
}
