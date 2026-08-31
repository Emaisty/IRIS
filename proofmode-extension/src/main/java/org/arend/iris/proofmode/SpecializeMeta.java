package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteStringExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
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
import java.util.List;

final class SpecializeMeta extends ExactMeta {
  @Dependency(name = "PMIntoWand")
  private CoreClassDefinition pmIntoWand;

  @Dependency(name = "pm_specialize")
  private ArendRef pmSpecialize;

  @Dependency(name = "pm_specialize_intuitionistic")
  private ArendRef pmSpecializeIntuitionistic;
  @Dependency(name = "pm_specialize_into_wand")
  private ArendRef pmSpecializeIntoWand;
  @Dependency(name = "pm_specialize_into_wand_intuitionistic")
  private ArendRef pmSpecializeIntoWandIntuitionistic;

  @Dependency(name = "pm_delete")
  private ArendRef pmDelete;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperWand")
  private CoreFunctionDefinition mkProperWand;

  @Dependency(name = "PMIntoForall")
  private CoreClassDefinition pmIntoForall;
  @Dependency(name = "pm_specialize_forall")
  private ArendRef pmSpecializeForall;
  @Dependency(name = "pm_specialize_into_forall")
  private ArendRef pmSpecializeIntoForall;
  @Dependency(name = "mkProperForall")
  private CoreFunctionDefinition mkProperForall;

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
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    if (explicit.size() >= 2
        && !(explicit.get(1) instanceof ConcreteStringExpression)) {
      return specializeForall(typechecker, contextData, explicit);
    }
    if (explicit.size() < 4 || explicit.size() > 5) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected wand, argument, result, optional PMIntoWand evidence, and continuation",
          contextData.getMarker()));
      return null;
    }
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
    ClassEvidence evidence = explicit.size() == 5
        ? classEvidence(typechecker, contextData, explicit.get(3),
            pmIntoWand, "PMIntoWand") : null;
    if (explicit.size() == 5 && evidence == null) return null;
    CoreFunCallExpression wand = wandProposition instanceof CoreFunCallExpression call
        && call.getDefinition().getName().equals(mkProperWand.getName())
        && call.getDefCallArguments().size() >= 3 ? call : null;
    if (evidence == null && wand == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize expected a wand hypothesis", contextData.getMarker()));
      return null;
    }
    CoreExpression domain = evidence == null
        ? wand.getDefCallArguments().get(wand.getDefCallArguments().size() - 2)
        : classField(evidence, "Q");
    CoreExpression codomain = evidence == null
        ? wand.getDefCallArguments().getLast() : classField(evidence, "R");
    if (domain == null || codomain == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMIntoWand evidence", contextData.getMarker()));
      return null;
    }

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
    args.add(factory.arg(evidence == null
        ? refl(contextData, wandProposition) : evidence.term(), true));
    args.add(factory.arg(refl(contextData, argumentProposition), true));
    args.add(factory.arg(explicit.getLast(), true));
    ArendRef lemma = wandSelection.persistent()
        ? evidence == null ? pmSpecializeIntuitionistic
            : pmSpecializeIntoWandIntuitionistic
        : evidence == null ? pmSpecialize : pmSpecializeIntoWand;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression specializeForall(
      ExpressionTypechecker typechecker, ContextData contextData,
      List<ConcreteExpression> explicit) {
    if (explicit.size() != 4 && explicit.size() != 5) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Universal iSpecialize expects a hypothesis, witness, result name, optional PMIntoForall evidence, and continuation",
          contextData.getMarker()));
      return null;
    }
    String sourceName = stringArgument(typechecker, contextData, 0);
    String resultName = stringArgument(typechecker, contextData, 2);
    if (sourceName == null || resultName == null) return null;
    if (resultName.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iSpecialize result name cannot be empty", contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, sourceName);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Universal iSpecialize currently expects a spatial hypothesis",
          contextData.getMarker()));
      return null;
    }
    if (!resultName.equals(sourceName)
        && environmentContainsName(typechecker, resolved.environment(), resultName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "A proof-mode hypothesis named '" + resultName + "' already exists",
          contextData.getMarker()));
      return null;
    }

    ClassEvidence evidence = explicit.size() == 5
        ? classEvidence(typechecker, contextData, explicit.get(3),
            pmIntoForall, "PMIntoForall") : null;
    if (explicit.size() == 5 && evidence == null) return null;
    CoreExpression source = weakHead(typechecker,
        resolved.selection().proposition());
    CoreFunCallExpression forall = source instanceof CoreFunCallExpression call
        && call.getDefinition() == mkProperForall
        && call.getDefCallArguments().size() >= 3 ? call : null;
    if (evidence == null && forall == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Universal iSpecialize expected a forall hypothesis or PMIntoForall evidence",
          contextData.getMarker()));
      return null;
    }
    CoreExpression carrier = evidence == null
        ? forall.getDefCallArguments().get(forall.getDefCallArguments().size() - 2)
        : classField(evidence, "A");
    CoreExpression family = evidence == null
        ? forall.getDefCallArguments().getLast() : classField(evidence, "Phi");
    if (carrier == null || family == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect universal-hypothesis evidence",
          contextData.getMarker()));
      return null;
    }

    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, resultName), true));
    args.add(factory.arg(factory.core(carrier.computeTyped()), false));
    args.add(factory.arg(factory.core(family.computeTyped()), false));
    args.add(factory.arg(explicit.get(1), true));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(evidence == null
        ? refl(contextData, source) : evidence.term(), true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmSpecializeForall : pmSpecializeIntoForall), args),
        contextData.getExpectedType());
  }
}
