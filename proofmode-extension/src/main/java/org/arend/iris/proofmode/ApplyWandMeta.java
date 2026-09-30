package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
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
import java.util.List;

final class ApplyWandMeta extends ExactMeta {
  @Dependency(name = "PMIntoWand")
  private CoreClassDefinition pmIntoWand;

  @Dependency(name = "pm_apply_wand")
  private ArendRef pmApplyWand;

  @Dependency(name = "pm_apply_wand_intuitionistic")
  private ArendRef pmApplyWandIntuitionistic;
  @Dependency(name = "pm_apply_into_wand")
  private ArendRef pmApplyIntoWand;
  @Dependency(name = "pm_apply_into_wand_intuitionistic")
  private ArendRef pmApplyIntoWandIntuitionistic;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperWand")
  private CoreFunctionDefinition mkProperWand;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    if (explicit.size() < 2 || explicit.size() > 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected a wand name, optional PMIntoWand evidence, and a continuation",
          contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    ClassEvidence evidence = explicit.size() == 3
        ? classEvidence(typechecker, contextData, explicit.get(1),
            pmIntoWand, "PMIntoWand") : null;
    if (explicit.size() == 3 && evidence == null) return null;
    CoreFunCallExpression wand = proposition instanceof CoreFunCallExpression call
        && call.getDefinition().getName().equals(mkProperWand.getName())
        && call.getDefCallArguments().size() >= 3 ? call : null;
    if (evidence == null && wand == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iApply expected a wand hypothesis", contextData.getMarker()));
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
    var factory = contextData.getFactory();
    ConcreteExpression into;
    if (evidence == null) {
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      into = factory.app(factory.ref(entailmentRefl), reflArgs);
    } else {
      into = evidence.term();
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(factory.core(domain.computeTyped()), false));
    args.add(factory.arg(factory.core(codomain.computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(explicit.getLast(), true));
    ArendRef lemma = resolved.persistent()
        ? evidence == null ? pmApplyWandIntuitionistic : pmApplyIntoWandIntuitionistic
        : evidence == null ? pmApplyWand : pmApplyIntoWand;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }
}
