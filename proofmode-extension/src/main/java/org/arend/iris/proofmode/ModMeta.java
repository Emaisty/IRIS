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

final class ModMeta extends ExactMeta {
  @Dependency(name = "PMIntoUpdate")
  private CoreClassDefinition pmIntoUpdate;
  @Dependency(name = "pm_mod")
  private ArendRef pmMod;
  @Dependency(name = "pm_mod_into_update")
  private ArendRef pmModIntoUpdate;
  @Dependency(name = "pm_fupd")
  private ArendRef pmFUpd;
  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;
  @Dependency(name = "mkProperBUpd")
  private CoreFunctionDefinition mkProperBUpd;
  @Dependency(name = "mkProperFUpd")
  private CoreFunctionDefinition mkProperFUpd;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    if (explicit.size() < 3 || explicit.size() > 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected an update name, result name, optional PMIntoUpdate evidence, and continuation",
          contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    String introduced = stringArgument(typechecker, contextData, 1);
    if (requested == null || introduced == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod currently consumes a spatial update", contextData.getMarker()));
      return null;
    }
    if (!requested.equals(introduced)
        && environmentContainsName(typechecker, resolved.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Proof-mode hypothesis '" + introduced + "' already exists",
          contextData.getMarker()));
      return null;
    }
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    ClassEvidence evidence = explicit.size() == 4
        ? classEvidence(typechecker, contextData, explicit.get(2),
            pmIntoUpdate, "PMIntoUpdate") : null;
    if (explicit.size() == 4 && evidence == null) return null;
    CoreFunCallExpression update = proposition instanceof CoreFunCallExpression call
        ? call : null;
    if (evidence == null && update == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod expected an update hypothesis", contextData.getMarker()));
      return null;
    }
    CoreExpression target = weakHead(typechecker, resolved.target());
    if (!(target instanceof CoreFunCallExpression targetUpdate)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod requires an update goal", contextData.getMarker()));
      return null;
    }

    if (evidence == null && update.getDefinition() == mkProperFUpd
        && targetUpdate.getDefinition() == mkProperFUpd
        && update.getDefCallArguments().size() >= 4
        && targetUpdate.getDefCallArguments().size() >= 4) {
      return invokeFancy(typechecker, contextData, resolved, proposition,
          update, targetUpdate, introduced);
    }
    if (evidence == null && (update.getDefinition() != mkProperBUpd
        || update.getDefCallArguments().isEmpty())) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod expected a basic or fancy update hypothesis",
          contextData.getMarker()));
      return null;
    }
    if (targetUpdate.getDefinition() != mkProperBUpd
        || targetUpdate.getDefCallArguments().isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod requires a matching basic-update goal",
          contextData.getMarker()));
      return null;
    }
    CoreExpression body = evidence == null
        ? update.getDefCallArguments().getLast() : classField(evidence, "Q");
    if (body == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMIntoUpdate evidence", contextData.getMarker()));
      return null;
    }
    CoreExpression targetBody = targetUpdate.getDefCallArguments().getLast();
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
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(targetBody.computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmMod : pmModIntoUpdate), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression invokeFancy(
      @NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData,
      @NotNull ResolvedSelection resolved,
      @NotNull CoreExpression proposition,
      @NotNull CoreFunCallExpression update,
      @NotNull CoreFunCallExpression targetUpdate,
      @NotNull String introduced) {
    var updateArgs = update.getDefCallArguments();
    var targetArgs = targetUpdate.getDefCallArguments();
    CoreExpression wsat = updateArgs.get(updateArgs.size() - 4);
    CoreExpression sourceMask = updateArgs.get(updateArgs.size() - 3);
    CoreExpression middleMask = updateArgs.get(updateArgs.size() - 2);
    CoreExpression body = updateArgs.getLast();
    CoreExpression targetMask = targetArgs.get(targetArgs.size() - 2);
    CoreExpression targetBody = targetArgs.getLast();

    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression refl = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(wsat.computeTyped()), true));
    args.add(factory.arg(factory.core(sourceMask.computeTyped()), true));
    args.add(factory.arg(factory.core(middleMask.computeTyped()), true));
    args.add(factory.arg(factory.core(targetMask.computeTyped()), true));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(targetBody.computeTyped()), false));
    args.add(factory.arg(refl, true));
    args.add(factory.arg(explicitArguments(contextData).get(2), true));
    return typechecker.typecheck(factory.app(factory.ref(pmFUpd), args),
        contextData.getExpectedType());
  }
}
