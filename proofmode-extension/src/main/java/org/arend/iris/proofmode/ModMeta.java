package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
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

final class ModMeta extends ExactMeta {
  @Dependency(name = "pm_mod")
  private ArendRef pmMod;
  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;
  @Dependency(name = "mkProperBUpd")
  private CoreFunctionDefinition mkProperBUpd;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 3)) return null;
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
    if (!(proposition instanceof CoreFunCallExpression update)
        || update.getDefinition() != mkProperBUpd
        || update.getDefCallArguments().isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod expected a basic-update hypothesis", contextData.getMarker()));
      return null;
    }
    CoreExpression body = update.getDefCallArguments().getLast();
    CoreExpression target = weakHead(typechecker, resolved.target());
    if (!(target instanceof CoreFunCallExpression targetUpdate)
        || targetUpdate.getDefinition() != mkProperBUpd
        || targetUpdate.getDefCallArguments().isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iMod requires a basic-update goal", contextData.getMarker()));
      return null;
    }
    CoreExpression targetBody = targetUpdate.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression refl = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(targetBody.computeTyped()), false));
    args.add(factory.arg(refl, true));
    args.add(factory.arg(explicitArguments(contextData).get(2), true));
    return typechecker.typecheck(factory.app(factory.ref(pmMod), args),
        contextData.getExpectedType());
  }
}
