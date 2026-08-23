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

final class ApplyWandMeta extends ExactMeta {
  @Dependency(name = "pm_apply_wand")
  private ArendRef pmApplyWand;

  @Dependency(name = "pm_apply_wand_intuitionistic")
  private ArendRef pmApplyWandIntuitionistic;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperWand")
  private CoreFunctionDefinition mkProperWand;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (!(proposition instanceof CoreFunCallExpression wand)
        || !wand.getDefinition().getName().equals(mkProperWand.getName())
        || wand.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iApply expected a wand hypothesis", contextData.getMarker()));
      return null;
    }
    CoreExpression domain = wand.getDefCallArguments().get(wand.getDefCallArguments().size() - 2);
    CoreExpression codomain = wand.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression refl = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(factory.core(domain.computeTyped()), false));
    args.add(factory.arg(factory.core(codomain.computeTyped()), false));
    args.add(factory.arg(refl, true));
    args.add(factory.arg(explicitArguments(contextData).get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(resolved.persistent()
            ? pmApplyWandIntuitionistic : pmApplyWand), args),
        contextData.getExpectedType());
  }
}
