package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;

final class ClearMeta extends ExactMeta {
  @Dependency(name = "pm_clear_spatial")
  private ArendRef pmClearSpatial;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new org.arend.ext.error.TypecheckingError(
          "Clearing intuitionistic hypotheses is not implemented yet", contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(pmClearSpatial), args),
        contextData.getExpectedType());
  }
}
