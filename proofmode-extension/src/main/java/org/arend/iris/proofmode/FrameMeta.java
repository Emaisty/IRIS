package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
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

final class FrameMeta extends ExactMeta {
  @Dependency(name = "pm_frame_spatial")
  private ArendRef pmFrameSpatial;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 2)) return null;
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Framing intuitionistic hypotheses is not implemented yet", contextData.getMarker()));
      return null;
    }
    CoreExpression target = weakHead(typechecker, resolved.target());
    if (!(target instanceof CoreFunCallExpression sep)
        || !sep.getDefinition().getName().equals(mkProperSep.getName())
        || sep.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iFrame expects a separating-conjunction goal", contextData.getMarker()));
      return null;
    }
    CoreExpression residual = sep.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(factory.core(residual.computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(pmFrameSpatial), args),
        contextData.getExpectedType());
  }
}
