package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
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

  @Dependency(name = "pm_frame_intuitionistic")
  private ArendRef pmFrameIntuitionistic;

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
    var factory = contextData.getFactory();
    CoreExpression target = weakHead(typechecker, resolved.target());
    ConcreteExpression residual = target instanceof CoreFunCallExpression sep
        && sep.getDefinition() == mkProperSep
        && sep.getDefCallArguments().size() >= 3
        ? factory.core(sep.getDefCallArguments().getLast().computeTyped())
        : factory.hole();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(residual, false));
    args.add(factory.arg(explicitArguments(contextData).get(1), true));
    return typechecker.typecheck(factory.app(factory.ref(resolved.persistent()
            ? pmFrameIntuitionistic : pmFrameSpatial), args),
        contextData.getExpectedType());
  }
}
