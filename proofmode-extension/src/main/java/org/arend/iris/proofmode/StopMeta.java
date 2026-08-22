package org.arend.iris.proofmode;

import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

final class StopMeta extends ProofModeMeta {
  @Dependency(name = "pm_stop")
  private ArendRef pmStop;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    return typechecker.typecheck(explicitArguments(contextData).getFirst(),
        contextData.getExpectedType());
  }
}
