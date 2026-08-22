package org.arend.iris.proofmode;

import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

final class UnsupportedMeta extends BaseMetaDefinition {
  private final String name;

  UnsupportedMeta(String name) {
    this.name = name;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    typechecker.getErrorReporter().report(new TypecheckingError(
        "Proof-mode tactic '" + name + "' is not implemented yet", contextData.getMarker()));
    return null;
  }
}
