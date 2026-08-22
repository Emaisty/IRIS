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

final class RenameMeta extends ExactMeta {
  @Dependency(name = "pm_rename_spatial")
  private ArendRef pmRenameSpatial;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 3)) return null;
    String oldName = stringArgument(typechecker, contextData, 0);
    String newName = stringArgument(typechecker, contextData, 1);
    if (oldName == null || newName == null) return null;
    if (newName.isEmpty()) {
      typechecker.getErrorReporter().report(new org.arend.ext.error.TypecheckingError(
          "Proof-mode hypothesis names cannot be empty", contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, oldName);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new org.arend.ext.error.TypecheckingError(
          "Renaming intuitionistic hypotheses is not implemented yet", contextData.getMarker()));
      return null;
    }
    if (!oldName.equals(newName)
        && environmentContainsName(typechecker, resolved.environment(), newName)) {
      typechecker.getErrorReporter().report(new org.arend.ext.error.TypecheckingError(
          "Proof-mode hypothesis '" + newName + "' already exists",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, newName), true));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).get(2), true));
    return typechecker.typecheck(factory.app(factory.ref(pmRenameSpatial), args),
        contextData.getExpectedType());
  }
}
