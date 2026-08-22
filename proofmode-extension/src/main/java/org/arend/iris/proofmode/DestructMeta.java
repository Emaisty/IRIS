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

final class DestructMeta extends ExactMeta {
  @Dependency(name = "pm_destruct_sep")
  private ArendRef pmDestructSep;

  @Dependency(name = "pm_destruct_persistent")
  private ArendRef pmDestructPersistent;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Dependency(name = "mkProperPersistently")
  private CoreFunctionDefinition mkProperPersistently;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 3)) return null;
    String requested = stringArgument(typechecker, contextData, 0);
    String pattern = stringArgument(typechecker, contextData, 1);
    if (requested == null || pattern == null) return null;
    String trimmedPattern = pattern.trim();
    if (trimmedPattern.startsWith("#")) {
      return destructPersistent(typechecker, contextData, requested,
          trimmedPattern.substring(1).trim());
    }
    String[] names = trimmedPattern.split("\\s+");
    if (names.length != 2 || names[0].isEmpty() || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "This iDestruct form expects exactly two names", contextData.getMarker()));
      return null;
    }
    if (names[0].equals(names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + names[0] + "'",
          contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Destructing intuitionistic hypotheses is not implemented yet", contextData.getMarker()));
      return null;
    }
    if ((!names[0].equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), names[0]))
        || (!names[1].equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), names[1]))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iDestruct would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (!(proposition instanceof CoreFunCallExpression sep)
        || !sep.getDefinition().getName().equals(mkProperSep.getName())
        || sep.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iDestruct expected a separating conjunction", contextData.getMarker()));
      return null;
    }
    CoreExpression left = sep.getDefCallArguments().get(sep.getDefCallArguments().size() - 2);
    CoreExpression right = sep.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression split = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, names[0]), true));
    args.add(factory.arg(name(contextData, names[1]), true));
    args.add(factory.arg(factory.core(left.computeTyped()), false));
    args.add(factory.arg(factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(split, true));
    args.add(factory.arg(explicitArguments(contextData).get(2), true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructSep), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructPersistent(
      ExpressionTypechecker typechecker, ContextData contextData,
      String requested, String introduced) {
    if (introduced.isEmpty() || introduced.contains(" ")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Persistent iDestruct expects exactly one name after '#'",
          contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "The hypothesis '" + requested + "' is already intuitionistic",
          contextData.getMarker()));
      return null;
    }
    if (!introduced.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + introduced + "'",
          contextData.getMarker()));
      return null;
    }
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (!(proposition instanceof CoreFunCallExpression persistently)
        || !persistently.getDefinition().getName().equals(mkProperPersistently.getName())
        || persistently.getDefCallArguments().size() < 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Persistent iDestruct expected a persistently proposition",
          contextData.getMarker()));
      return null;
    }
    CoreExpression body = persistently.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression persistent = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(persistent, true));
    args.add(factory.arg(explicitArguments(contextData).get(2), true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructPersistent), args),
        contextData.getExpectedType());
  }
}
