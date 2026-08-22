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

final class InvMeta extends ExactMeta {
  @Dependency(name = "pm_wp_inv")
  private ArendRef pmWpInv;

  @Dependency(name = "inv")
  private CoreFunctionDefinition invariant;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 5)) return null;
    String invariantName = stringArgument(typechecker, contextData, 0);
    String pattern = stringArgument(typechecker, contextData, 1);
    if (invariantName == null || pattern == null) return null;
    String[] introduced = pattern.trim().isEmpty()
        ? new String[0] : pattern.trim().split("\\s+");
    if (introduced.length != 2 || introduced[0].equals(introduced[1])
        || introduced[0].isEmpty() || introduced[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv expects two distinct names, for example \"HP Hclose\"",
          contextData.getMarker()));
      return null;
    }

    ResolvedSelection resolved = resolveNamed(typechecker, contextData, invariantName);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv currently opens a spatial invariant hypothesis",
          contextData.getMarker()));
      return null;
    }
    for (String name : introduced) {
      if (!name.equals(invariantName)
          && environmentContainsName(typechecker, resolved.environment(), name)) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "A proof-mode hypothesis named '" + name + "' already exists",
            contextData.getMarker()));
        return null;
      }
    }

    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (!(proposition instanceof CoreFunCallExpression invCall)
        || invCall.getDefinition() != invariant
        || invCall.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv expected an invariant hypothesis", contextData.getMarker()));
      return null;
    }
    var invArgs = invCall.getDefCallArguments();
    CoreExpression namespace = invArgs.get(invArgs.size() - 2);
    CoreExpression body = invArgs.getLast();

    CoreExpression target = weakHead(typechecker, resolved.target());
    if (!(target instanceof CoreFunCallExpression wpCall)
        || !(wpCall.getDefinition().getName().equals("wp")
          || wpCall.getDefinition().getName().equals("pm_wp"))
        || wpCall.getDefCallArguments().size() < 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    var wpArgs = wpCall.getDefCallArguments();
    CoreExpression iris = wpArgs.get(wpArgs.size() - 4);
    CoreExpression mask = wpArgs.get(wpArgs.size() - 3);
    CoreExpression expression = wpArgs.get(wpArgs.size() - 2);
    CoreExpression post = wpArgs.getLast();

    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression refl = factory.app(factory.ref(entailmentRefl), reflArgs);

    var arguments = explicitArguments(contextData);
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(iris.computeTyped()), true));
    args.add(factory.arg(factory.core(mask.computeTyped()), true));
    args.add(factory.arg(factory.core(namespace.computeTyped()), true));
    args.add(factory.arg(factory.core(body.computeTyped()), true));
    args.add(factory.arg(factory.core(expression.computeTyped()), true));
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    args.add(factory.arg(arguments.get(2), true));
    args.add(factory.arg(arguments.get(3), true));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced[0]), true));
    args.add(factory.arg(name(contextData, introduced[1]), true));
    args.add(factory.arg(refl, true));
    args.add(factory.arg(arguments.get(4), true));
    return typechecker.typecheck(factory.app(factory.ref(pmWpInv), args),
        contextData.getExpectedType());
  }
}
