package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteStringExpression;
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

final class RewriteMeta extends ExactMeta {
  @Dependency(name = "pm_rewrite")
  private ArendRef pmRewrite;

  @Dependency(name = "pm_rewrite_intuitionistic")
  private ArendRef pmRewriteIntuitionistic;

  @Dependency(name = "pm_transport")
  private ArendRef pmTransport;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperInternalEq")
  private CoreFunctionDefinition mkProperInternalEq;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    var explicit = explicitArguments(contextData);
    if (explicit.size() != 2 && explicit.size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iRewrite expects an equality, an optional goal family, and a continuation",
          contextData.getMarker()));
      return null;
    }
    if (!(explicit.getFirst() instanceof ConcreteStringExpression)) {
      GoalData goal = resolveGoal(typechecker, contextData);
      if (goal == null) return null;
      var factory = contextData.getFactory();
      var args = new ArrayList<ConcreteArgument>();
      args.add(factory.arg(factory.hole(), false));
      args.add(factory.arg(factory.hole(), false));
      args.add(factory.arg(factory.hole(), false));
      args.add(factory.arg(explicit.getFirst(), true));
      args.add(factory.arg(factory.hole(), false));
      args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
      args.add(factory.arg(explicit.size() == 3 ? explicit.get(1) : factory.hole(), false));
      args.add(factory.arg(explicit.getLast(), true));
      return typechecker.typecheck(factory.app(factory.ref(pmTransport), args),
          contextData.getExpectedType());
    }
    if (explicit.size() != 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Internal-equality iRewrite expects a hypothesis name and a continuation",
          contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (!(proposition instanceof CoreFunCallExpression equality)
        || equality.getDefinition() != mkProperInternalEq
        || equality.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iRewrite expected an internal equality hypothesis",
          contextData.getMarker()));
      return null;
    }
    CoreExpression left = equality.getDefCallArguments().get(
        equality.getDefCallArguments().size() - 2);
    CoreExpression right = equality.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression refl = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(factory.core(left.computeTyped()), false));
    args.add(factory.arg(factory.core(right.computeTyped()), false));
    args.add(factory.arg(refl, true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(resolved.persistent()
            ? pmRewriteIntuitionistic : pmRewrite), args),
        contextData.getExpectedType());
  }
}
