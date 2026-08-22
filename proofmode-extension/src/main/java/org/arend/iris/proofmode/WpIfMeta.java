package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;

final class WpIfMeta extends ExactMeta {
  @Dependency(name = "pm_wp")
  private CoreFunctionDefinition pmWp;
  @Dependency(name = "pm_wp_if_true")
  private ArendRef wpIfTrue;
  @Dependency(name = "pm_wp_if_false")
  private ArendRef wpIfFalse;
  @Dependency(name = "pm_ent_apply")
  private ArendRef pmEntApply;

  private @Nullable Boolean booleanValue(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression current = constructorForm(typechecker, expression);
    if (!(current instanceof CoreConCallExpression valCall)
        || !valCall.getDefinition().getName().equals("Val")
        || valCall.getDefCallArguments().isEmpty()) return null;
    current = constructorForm(typechecker, valCall.getDefCallArguments().getLast());
    if (!(current instanceof CoreConCallExpression litV)
        || !litV.getDefinition().getName().equals("LitV")
        || litV.getDefCallArguments().isEmpty()) return null;
    current = constructorForm(typechecker, litV.getDefCallArguments().getLast());
    if (!(current instanceof CoreConCallExpression litBool)
        || !litBool.getDefinition().getName().equals("LitBool")
        || litBool.getDefCallArguments().isEmpty()) return null;
    current = constructorForm(typechecker, litBool.getDefCallArguments().getLast());
    if (!(current instanceof CoreConCallExpression bool)) return null;
    return switch (bool.getDefinition().getName()) {
      case "true" -> true;
      case "false" -> false;
      default -> null;
    };
  }

  private CoreExpression constructorForm(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = dereference(typechecker, expression);
    return result instanceof CoreConCallExpression ? result
        : dereference(typechecker, result.normalize(NormalizationMode.WHNF));
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = dereference(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression wpCall)
        || !(wpCall.getDefinition().getName().equals("wp")
          || wpCall.getDefinition().getName().equals("pm_wp"))
        || wpCall.getDefCallArguments().size() < 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_if requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    var wpArgs = wpCall.getDefCallArguments();
    CoreExpression iris = wpArgs.get(wpArgs.size() - 4);
    CoreExpression mask = wpArgs.get(wpArgs.size() - 3);
    CoreExpression expression = dereference(typechecker, wpArgs.get(wpArgs.size() - 2));
    CoreExpression post = wpArgs.getLast();
    if (!(expression instanceof CoreConCallExpression ifCall)
        || !ifCall.getDefinition().getName().equals("If")
        || ifCall.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_if requires an if-expression", contextData.getMarker()));
      return null;
    }
    var ifArgs = ifCall.getDefCallArguments();
    CoreExpression condition = ifArgs.get(ifArgs.size() - 3);
    CoreExpression thenBranch = ifArgs.get(ifArgs.size() - 2);
    CoreExpression elseBranch = ifArgs.getLast();
    Boolean value = booleanValue(typechecker, condition);
    if (value == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_if requires a boolean value condition", contextData.getMarker()));
      return null;
    }
    CoreExpression chosen = value ? thenBranch : elseBranch;
    var factory = contextData.getFactory();
    var preArgs = new ArrayList<ConcreteArgument>();
    preArgs.add(factory.arg(factory.hole(), false));
    preArgs.add(factory.arg(factory.hole(), false));
    preArgs.add(factory.arg(factory.core(iris.computeTyped()), true));
    preArgs.add(factory.arg(factory.core(mask.computeTyped()), true));
    preArgs.add(factory.arg(factory.core(chosen.computeTyped()), true));
    preArgs.add(factory.arg(factory.core(post.computeTyped()), true));
    ConcreteExpression precondition = factory.app(factory.ref(pmWp.getRef()), preArgs);

    var theoremArgs = new ArrayList<ConcreteArgument>();
    theoremArgs.add(factory.arg(factory.hole(), false));
    theoremArgs.add(factory.arg(factory.hole(), false));
    theoremArgs.add(factory.arg(factory.core(iris.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(mask.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(thenBranch.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(elseBranch.computeTyped()), true));
    theoremArgs.add(factory.arg(factory.core(post.computeTyped()), true));
    ConcreteExpression theorem = factory.app(factory.ref(value ? wpIfTrue : wpIfFalse),
        theoremArgs);

    var applyArgs = new ArrayList<ConcreteArgument>();
    applyArgs.add(factory.arg(factory.hole(), false));
    applyArgs.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    applyArgs.add(factory.arg(precondition, false));
    applyArgs.add(factory.arg(factory.core(target.computeTyped()), false));
    applyArgs.add(factory.arg(theorem, true));
    applyArgs.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(pmEntApply), applyArgs),
        contextData.getExpectedType());
  }
}
