package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
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
import java.util.Set;

final class WpSmartApplyMeta extends WpBindMeta {
  @Dependency(name = "pm_wp_smart_apply")
  private ArendRef pmWpSmartApply;
  @Dependency(name = "pm_wp_smart_bind_item")
  private ArendRef pmWpSmartBindItem;
  @Dependency(name = "pm_wp_smart_let")
  private ArendRef pmWpSmartLet;

  private record WpData(CoreExpression iris, CoreExpression mask,
      CoreExpression expression, CoreExpression postcondition) {}

  private record LetFocus(CoreExpression name, CoreExpression body,
      CoreExpression expression) {}

  private @Nullable LetFocus letFocus(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression form = constructorForm(typechecker, expression);
    if (!(form instanceof CoreConCallExpression app)
        || !app.getDefinition().getName().equals("App")
        || app.getDefCallArguments().size() < 2) return null;
    var appArgs = app.getDefCallArguments();
    CoreExpression function = appArgs.get(appArgs.size() - 2);
    CoreExpression argument = appArgs.getLast();
    CoreExpression functionForm = constructorForm(typechecker, function);
    if (!(functionForm instanceof CoreConCallExpression lam)
        || !lam.getDefinition().getName().equals("Lam")
        || lam.getDefCallArguments().size() < 2) return null;
    var lamArgs = lam.getDefCallArguments();
    return new LetFocus(lamArgs.get(lamArgs.size() - 2), lamArgs.getLast(),
        argument);
  }

  private @Nullable WpData wpData(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression target = dereference(typechecker, expression)
        .unfold(Set.of(), null, true, false);
    for (int i = 0; i < 4; i++) {
      target = dereference(typechecker, target);
      if (target instanceof CoreFunCallExpression call) {
        String name = call.getDefinition().getName();
        if ((name.equals("wp") || name.equals("pm_wp"))
            && call.getDefCallArguments().size() >= 4) {
          var args = call.getDefCallArguments();
          return new WpData(args.get(args.size() - 4),
              args.get(args.size() - 3), args.get(args.size() - 2),
              args.getLast());
        }
        target = target.unfold(Set.of(call.getDefinition()), null, true, false);
      } else {
        target = target.normalize(NormalizationMode.WHNF);
      }
    }
    return null;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 3)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    WpData target = wpData(typechecker, goal.target());
    if (target == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_smart_apply requires a weakest-precondition goal",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var explicit = explicitArguments(contextData);
    TypedExpression rule = typechecker.typecheck(explicit.get(0), null);
    if (rule == null) return null;
    CoreExpression ruleType = weakHead(typechecker, rule.getType());
    if (!(ruleType instanceof CoreFunCallExpression entailment)
        || !entailment.getDefinition().getName().equals("properUPred_ent")
        || entailment.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_smart_apply expects an entailment theorem",
          contextData.getMarker()));
      return null;
    }
    var entailmentArgs = entailment.getDefCallArguments();
    CoreExpression source = entailmentArgs.get(entailmentArgs.size() - 2);
    WpData applied = wpData(typechecker, entailmentArgs.getLast());
    if (applied == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_smart_apply expects a weakest-precondition conclusion",
          contextData.getMarker()));
      return null;
    }

    boolean direct = dereference(typechecker, target.expression()).compare(
        dereference(typechecker, applied.expression()), CMP.EQ);
    LetFocus let = direct ? null : letFocus(typechecker, target.expression());
    boolean letMatch = let != null
        && dereference(typechecker, let.expression()).compare(
          dereference(typechecker, applied.expression()), CMP.EQ);
    Focus focused = direct || letMatch ? null
        : focus(typechecker, contextData, target.expression());
    if (!direct && !letMatch && (focused == null
        || !dereference(typechecker, focused.expression()).compare(
          dereference(typechecker, applied.expression()), CMP.EQ))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_smart_apply could not match the rule to the goal expression",
          contextData.getMarker()));
      return null;
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(target.iris().computeTyped()), true));
    args.add(factory.arg(factory.core(target.mask().computeTyped()), true));
    if (letMatch) {
      args.add(factory.arg(factory.core(let.name().computeTyped()), true));
    } else if (!direct) {
      args.add(factory.arg(focused.item(), true));
    }
    args.add(factory.arg(factory.core(applied.expression().computeTyped()), true));
    if (letMatch) {
      args.add(factory.arg(factory.core(let.body().computeTyped()), true));
    }
    args.add(factory.arg(factory.core(applied.postcondition().computeTyped()), true));
    args.add(factory.arg(factory.core(target.postcondition().computeTyped()), true));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), true));
    args.add(factory.arg(factory.core(source.computeTyped()), true));
    args.add(factory.arg(factory.core(rule), true));
    args.add(factory.arg(explicit.get(1), true));
    args.add(factory.arg(explicit.get(2), true));
    ArendRef lemma = direct ? pmWpSmartApply
        : letMatch ? pmWpSmartLet : pmWpSmartBindItem;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }
}
