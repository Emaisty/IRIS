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
import java.util.List;

final class WpPuresMeta extends ExactMeta {
  @Dependency(name = "pm_ent_apply")
  private ArendRef pmEntApply;
  @Dependency(name = "pm_wp")
  private CoreFunctionDefinition pmWp;
  @Dependency(name = "pure_head_eval")
  private CoreFunctionDefinition pureHeadEval;
  @Dependency(name = "wp_lam_expr")
  private ArendRef wpLamExpr;
  @Dependency(name = "wp_rec_expr")
  private ArendRef wpRecExpr;
  @Dependency(name = "wp_lam_beta")
  private ArendRef wpLamBeta;
  @Dependency(name = "wp_rec_beta")
  private ArendRef wpRecBeta;
  @Dependency(name = "pm_wp_if_true")
  private ArendRef wpIfTrue;
  @Dependency(name = "pm_wp_if_false")
  private ArendRef wpIfFalse;
  @Dependency(name = "wp_pair_values")
  private ArendRef wpPairValues;
  @Dependency(name = "wp_fst_pair")
  private ArendRef wpFstPair;
  @Dependency(name = "wp_snd_pair")
  private ArendRef wpSndPair;

  private CoreExpression constructorForm(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = dereference(typechecker, expression);
    return result instanceof CoreConCallExpression ? result
        : dereference(typechecker, result.normalize(NormalizationMode.NF));
  }

  private @Nullable CoreConCallExpression constructor(ExpressionTypechecker typechecker,
      CoreExpression expression, String name) {
    CoreExpression result = constructorForm(typechecker, expression);
    return result instanceof CoreConCallExpression call
        && call.getDefinition().getName().equals(name) ? call : null;
  }

  private List<ConcreteArgument> theoremPrefix(ContextData contextData,
      CoreExpression iris, CoreExpression mask) {
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(iris.computeTyped()), true));
    args.add(factory.arg(factory.core(mask.computeTyped()), true));
    return args;
  }

  private @Nullable ConcreteExpression theorem(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression iris, CoreExpression mask,
      CoreExpression expression, CoreExpression post) {
    var factory = contextData.getFactory();
    CoreExpression outerExpression = constructorForm(typechecker, expression);
    if (!(outerExpression instanceof CoreConCallExpression outer)) return null;
    var fields = outer.getDefCallArguments();
    var args = theoremPrefix(contextData, iris, mask);
    ArendRef rule;
    switch (outer.getDefinition().getName()) {
      case "Lam" -> {
        if (fields.size() < 2) return null;
        rule = wpLamExpr;
        args.add(factory.arg(factory.core(fields.get(fields.size() - 2).computeTyped()), true));
        args.add(factory.arg(factory.core(fields.getLast().computeTyped()), true));
      }
      case "Rec" -> {
        if (fields.size() < 3) return null;
        rule = wpRecExpr;
        args.add(factory.arg(factory.core(fields.get(fields.size() - 3).computeTyped()), true));
        args.add(factory.arg(factory.core(fields.get(fields.size() - 2).computeTyped()), true));
        args.add(factory.arg(factory.core(fields.getLast().computeTyped()), true));
      }
      case "App" -> {
        if (fields.size() < 2) return null;
        CoreConCallExpression functionExpr = constructor(typechecker,
            fields.get(fields.size() - 2), "Val");
        CoreConCallExpression argumentExpr = constructor(typechecker, fields.getLast(), "Val");
        if (functionExpr == null || argumentExpr == null) return null;
        CoreExpression function = constructorForm(typechecker,
            functionExpr.getDefCallArguments().getLast());
        CoreExpression argument = argumentExpr.getDefCallArguments().getLast();
        if (!(function instanceof CoreConCallExpression functionCall)) return null;
        var functionFields = functionCall.getDefCallArguments();
        if (functionCall.getDefinition().getName().equals("LamV")
            && functionFields.size() >= 2) {
          rule = wpLamBeta;
          args.add(factory.arg(factory.core(
              functionFields.get(functionFields.size() - 2).computeTyped()), true));
          args.add(factory.arg(factory.core(functionFields.getLast().computeTyped()), true));
        } else if (functionCall.getDefinition().getName().equals("RecV")
            && functionFields.size() >= 3) {
          rule = wpRecBeta;
          args.add(factory.arg(factory.core(
              functionFields.get(functionFields.size() - 3).computeTyped()), true));
          args.add(factory.arg(factory.core(
              functionFields.get(functionFields.size() - 2).computeTyped()), true));
          args.add(factory.arg(factory.core(functionFields.getLast().computeTyped()), true));
        } else return null;
        args.add(factory.arg(factory.core(argument.computeTyped()), true));
      }
      case "If" -> {
        if (fields.size() < 3) return null;
        CoreConCallExpression conditionExpr = constructor(typechecker,
            fields.get(fields.size() - 3), "Val");
        if (conditionExpr == null) return null;
        CoreConCallExpression litV = constructor(typechecker,
            conditionExpr.getDefCallArguments().getLast(), "LitV");
        if (litV == null) return null;
        CoreConCallExpression litBool = constructor(typechecker,
            litV.getDefCallArguments().getLast(), "LitBool");
        if (litBool == null) return null;
        CoreExpression bool = constructorForm(typechecker,
            litBool.getDefCallArguments().getLast());
        if (!(bool instanceof CoreConCallExpression boolCall)) return null;
        rule = switch (boolCall.getDefinition().getName()) {
          case "true" -> wpIfTrue;
          case "false" -> wpIfFalse;
          default -> null;
        };
        if (rule == null) return null;
        args.add(factory.arg(factory.core(fields.get(fields.size() - 2).computeTyped()), true));
        args.add(factory.arg(factory.core(fields.getLast().computeTyped()), true));
      }
      case "Pair" -> {
        if (fields.size() < 2) return null;
        CoreConCallExpression left = constructor(typechecker,
            fields.get(fields.size() - 2), "Val");
        CoreConCallExpression right = constructor(typechecker, fields.getLast(), "Val");
        if (left == null || right == null) return null;
        rule = wpPairValues;
        args.add(factory.arg(factory.core(left.getDefCallArguments().getLast().computeTyped()), true));
        args.add(factory.arg(factory.core(right.getDefCallArguments().getLast().computeTyped()), true));
      }
      case "Fst", "Snd" -> {
        if (fields.isEmpty()) return null;
        CoreConCallExpression valueExpr = constructor(typechecker, fields.getLast(), "Val");
        if (valueExpr == null) return null;
        CoreConCallExpression pair = constructor(typechecker,
            valueExpr.getDefCallArguments().getLast(), "PairV");
        if (pair == null || pair.getDefCallArguments().size() < 2) return null;
        rule = outer.getDefinition().getName().equals("Fst") ? wpFstPair : wpSndPair;
        args.add(factory.arg(factory.core(
            pair.getDefCallArguments().get(pair.getDefCallArguments().size() - 2).computeTyped()), true));
        args.add(factory.arg(factory.core(pair.getDefCallArguments().getLast().computeTyped()), true));
      }
      default -> { return null; }
    }
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    return factory.app(factory.ref(rule), args);
  }

  private @Nullable CoreExpression evaluate(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression expression) {
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.core(expression.computeTyped()), true));
    TypedExpression evaluated = typechecker.typecheck(
        factory.app(factory.ref(pureHeadEval.getRef()), args), null);
    if (evaluated == null) return null;
    CoreExpression result = constructorForm(typechecker, evaluated.getExpression());
    if (!(result instanceof CoreConCallExpression just)
        || !just.getDefinition().getName().equals("just")
        || just.getDefCallArguments().isEmpty()) return null;
    return just.getDefCallArguments().getLast();
  }

  private ConcreteExpression wp(ContextData contextData, CoreExpression iris,
      CoreExpression mask, CoreExpression expression, CoreExpression post) {
    var factory = contextData.getFactory();
    var args = theoremPrefix(contextData, iris, mask);
    args.add(factory.arg(factory.core(expression.computeTyped()), true));
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    return factory.app(factory.ref(pmWp.getRef()), args);
  }

  private ConcreteExpression chain(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression environment, CoreExpression iris,
      CoreExpression mask, CoreExpression expression, CoreExpression post,
      ConcreteExpression continuation, int depth) {
    if (depth >= 64) return continuation;
    ConcreteExpression theorem = theorem(typechecker, contextData, iris, mask,
        expression, post);
    if (theorem == null) return continuation;
    CoreExpression result = evaluate(typechecker, contextData, expression);
    if (result == null) return continuation;
    ConcreteExpression inner = chain(typechecker, contextData, environment, iris,
        mask, result, post, continuation, depth + 1);
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(environment.computeTyped()), false));
    args.add(factory.arg(wp(contextData, iris, mask, result, post), false));
    args.add(factory.arg(wp(contextData, iris, mask, expression, post), false));
    args.add(factory.arg(theorem, true));
    args.add(factory.arg(inner, true));
    return factory.app(factory.ref(pmEntApply), args);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    if (!(target instanceof CoreFunCallExpression wpCall)
        || !(wpCall.getDefinition().getName().equals("wp")
          || wpCall.getDefinition().getName().equals("pm_wp"))
        || wpCall.getDefCallArguments().size() < 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_pures requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    var wpArgs = wpCall.getDefCallArguments();
    CoreExpression iris = wpArgs.get(wpArgs.size() - 4);
    CoreExpression mask = wpArgs.get(wpArgs.size() - 3);
    CoreExpression expression = constructorForm(typechecker,
        wpArgs.get(wpArgs.size() - 2));
    CoreExpression post = wpArgs.getLast();
    ConcreteExpression proof = chain(typechecker, contextData, goal.environment(),
        iris, mask, expression, post, explicitArguments(contextData).getFirst(), 0);
    return typechecker.typecheck(proof, contextData.getExpectedType());
  }
}
