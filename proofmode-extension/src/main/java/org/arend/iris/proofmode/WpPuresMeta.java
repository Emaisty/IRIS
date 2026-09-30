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
import java.util.Set;

final class WpPuresMeta extends WpBindMeta {
  enum StopAfter { NONE, VALUE, LAM_BETA, REC_BETA }

  private enum StepKind { OTHER, LAM_BETA, REC_BETA }

  private final StopAfter stopAfter;

  WpPuresMeta() {
    this(StopAfter.NONE);
  }

  WpPuresMeta(boolean resumeNestedContexts) {
    this(resumeNestedContexts ? StopAfter.NONE : StopAfter.VALUE);
  }

  WpPuresMeta(StopAfter stopAfter) {
    this.stopAfter = stopAfter;
  }

  @Dependency(name = "pm_ent_apply")
  private ArendRef pmEntApply;
  @Dependency(name = "pm_wp")
  private CoreFunctionDefinition pmWp;
  @Dependency(name = "wp_bind_item")
  private ArendRef wpBindItem;
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
  @Dependency(name = "wp_loc_add")
  private ArendRef wpLocAdd;
  @Dependency(name = "wp_nat_add")
  private ArendRef wpNatAdd;
  @Dependency(name = "pm_wp_value_intro")
  private ArendRef wpValueIntro;

  @Override
  protected CoreExpression constructorForm(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = dereference(typechecker, expression);
    return result instanceof CoreConCallExpression ? result
        : dereference(typechecker, result.normalize(NormalizationMode.WHNF));
  }

  private @Nullable CoreExpression natValue(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreConCallExpression valueExpr = constructor(typechecker, expression, "Val");
    if (valueExpr == null || valueExpr.getDefCallArguments().isEmpty()) return null;
    CoreConCallExpression litV = constructor(typechecker,
        valueExpr.getDefCallArguments().getLast(), "LitV");
    if (litV == null || litV.getDefCallArguments().isEmpty()) return null;
    CoreConCallExpression litInt = constructor(typechecker,
        litV.getDefCallArguments().getLast(), "LitInt");
    if (litInt == null || litInt.getDefCallArguments().isEmpty()) return null;
    CoreConCallExpression positive = constructor(typechecker,
        litInt.getDefCallArguments().getLast(), "pos");
    return positive == null || positive.getDefCallArguments().isEmpty()
        ? null : positive.getDefCallArguments().getLast();
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

  private record Step(ConcreteExpression theorem, StepKind kind) {}

  private @Nullable Step theorem(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression iris, CoreExpression mask,
      CoreExpression expression, CoreExpression post) {
    var factory = contextData.getFactory();
    CoreExpression outerExpression = constructorForm(typechecker, expression);
    List<? extends CoreExpression> fields;
    String outerName;
    if (outerExpression instanceof CoreConCallExpression outer) {
      fields = outer.getDefCallArguments();
      outerName = outer.getDefinition().getName();
    } else if (outerExpression instanceof CoreFunCallExpression outer) {
      fields = outer.getDefCallArguments();
      outerName = outer.getDefinition().getName();
    } else return null;
    var args = theoremPrefix(contextData, iris, mask);
    ArendRef rule;
    StepKind kind = StepKind.OTHER;
    switch (outerName) {
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
          kind = StepKind.LAM_BETA;
          args.add(factory.arg(factory.core(
              functionFields.get(functionFields.size() - 2).computeTyped()), true));
          args.add(factory.arg(factory.core(functionFields.getLast().computeTyped()), true));
        } else if (functionCall.getDefinition().getName().equals("RecV")
            && functionFields.size() >= 3) {
          rule = wpRecBeta;
          kind = StepKind.REC_BETA;
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
        rule = outerName.equals("Fst") ? wpFstPair : wpSndPair;
        args.add(factory.arg(factory.core(
            pair.getDefCallArguments().get(pair.getDefCallArguments().size() - 2).computeTyped()), true));
        args.add(factory.arg(factory.core(pair.getDefCallArguments().getLast().computeTyped()), true));
      }
      case "BinOp", "LocAdd" -> {
        if (fields.size() < (outerName.equals("BinOp") ? 3 : 2)) return null;
        String operationName = "LocAddOp";
        if (outerName.equals("BinOp")) {
          CoreExpression operation = constructorForm(typechecker,
              fields.get(fields.size() - 3));
          if (!(operation instanceof CoreConCallExpression operationCall)) return null;
          operationName = operationCall.getDefinition().getName();
        }
        if (operationName.equals("NatAddOp")) {
          CoreExpression left = natValue(typechecker,
              fields.get(fields.size() - 2));
          CoreExpression right = natValue(typechecker, fields.getLast());
          if (left == null || right == null) return null;
          rule = wpNatAdd;
          args.add(factory.arg(factory.core(left.computeTyped()), true));
          args.add(factory.arg(factory.core(right.computeTyped()), true));
          break;
        }
        if (!operationName.equals("LocAddOp")) return null;
        CoreConCallExpression leftExpr = constructor(typechecker,
            fields.get(fields.size() - 2), "Val");
        CoreConCallExpression rightExpr = constructor(typechecker, fields.getLast(), "Val");
        if (leftExpr == null || rightExpr == null) return null;
        CoreConCallExpression leftLit = constructor(typechecker,
            leftExpr.getDefCallArguments().getLast(), "LitV");
        CoreConCallExpression rightLit = constructor(typechecker,
            rightExpr.getDefCallArguments().getLast(), "LitV");
        if (leftLit == null || rightLit == null) return null;
        CoreConCallExpression location = constructor(typechecker,
            leftLit.getDefCallArguments().getLast(), "LitLoc");
        CoreConCallExpression integer = constructor(typechecker,
            rightLit.getDefCallArguments().getLast(), "LitInt");
        if (location == null || integer == null
            || location.getDefCallArguments().isEmpty()
            || integer.getDefCallArguments().isEmpty()) return null;
        CoreConCallExpression positive = constructor(typechecker,
            integer.getDefCallArguments().getLast(), "pos");
        if (positive == null || positive.getDefCallArguments().isEmpty()) return null;
        rule = wpLocAdd;
        args.add(factory.arg(factory.core(
            location.getDefCallArguments().getLast().computeTyped()), true));
        args.add(factory.arg(factory.core(
            positive.getDefCallArguments().getLast().computeTyped()), true));
      }
      default -> { return null; }
    }
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    return new Step(factory.app(factory.ref(rule), args), kind);
  }

  private boolean stopsAfter(StepKind kind) {
    return stopAfter == StopAfter.LAM_BETA && kind == StepKind.LAM_BETA
        || stopAfter == StopAfter.REC_BETA && kind == StepKind.REC_BETA;
  }

  private @Nullable CoreExpression theoremResult(ExpressionTypechecker typechecker,
      TypedExpression theorem) {
    CoreExpression type = dereference(typechecker, theorem.getType());
    if (!(type instanceof CoreFunCallExpression entailment)
        || !entailment.getDefinition().getName().equals("properUPred_ent")
        || entailment.getDefCallArguments().size() < 3) return null;
    var entailmentArgs = entailment.getDefCallArguments();
    CoreExpression source = weakHead(typechecker,
        entailmentArgs.get(entailmentArgs.size() - 2));
    if (!(source instanceof CoreFunCallExpression wpCall)
        || !(wpCall.getDefinition().getName().equals("wp")
          || wpCall.getDefinition().getName().equals("pm_wp"))
        || wpCall.getDefCallArguments().size() < 4) return null;
    var wpArgs = wpCall.getDefCallArguments();
    return wpArgs.get(wpArgs.size() - 2);
  }

  private record WpData(CoreExpression iris, CoreExpression mask,
      CoreExpression expression, CoreExpression post) {}

  private @Nullable WpData wpData(ExpressionTypechecker typechecker,
      CoreExpression proposition) {
    CoreExpression value = dereference(typechecker, proposition)
        .unfold(Set.of(), null, true, false);
    for (int i = 0; i < 4; i++) {
      value = weakHead(typechecker, value);
      if (value instanceof CoreFunCallExpression call) {
        String name = call.getDefinition().getName();
        if ((name.equals("wp") || name.equals("pm_wp"))
            && call.getDefCallArguments().size() >= 4) {
          var args = call.getDefCallArguments();
          return new WpData(args.get(args.size() - 4),
              args.get(args.size() - 3),
              constructorForm(typechecker, args.get(args.size() - 2)),
              args.getLast());
        }
        value = value.unfold(Set.of(call.getDefinition()), null, true, false);
      } else {
        value = value.normalize(NormalizationMode.WHNF);
      }
    }
    return null;
  }

  private @Nullable WpData theoremSource(ExpressionTypechecker typechecker,
      TypedExpression theorem) {
    CoreExpression type = dereference(typechecker, theorem.getType());
    if (!(type instanceof CoreFunCallExpression entailment)
        || !entailment.getDefinition().getName().equals("properUPred_ent")
        || entailment.getDefCallArguments().size() < 3) return null;
    var args = entailment.getDefCallArguments();
    return wpData(typechecker, args.get(args.size() - 2));
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
    CoreConCallExpression valueExpression = constructor(typechecker, expression, "Val");
    if (valueExpression != null && !valueExpression.getDefCallArguments().isEmpty()) {
      CoreExpression value = valueExpression.getDefCallArguments().getLast();
      var factory = contextData.getFactory();
      var theoremArgs = theoremPrefix(contextData, iris, mask);
      theoremArgs.add(factory.arg(factory.core(value.computeTyped()), true));
      theoremArgs.add(factory.arg(factory.core(post.computeTyped()), true));
      ConcreteExpression precondition = factory.app(
          factory.core(post.computeTyped()), true,
          factory.core(value.computeTyped()));
      TypedExpression typedPrecondition = typechecker.typecheck(precondition, null);
      WpData resumed = typedPrecondition == null ? null
          : wpData(typechecker, typedPrecondition.getExpression());
      ConcreteExpression next = resumed == null || stopAfter == StopAfter.VALUE
          ? continuation
          : chain(typechecker, contextData, environment, resumed.iris(),
              resumed.mask(), resumed.expression(), resumed.post(), continuation,
              depth + 1);
      var args = new ArrayList<ConcreteArgument>();
      args.add(factory.arg(factory.hole(), false));
      args.add(factory.arg(factory.core(environment.computeTyped()), false));
      args.add(factory.arg(precondition, false));
      args.add(factory.arg(wp(contextData, iris, mask, expression, post), false));
      args.add(factory.arg(factory.app(factory.ref(wpValueIntro), theoremArgs), true));
      args.add(factory.arg(next, true));
      return factory.app(factory.ref(pmEntApply), args);
    }
    Step step = theorem(typechecker, contextData, iris, mask,
        expression, post);
    if (step == null) {
      Focus focus = focus(typechecker, contextData, expression);
      if (focus == null) return continuation;
      var factory = contextData.getFactory();
      var theoremArgs = theoremPrefix(contextData, iris, mask);
      theoremArgs.add(factory.arg(focus.item(), true));
      theoremArgs.add(factory.arg(factory.core(focus.expression().computeTyped()), true));
      theoremArgs.add(factory.arg(factory.core(post.computeTyped()), true));
      ConcreteExpression bindExpression = factory.app(factory.ref(wpBindItem), theoremArgs);
      TypedExpression bind = typechecker.typecheck(bindExpression, null);
      if (bind == null) return continuation;
      WpData source = theoremSource(typechecker, bind);
      if (source == null) return continuation;
      ConcreteExpression inner = chain(typechecker, contextData, environment,
          source.iris(), source.mask(), source.expression(), source.post(),
          continuation, depth + 1);
      var args = new ArrayList<ConcreteArgument>();
      args.add(factory.arg(factory.hole(), false));
      args.add(factory.arg(factory.core(environment.computeTyped()), false));
      args.add(factory.arg(wp(contextData, source.iris(), source.mask(),
          source.expression(), source.post()), false));
      args.add(factory.arg(wp(contextData, iris, mask, expression, post), false));
      args.add(factory.arg(factory.core(bind), true));
      args.add(factory.arg(inner, true));
      return factory.app(factory.ref(pmEntApply), args);
    }
    TypedExpression theorem = typechecker.typecheck(step.theorem(), null);
    if (theorem == null) return continuation;
    CoreExpression result = theoremResult(typechecker, theorem);
    if (result == null) return continuation;
    ConcreteExpression inner = stopsAfter(step.kind()) ? continuation
        : chain(typechecker, contextData, environment, iris,
            mask, result, post, continuation, depth + 1);
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(environment.computeTyped()), false));
    args.add(factory.arg(wp(contextData, iris, mask, result, post), false));
    args.add(factory.arg(wp(contextData, iris, mask, expression, post), false));
    args.add(factory.arg(factory.core(theorem), true));
    args.add(factory.arg(inner, true));
    return factory.app(factory.ref(pmEntApply), args);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    if (!requireCount(typechecker, contextData, 1)) return null;
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    WpData data = wpData(typechecker, goal.target());
    if (data == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_pures requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    CoreExpression iris = data.iris();
    CoreExpression mask = data.mask();
    CoreExpression expression = data.expression();
    CoreExpression post = data.post();
    ConcreteExpression proof = chain(typechecker, contextData, goal.environment(),
        iris, mask, expression, post, explicitArguments(contextData).getFirst(), 0);
    return typechecker.typecheck(proof, contextData.getExpectedType());
  }
}
