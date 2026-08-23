package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
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

class WpBindMeta extends ExactMeta {
  @Dependency(name = "pm_wp_bind_item")
  private ArendRef pmWpBindItem;
  @Dependency(name = "AppLCtx")
  private ArendRef appLCtx;
  @Dependency(name = "AppRCtx")
  private ArendRef appRCtx;
  @Dependency(name = "IfCtx")
  private ArendRef ifCtx;
  @Dependency(name = "PairLCtx")
  private ArendRef pairLCtx;
  @Dependency(name = "PairRCtx")
  private ArendRef pairRCtx;
  @Dependency(name = "FstCtx")
  private ArendRef fstCtx;
  @Dependency(name = "SndCtx")
  private ArendRef sndCtx;
  @Dependency(name = "IsZeroCtx")
  private ArendRef isZeroCtx;
  @Dependency(name = "PredCtx")
  private ArendRef predCtx;
  @Dependency(name = "MulLCtx")
  private ArendRef mulLCtx;
  @Dependency(name = "MulRCtx")
  private ArendRef mulRCtx;
  @Dependency(name = "AllocCtx")
  private ArendRef allocCtx;
  @Dependency(name = "LoadCtx")
  private ArendRef loadCtx;
  @Dependency(name = "StoreLCtx")
  private ArendRef storeLCtx;
  @Dependency(name = "StoreRCtx")
  private ArendRef storeRCtx;

  protected record Focus(ConcreteExpression item, CoreExpression expression) {}

  protected CoreExpression constructorForm(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = dereference(typechecker, expression);
    return result instanceof CoreConCallExpression ? result
        : dereference(typechecker, result.normalize(NormalizationMode.NF));
  }

  protected @Nullable CoreExpression value(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = constructorForm(typechecker, expression);
    return result instanceof CoreConCallExpression call
        && call.getDefinition().getName().equals("Val")
        && !call.getDefCallArguments().isEmpty()
        ? call.getDefCallArguments().getLast() : null;
  }

  protected ConcreteExpression item(ContextData contextData, ArendRef constructor,
      CoreExpression... arguments) {
    var factory = contextData.getFactory();
    List<ConcreteArgument> args = new ArrayList<>();
    for (CoreExpression argument : arguments) {
      args.add(factory.arg(factory.core(argument.computeTyped()), true));
    }
    return args.isEmpty() ? factory.ref(constructor)
        : factory.app(factory.ref(constructor), args);
  }

  protected @Nullable Focus focus(ExpressionTypechecker typechecker,
      ContextData contextData, CoreExpression expression) {
    CoreExpression form = constructorForm(typechecker, expression);
    if (!(form instanceof CoreConCallExpression call)) return null;
    var fields = call.getDefCallArguments();
    String name = call.getDefinition().getName();
    if ((name.equals("App") || name.equals("Pair") || name.equals("Mul")
        || name.equals("Store")) && fields.size() >= 2) {
      CoreExpression left = fields.get(fields.size() - 2);
      CoreExpression right = fields.getLast();
      CoreExpression leftValue = value(typechecker, left);
      if (leftValue == null) {
        ArendRef constructor = switch (name) {
          case "App" -> appLCtx;
          case "Pair" -> pairLCtx;
          case "Mul" -> mulLCtx;
          default -> storeLCtx;
        };
        return new Focus(item(contextData, constructor, right), left);
      }
      if (value(typechecker, right) == null) {
        ArendRef constructor = switch (name) {
          case "App" -> appRCtx;
          case "Pair" -> pairRCtx;
          case "Mul" -> mulRCtx;
          default -> storeRCtx;
        };
        return new Focus(item(contextData, constructor, leftValue), right);
      }
      return null;
    }
    if (name.equals("If") && fields.size() >= 3) {
      CoreExpression condition = fields.get(fields.size() - 3);
      return value(typechecker, condition) == null
          ? new Focus(item(contextData, ifCtx,
              fields.get(fields.size() - 2), fields.getLast()), condition)
          : null;
    }
    if (fields.isEmpty()) return null;
    CoreExpression argument = fields.getLast();
    if (value(typechecker, argument) != null) return null;
    ArendRef constructor = switch (name) {
      case "Fst" -> fstCtx;
      case "Snd" -> sndCtx;
      case "IsZero" -> isZeroCtx;
      case "Pred" -> predCtx;
      case "Alloc" -> allocCtx;
      case "Load" -> loadCtx;
      default -> null;
    };
    return constructor == null ? null
        : new Focus(item(contextData, constructor), argument);
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
          "wp_bind requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    var wpArgs = wpCall.getDefCallArguments();
    CoreExpression iris = wpArgs.get(wpArgs.size() - 4);
    CoreExpression mask = wpArgs.get(wpArgs.size() - 3);
    CoreExpression expression = wpArgs.get(wpArgs.size() - 2);
    CoreExpression post = wpArgs.getLast();
    Focus focus = focus(typechecker, contextData, expression);
    if (focus == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "wp_bind found no evaluation context", contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(iris.computeTyped()), true));
    args.add(factory.arg(factory.core(mask.computeTyped()), true));
    args.add(factory.arg(focus.item(), true));
    args.add(factory.arg(factory.core(focus.expression().computeTyped()), true));
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(explicitArguments(contextData).getFirst(), true));
    return typechecker.typecheck(factory.app(factory.ref(pmWpBindItem), args),
        contextData.getExpectedType());
  }
}
