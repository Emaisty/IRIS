package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreNewExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.ArrayList;

final class IntrosMeta extends ExactMeta {
  @Dependency(name = "pm_destruct_sep")
  private ArendRef pmDestructSep;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "pm_rename_spatial")
  private ArendRef pmRenameSpatial;

  @Dependency(name = "envs_entails")
  private CoreFunctionDefinition envsEntails;

  @Dependency(name = "pm_snoc")
  private CoreConstructor pmSnoc;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Dependency(name = "PMFromForall")
  private CoreClassDefinition pmFromForall;

  @Dependency(name = "pm_forall")
  private ArendRef pmForall;

  @Dependency(name = "pm_forall_from")
  private ArendRef pmForallFrom;

  @Dependency(name = "mkProperForall")
  private CoreFunctionDefinition mkProperForall;

  @Dependency(name = "intuitionistic")
  private CoreClassField intuitionisticField;

  @Dependency(name = "spatial")
  private CoreClassField spatialField;

  @Override
  protected CoreExpression dereference(ExpressionTypechecker typechecker,
      CoreExpression expression) {
    CoreExpression result = expression.getUnderlyingExpression();
    while (result instanceof CoreInferenceReferenceExpression inference) {
      if (inference.getSubstExpression() == null) {
        typechecker.solveEquationsFor(inference.getVariable());
      }
      if (inference.getSubstExpression() == null) break;
      result = inference.getSubstExpression().getUnderlyingExpression();
    }
    return result;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    if (explicit.size() != 2 && explicit.size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros expects a pattern, optional PMFromForall evidence, and a continuation",
          contextData.getMarker()));
      return null;
    }
    String pattern = stringArgument(typechecker, contextData, 0);
    if (pattern == null) return null;
    if (pattern.trim().isEmpty()) {
      return introForall(typechecker, contextData, explicit);
    }
    if (explicit.size() != 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Named iIntros does not accept universal-goal evidence",
          contextData.getMarker()));
      return null;
    }
    String[] names = pattern.trim().split("\\s+");
    if (names.length > 2) {
      GoalData goal = resolveGoal(typechecker, contextData);
      if (goal == null) return null;
      String restName = freshName(typechecker, goal.environment(),
          "_ipm_intros_rest_", names);
      String remaining = String.join(" ",
          java.util.Arrays.copyOfRange(names, 1, names.length));
      var factory = contextData.getFactory();
      ConcreteExpression inner = factory.app(factory.meta("iIntros", this), true,
          factory.string(remaining), explicitArguments(contextData).get(1));
      ConcreteExpression outer = factory.app(factory.meta("iIntros", this), true,
          factory.string(names[0] + " " + restName), inner);
      return typechecker.typecheck(outer, contextData.getExpectedType());
    }
    if (names.length == 1 && !names[0].isEmpty()) {
      String introduced = names[0];
      ResolvedSelection resolved = resolveNamed(typechecker, contextData, "");
      if (resolved == null) return null;
      if (resolved.persistent()) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "iIntros expected an anonymous spatial hypothesis",
            contextData.getMarker()));
        return null;
      }
      if (environmentContainsName(typechecker, resolved.environment(), introduced)) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Proof-mode hypothesis '" + introduced + "' already exists",
            contextData.getMarker()));
        return null;
      }
      var factory = contextData.getFactory();
      var callArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
      callArgs.add(factory.arg(factory.hole(), false));
      callArgs.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
      callArgs.add(factory.arg(resolved.selection().term(), true));
      callArgs.add(factory.arg(name(contextData, introduced), true));
      callArgs.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
      callArgs.add(factory.arg(explicitArguments(contextData).get(1), true));
      return typechecker.typecheck(factory.app(factory.ref(pmRenameSpatial), callArgs),
          contextData.getExpectedType());
    }
    if (names.length != 2 || names[0].isEmpty() || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros expects one name or two separating-conjunction names",
          contextData.getMarker()));
      return null;
    }
    if (names[0].equals(names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + names[0] + "'",
          contextData.getMarker()));
      return null;
    }
    var arguments = explicitArguments(contextData);
    ConcreteExpression next = arguments.get(1);

    if (contextData.getExpectedType() == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros has no expected proof-mode goal", contextData.getMarker()));
      return null;
    }
    CoreExpression expected = dereference(typechecker, contextData.getExpectedType());
    if (!(expected instanceof CoreFunCallExpression goal)
        || goal.getDefinition() != envsEntails
        || goal.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros must run inside ipm", contextData.getMarker()));
      return null;
    }

    CoreExpression envExpression = dereference(typechecker, goal.getDefCallArguments().get(1));
    CoreClassCallExpression envClass = envExpression instanceof CoreNewExpression newExpression
        ? newExpression.getClassCall()
        : envExpression instanceof CoreClassCallExpression classCall ? classCall : null;
    if (envClass == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect the proof-mode environment", contextData.getMarker()));
      return null;
    }
    CoreExpression intuitionistic = envClass.getClosedImplementation(intuitionisticField);
    CoreExpression spatial = envClass.getClosedImplementation(spatialField);
    if (intuitionistic == null || spatial == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Incomplete proof-mode environment", contextData.getMarker()));
      return null;
    }
    if (environmentContainsName(typechecker, envExpression, names[0])
        || environmentContainsName(typechecker, envExpression, names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }

    CoreExpression spatialCore = dereference(typechecker, spatial);
    if (!(spatialCore instanceof CoreConCallExpression snoc)
        || snoc.getDefinition() != pmSnoc
        || snoc.getDefCallArguments().size() < 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iIntros expected one spatial hypothesis", contextData.getMarker()));
      return null;
    }
    List<? extends CoreExpression> snocArgs = snoc.getDefCallArguments();
    CoreExpression tail = snocArgs.get(snocArgs.size() - 3);
    CoreExpression anonymous = snocArgs.get(snocArgs.size() - 2);
    CoreExpression proposition = dereference(typechecker, snocArgs.get(snocArgs.size() - 1));
    if (!(proposition instanceof CoreFunCallExpression)) {
      proposition = dereference(typechecker,
          proposition.normalize(NormalizationMode.WHNF));
    }
    CoreFunCallExpression sep = proposition instanceof CoreFunCallExpression call
        && call.getDefinition().getName().equals(mkProperSep.getName())
        && call.getDefCallArguments().size() >= 3 ? call : null;
    List<? extends CoreExpression> sepArgs = sep == null
        ? java.util.Collections.emptyList() : sep.getDefCallArguments();
    CoreExpression left = sep == null ? null
        : sepArgs.get(sepArgs.size() - 2);
    CoreExpression right = sep == null ? null : sepArgs.get(sepArgs.size() - 1);
    CoreExpression target = goal.getDefCallArguments().getLast();

    var factory = contextData.getFactory();
    var selectionArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
    selectionArgs.add(factory.arg(factory.hole(), false));
    selectionArgs.add(factory.arg(factory.core(tail.computeTyped()), true));
    selectionArgs.add(factory.arg(factory.core(anonymous.computeTyped()), true));
    selectionArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression selection = factory.app(factory.ref(pmSelectHere), selectionArgs);

    var reflArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression split = factory.app(factory.ref(entailmentRefl), reflArgs);

    var callArgs = new ArrayList<org.arend.ext.concrete.expr.ConcreteArgument>();
    callArgs.add(factory.arg(factory.hole(), false));
    callArgs.add(factory.arg(factory.core(envExpression.computeTyped()), false));
    callArgs.add(factory.arg(selection, true));
    callArgs.add(factory.arg(name(contextData, names[0]), true));
    callArgs.add(factory.arg(name(contextData, names[1]), true));
    callArgs.add(factory.arg(left == null ? factory.hole()
        : factory.core(left.computeTyped()), false));
    callArgs.add(factory.arg(right == null ? factory.hole()
        : factory.core(right.computeTyped()), false));
    callArgs.add(factory.arg(factory.core(target.computeTyped()), false));
    callArgs.add(factory.arg(split, true));
    callArgs.add(factory.arg(next, true));
    ConcreteExpression call = factory.app(factory.ref(pmDestructSep), callArgs);
    return typechecker.typecheck(call, contextData.getExpectedType());
  }

  private @Nullable TypedExpression introForall(
      ExpressionTypechecker typechecker, ContextData contextData,
      List<ConcreteExpression> explicit) {
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    ClassEvidence evidence = explicit.size() == 3
        ? classEvidence(typechecker, contextData, explicit.get(1),
            pmFromForall, "PMFromForall") : null;
    if (explicit.size() == 3 && evidence == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    CoreFunCallExpression forall = target instanceof CoreFunCallExpression call
        && call.getDefinition() == mkProperForall
        && call.getDefCallArguments().size() >= 3 ? call : null;
    if (evidence == null && forall == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Empty iIntros expects a universal goal or PMFromForall evidence",
          contextData.getMarker()));
      return null;
    }
    CoreExpression carrier = evidence == null
        ? forall.getDefCallArguments().get(forall.getDefCallArguments().size() - 2)
        : classField(evidence, "A");
    CoreExpression family = evidence == null
        ? forall.getDefCallArguments().getLast() : classField(evidence, "Phi");
    CoreExpression evidenceTarget = evidence == null ? null
        : classField(evidence, "P");
    if (carrier == null || family == null
        || evidence != null && evidenceTarget == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect universal-goal evidence", contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    if (evidence != null) {
      args.add(factory.arg(factory.core(evidenceTarget.computeTyped()), false));
    }
    args.add(factory.arg(factory.core(carrier.computeTyped()), false));
    args.add(factory.arg(factory.core(family.computeTyped()), false));
    if (evidence != null) args.add(factory.arg(evidence.term(), true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmForall : pmForallFrom), args),
        contextData.getExpectedType());
  }
}
