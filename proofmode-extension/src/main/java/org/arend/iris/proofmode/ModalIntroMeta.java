package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteStringExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
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
import java.util.List;

abstract class ModalIntroMeta extends ExactMeta {
  protected abstract CoreFunctionDefinition modality();
  protected abstract ArendRef lemma();
  protected @Nullable CoreClassDefinition evidenceClass() { return null; }
  protected @Nullable ArendRef evidenceLemma() { return null; }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    boolean withEvidence = explicit.size() == 2 && evidenceClass() != null;
    if (explicit.size() != 1 && !withEvidence) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected optional modal evidence and a continuation",
          contextData.getMarker()));
      return null;
    }
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    ClassEvidence evidence = withEvidence
        ? classEvidence(typechecker, contextData, explicit.getFirst(),
            evidenceClass(), evidenceClass().getName()) : null;
    if (withEvidence && evidence == null) return null;
    CoreFunCallExpression modal = target instanceof CoreFunCallExpression call
        && call.getDefinition() == modality()
        && call.getDefCallArguments().size() >= 2 ? call : null;
    if (evidence == null && modal == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected the corresponding modal goal", contextData.getMarker()));
      return null;
    }
    CoreExpression body = evidence == null
        ? modal.getDefCallArguments().getLast() : classField(evidence, "P");
    CoreExpression evidenceTarget = evidence == null ? null : classField(evidence, "Q");
    if (body == null || evidence != null && evidenceTarget == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect modal evidence", contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    if (evidence != null) {
      args.add(factory.arg(factory.core(evidenceTarget.computeTyped()), false));
      args.add(factory.arg(evidence.term(), true));
    }
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? lemma() : evidenceLemma()), args),
        contextData.getExpectedType());
  }
}

final class NextMeta extends ModalIntroMeta {
  @Dependency(name = "PMFromLater")
  private CoreClassDefinition pmFromLater;
  @Dependency(name = "mkProperLater")
  private CoreFunctionDefinition mkProperLater;
  @Dependency(name = "pm_next")
  private ArendRef pmNext;
  @Dependency(name = "pm_next_from")
  private ArendRef pmNextFrom;
  @Dependency(name = "PMIntoLater")
  private CoreClassDefinition pmIntoLater;
  @Dependency(name = "pm_next_hyp")
  private ArendRef pmNextHyp;
  @Dependency(name = "pm_next_hyp_from")
  private ArendRef pmNextHypFrom;
  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;
  @Override protected CoreFunctionDefinition modality() { return mkProperLater; }
  @Override protected ArendRef lemma() { return pmNext; }
  @Override protected CoreClassDefinition evidenceClass() { return pmFromLater; }
  @Override protected ArendRef evidenceLemma() { return pmNextFrom; }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> explicit = explicitArguments(contextData);
    if (!explicit.isEmpty()
        && explicit.getFirst() instanceof ConcreteStringExpression) {
      return nextHypothesis(typechecker, contextData, explicit);
    }
    return super.invokeMeta(typechecker, contextData);
  }

  private @Nullable TypedExpression nextHypothesis(
      ExpressionTypechecker typechecker, ContextData contextData,
      List<ConcreteExpression> explicit) {
    if (explicit.size() != 2 && explicit.size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Hypothesis iNext expects a name, optional PMIntoLater evidence, and a continuation",
          contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    if (requested == null) return null;
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Hypothesis iNext currently expects a spatial hypothesis",
          contextData.getMarker()));
      return null;
    }

    ClassEvidence evidence = explicit.size() == 3
        ? classEvidence(typechecker, contextData, explicit.get(1),
            pmIntoLater, "PMIntoLater") : null;
    if (explicit.size() == 3 && evidence == null) return null;
    CoreExpression source = weakHead(typechecker,
        resolved.selection().proposition());
    CoreFunCallExpression sourceLater = source instanceof CoreFunCallExpression call
        && call.getDefinition() == mkProperLater
        && call.getDefCallArguments().size() >= 2 ? call : null;
    CoreExpression body = evidence == null ? sourceLater == null ? null
        : sourceLater.getDefCallArguments().getLast() : classField(evidence, "Q");
    if (body == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Hypothesis iNext expected a later hypothesis or PMIntoLater evidence",
          contextData.getMarker()));
      return null;
    }

    CoreExpression target = weakHead(typechecker, resolved.target());
    CoreFunCallExpression targetLater = target instanceof CoreFunCallExpression call
        && call.getDefinition() == mkProperLater
        && call.getDefCallArguments().size() >= 2 ? call : null;
    if (targetLater == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Hypothesis iNext expects a later goal",
          contextData.getMarker()));
      return null;
    }
    CoreExpression targetBody = targetLater.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    ConcreteExpression into;
    if (evidence == null) {
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(source.computeTyped()), true));
      into = factory.app(factory.ref(entailmentRefl), reflArgs);
    } else {
      into = evidence.term();
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, requested), true));
    args.add(factory.arg(factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(targetBody.computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(explicit.getLast(), true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmNextHyp : pmNextHypFrom), args),
        contextData.getExpectedType());
  }
}

final class ModIntroMeta extends ModalIntroMeta {
  @Dependency(name = "mkProperBUpd")
  private CoreFunctionDefinition mkProperBUpd;
  @Dependency(name = "pm_mod_intro")
  private ArendRef pmModIntro;
  @Override protected CoreFunctionDefinition modality() { return mkProperBUpd; }
  @Override protected ArendRef lemma() { return pmModIntro; }
}
