package org.arend.iris.proofmode;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
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

final class ExistsMeta extends ExactMeta {
  @Dependency(name = "PMFromExist")
  private CoreClassDefinition pmFromExist;
  @Dependency(name = "PMFromExist1")
  private CoreClassDefinition pmFromExist1;
  @Dependency(name = "pm_exists")
  private ArendRef pmExists;
  @Dependency(name = "pm_exists1")
  private ArendRef pmExists1;
  @Dependency(name = "pm_exists_from")
  private ArendRef pmExistsFrom;
  @Dependency(name = "pm_exists1_from")
  private ArendRef pmExists1From;

  @Dependency(name = "mkProperExist")
  private CoreFunctionDefinition mkProperExist;
  @Dependency(name = "mkProperExist1")
  private CoreFunctionDefinition mkProperExist1;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    var explicit = explicitArguments(contextData);
    if (explicit.size() != 2 && explicit.size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iExists expects a witness, an optional family, and a continuation",
          contextData.getMarker()));
      return null;
    }
    GoalData goal = resolveGoal(typechecker, contextData);
    if (goal == null) return null;
    CoreExpression target = weakHead(typechecker, goal.target());
    ClassEvidence evidence = null;
    boolean universeOne = false;
    if (explicit.size() == 3) {
      evidence = tryClassEvidence(typechecker, contextData,
          explicit.get(1), pmFromExist);
      if (evidence == null) {
        evidence = tryClassEvidence(typechecker, contextData,
            explicit.get(1), pmFromExist1);
        universeOne = evidence != null;
      }
    }
    CoreExpression carrier = null;
    CoreExpression family = null;
    CoreExpression evidenceTarget = null;
    if (evidence != null) {
      carrier = classField(evidence, "A");
      family = classField(evidence, "Phi");
      evidenceTarget = classField(evidence, "P");
      if (carrier == null || family == null || evidenceTarget == null) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Cannot inspect existential goal evidence",
            contextData.getMarker()));
        return null;
      }
    } else if (target instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist
        && exists.getDefCallArguments().size() >= 3) {
      var existsArgs = exists.getDefCallArguments();
      carrier = existsArgs.get(existsArgs.size() - 2);
      family = existsArgs.getLast();
    } else if (target instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist1
        && exists.getDefCallArguments().size() >= 3) {
      var existsArgs = exists.getDefCallArguments();
      carrier = existsArgs.get(existsArgs.size() - 2);
      family = existsArgs.getLast();
      universeOne = true;
    }
    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(goal.environment().computeTyped()), false));
    if (evidence != null) {
      args.add(factory.arg(factory.core(evidenceTarget.computeTyped()), false));
    }
    args.add(factory.arg(carrier == null ? factory.hole()
        : factory.core(carrier.computeTyped()), false));
    ConcreteExpression familyArgument = evidence != null
        ? factory.core(family.computeTyped()) : explicit.size() == 3 ? explicit.get(1)
        : family == null ? factory.hole() : factory.core(family.computeTyped());
    args.add(factory.arg(familyArgument, false));
    if (evidence != null) args.add(factory.arg(evidence.term(), true));
    args.add(factory.arg(explicit.get(0), true));
    args.add(factory.arg(explicit.getLast(), true));
    ArendRef lemma = universeOne
        ? evidence == null ? pmExists1 : pmExists1From
        : evidence == null ? pmExists : pmExistsFrom;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }
}
