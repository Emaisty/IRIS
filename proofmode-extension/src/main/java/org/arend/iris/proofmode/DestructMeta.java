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

final class DestructMeta extends ExactMeta {
  @Dependency(name = "PMFromSep")
  private CoreClassDefinition pmFromSep;

  @Dependency(name = "pm_destruct_sep")
  private ArendRef pmDestructSep;
  @Dependency(name = "pm_destruct_from_sep")
  private ArendRef pmDestructFromSep;

  @Dependency(name = "pm_destruct_persistent")
  private ArendRef pmDestructPersistent;
  @Dependency(name = "pm_destruct_persistent_copy")
  private ArendRef pmDestructPersistentCopy;
  @Dependency(name = "PMIntoPersistent")
  private CoreClassDefinition pmIntoPersistent;
  @Dependency(name = "pm_destruct_into_persistent")
  private ArendRef pmDestructIntoPersistent;
  @Dependency(name = "pm_destruct_into_persistent_copy")
  private ArendRef pmDestructIntoPersistentCopy;

  @Dependency(name = "pm_destruct_exist")
  private ArendRef pmDestructExist;
  @Dependency(name = "pm_destruct_exist1")
  private ArendRef pmDestructExist1;
  @Dependency(name = "pm_destruct_exist_intuitionistic")
  private ArendRef pmDestructExistIntuitionistic;
  @Dependency(name = "PMIntoExist")
  private CoreClassDefinition pmIntoExist;
  @Dependency(name = "PMIntoExist1")
  private CoreClassDefinition pmIntoExist1;
  @Dependency(name = "pm_destruct_into_exist")
  private ArendRef pmDestructIntoExist;
  @Dependency(name = "pm_destruct_into_exist1")
  private ArendRef pmDestructIntoExist1;
  @Dependency(name = "pm_destruct_into_exist_intuitionistic")
  private ArendRef pmDestructIntoExistIntuitionistic;

  @Dependency(name = "pm_destruct_pure")
  private ArendRef pmDestructPure;
  @Dependency(name = "PMIntoPure")
  private CoreClassDefinition pmIntoPure;
  @Dependency(name = "pm_destruct_into_pure")
  private ArendRef pmDestructIntoPure;

  @Dependency(name = "pm_destruct_and_pure_l")
  private ArendRef pmDestructAndPureLeft;

  @Dependency(name = "pm_destruct_or")
  private ArendRef pmDestructOr;
  @Dependency(name = "PMIntoOr")
  private CoreClassDefinition pmIntoOr;
  @Dependency(name = "pm_destruct_into_or")
  private ArendRef pmDestructIntoOr;

  @Dependency(name = "properUPred_ent_refl")
  private ArendRef entailmentRefl;

  @Dependency(name = "mkProperSep")
  private CoreFunctionDefinition mkProperSep;

  @Dependency(name = "mkProperPersistently")
  private CoreFunctionDefinition mkProperPersistently;

  @Dependency(name = "mkProperExist")
  private CoreFunctionDefinition mkProperExist;
  @Dependency(name = "mkProperExist1")
  private CoreFunctionDefinition mkProperExist1;

  @Dependency(name = "mkProperPure")
  private CoreFunctionDefinition mkProperPure;

  @Dependency(name = "mkProperAnd")
  private CoreFunctionDefinition mkProperAnd;

  @Dependency(name = "mkProperOr")
  private CoreFunctionDefinition mkProperOr;

  private record SepEvidence(CoreExpression left, CoreExpression right,
      ConcreteExpression term) {}

  private record PureEvidence(CoreExpression fact, ConcreteExpression term) {}

  private record ExistEvidence(CoreExpression carrier, CoreExpression family,
      ConcreteExpression term, boolean universeOne) {}

  private @Nullable SepEvidence sepEvidence(ExpressionTypechecker typechecker,
      ContextData contextData, ConcreteExpression expression) {
    ClassEvidence checked = classEvidence(typechecker, contextData,
        expression, pmFromSep, "PMFromSep");
    if (checked == null) return null;
    CoreExpression left = classField(checked, "Q");
    CoreExpression right = classField(checked, "R");
    if (left == null || right == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMFromSep evidence", contextData.getMarker()));
      return null;
    }
    return new SepEvidence(left, right, checked.term());
  }

  private @Nullable PureEvidence pureEvidence(ExpressionTypechecker typechecker,
      ContextData contextData, ConcreteExpression expression) {
    ClassEvidence checked = tryClassEvidence(typechecker, contextData,
        expression, pmIntoPure);
    if (checked == null) return null;
    CoreExpression fact = classField(checked, "phi");
    if (fact == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMIntoPure evidence", contextData.getMarker()));
      return null;
    }
    return new PureEvidence(fact, checked.term());
  }

  private @Nullable ExistEvidence existEvidence(ExpressionTypechecker typechecker,
      ContextData contextData, ConcreteExpression expression) {
    ClassEvidence checked = tryClassEvidence(typechecker, contextData,
        expression, pmIntoExist);
    boolean universeOne = false;
    if (checked == null) {
      checked = tryClassEvidence(typechecker, contextData,
          expression, pmIntoExist1);
      universeOne = true;
    }
    if (checked == null) return null;
    CoreExpression carrier = classField(checked, "A");
    CoreExpression family = classField(checked, "Phi");
    if (carrier == null || family == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect existential proof-mode evidence",
          contextData.getMarker()));
      return null;
    }
    return new ExistEvidence(carrier, family, checked.term(), universeOne);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    var explicit = explicitArguments(contextData);
    if (explicit.size() < 3 || explicit.size() > 6) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Expected 3 to 6 arguments", contextData.getMarker()));
      return null;
    }
    String requested = stringArgument(typechecker, contextData, 0);
    String pattern = stringArgument(typechecker, contextData, 1);
    if (requested == null || pattern == null) return null;
    String trimmedPattern = pattern.trim();
    ConcreteExpression explicitShape = explicit.size() >= 4 ? explicit.get(2) : null;
    ConcreteExpression explicitRight = explicit.size() == 5 ? explicit.get(3) : null;
    ConcreteExpression continuation = explicit.get(explicit.size() - 1);
    if (trimmedPattern.startsWith("#")) {
      if (explicit.size() != 3 && explicit.size() != 4) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Persistent iDestruct expects a name pattern, optional persistence rule, and a continuation",
            contextData.getMarker()));
        return null;
      }
      return destructPersistent(typechecker, contextData, requested,
          trimmedPattern.substring(1).trim());
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    String[] flatNames = trimmedPattern.split("\\s+");
    if (flatNames.length > 2 && !trimmedPattern.contains("|")) {
      if (explicit.size() != 3) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Multi-name iDestruct does not take explicit proposition arguments",
            contextData.getMarker()));
        return null;
      }
      String restName = freshName(typechecker, resolved.environment(),
          "_ipm_destruct_rest_", flatNames);
      String remaining = String.join(" ",
          java.util.Arrays.copyOfRange(flatNames, 1, flatNames.length));
      var factory = contextData.getFactory();
      ConcreteExpression inner = factory.app(factory.meta("iDestruct", this), true,
          factory.string(restName), factory.string(remaining), continuation);
      ConcreteExpression outer = factory.app(factory.meta("iDestruct", this), true,
          factory.string(requested),
          factory.string(flatNames[0] + " " + restName), inner);
      return typechecker.typecheck(outer, contextData.getExpectedType());
    }
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    if (resolved.persistent()) {
      if (proposition instanceof CoreFunCallExpression exists
          && exists.getDefinition() == mkProperExist
          && exists.getDefCallArguments().size() >= 3) {
        return destructExist(typechecker, contextData, resolved, proposition,
            exists, requested, trimmedPattern, explicitShape, continuation);
      }
      String[] names = trimmedPattern.split("\\s+");
      if (names.length == 1 && !trimmedPattern.isEmpty()) {
        return destructExist(typechecker, contextData, resolved, proposition,
            null, requested, trimmedPattern, explicitShape, continuation);
      }
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Only existential intuitionistic hypotheses can currently be destructed",
          contextData.getMarker()));
      return null;
    }
    String[] branchNames = trimmedPattern.split("\\|", -1);
    if (branchNames.length == 2) {
      if (explicit.size() < 4 || explicit.size() > 6) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Disjunction iDestruct expects two branch continuations and optional PMIntoOr evidence or propositions",
            contextData.getMarker()));
        return null;
      }
      CoreFunCallExpression or = proposition instanceof CoreFunCallExpression call
          && call.getDefinition() == mkProperOr
          && call.getDefCallArguments().size() >= 3 ? call : null;
      return destructOr(typechecker, contextData, resolved, proposition, or,
          requested, branchNames[0].trim(), branchNames[1].trim(), explicit);
    }
    if (proposition instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist
        && exists.getDefCallArguments().size() >= 3) {
      return destructExist(typechecker, contextData, resolved, proposition,
          exists, requested, trimmedPattern, explicitShape, continuation);
    }
    if (proposition instanceof CoreFunCallExpression exists
        && exists.getDefinition() == mkProperExist1
        && exists.getDefCallArguments().size() >= 3) {
      return destructExist(typechecker, contextData, resolved, proposition,
          exists, requested, trimmedPattern, explicitShape, continuation, true);
    }
    if (proposition instanceof CoreFunCallExpression pure
        && pure.getDefinition() == mkProperPure
        && pure.getDefCallArguments().size() >= 2) {
      return destructPure(typechecker, contextData, resolved, proposition,
          pure, trimmedPattern, explicitShape, continuation);
    }
    if (explicit.size() == 3
        && proposition instanceof CoreFunCallExpression and
        && and.getDefinition() == mkProperAnd
        && and.getDefCallArguments().size() >= 3) {
      CoreExpression left = weakHead(typechecker,
          and.getDefCallArguments().get(and.getDefCallArguments().size() - 2));
      if (left instanceof CoreFunCallExpression pure
          && pure.getDefinition() == mkProperPure
          && pure.getDefCallArguments().size() >= 2) {
        return destructAndPureLeft(typechecker, contextData, resolved,
            proposition, and, pure, requested, trimmedPattern, continuation);
      }
    }
    String[] inferredNames = trimmedPattern.split("\\s+");
    if (explicit.size() == 4 && inferredNames.length == 1
        && !trimmedPattern.isEmpty() && !trimmedPattern.equals("%")) {
      return destructExist(typechecker, contextData, resolved, proposition,
          null, requested, trimmedPattern, explicitShape, continuation);
    }
    if (proposition instanceof CoreFunCallExpression sep
        && sep.getDefinition() == mkProperSep
        && sep.getDefCallArguments().size() >= 3) {
      return destructSep(typechecker, contextData, resolved, proposition,
          sep, requested, trimmedPattern, explicitShape, explicitRight, continuation);
    }
    if (trimmedPattern.equals("%")) {
      return destructPure(typechecker, contextData, resolved, proposition,
          null, trimmedPattern, explicitShape, continuation);
    }
    if (inferredNames.length == 1 && !trimmedPattern.isEmpty()) {
      return destructExist(typechecker, contextData, resolved, proposition,
          null, requested, trimmedPattern, explicitShape, continuation);
    }
    if (inferredNames.length == 2) {
      return destructSep(typechecker, contextData, resolved, proposition,
          null, requested, trimmedPattern, explicitShape, explicitRight, continuation);
    }
    typechecker.getErrorReporter().report(new TypecheckingError(
        "iDestruct expected a separating conjunction, existential, pure, or persistent proposition",
        contextData.getMarker()));
    return null;
  }

  private @Nullable TypedExpression destructAndPureLeft(
      ExpressionTypechecker typechecker, ContextData contextData,
      ResolvedSelection resolved, CoreExpression proposition,
      CoreFunCallExpression and, CoreFunCallExpression pure,
      String requested, String pattern, ConcreteExpression continuation) {
    if (explicitArguments(contextData).size() != 3) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure conjunction iDestruct expects a pattern and continuation",
          contextData.getMarker()));
      return null;
    }
    String[] names = pattern.split("\\s+");
    if (names.length != 2 || !names[0].equals("%") || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure conjunction iDestruct expects the pattern '% Hrest'",
          contextData.getMarker()));
      return null;
    }
    String introduced = names[1];
    if (!introduced.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + introduced + "'",
          contextData.getMarker()));
      return null;
    }
    CoreExpression fact = pure.getDefCallArguments().getLast();
    CoreExpression right = and.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    var reflArgs = new ArrayList<ConcreteArgument>();
    reflArgs.add(factory.arg(factory.hole(), false));
    reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
    ConcreteExpression into = factory.app(factory.ref(entailmentRefl), reflArgs);

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(factory.core(fact.computeTyped()), false));
    args.add(factory.arg(factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(continuation, true));
    return typechecker.typecheck(factory.app(factory.ref(pmDestructAndPureLeft), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructOr(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved, CoreExpression proposition,
      @Nullable CoreFunCallExpression or, String requested, String leftName,
      String rightName, java.util.List<ConcreteExpression> explicit) {
    if (leftName.isEmpty() || rightName.isEmpty()
        || leftName.contains(" ") || rightName.contains(" ")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Disjunction iDestruct expects one name in each branch",
          contextData.getMarker()));
      return null;
    }
    if ((!leftName.equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), leftName))
        || (!rightName.equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), rightName))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iDestruct would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    ClassEvidence evidence = explicit.size() == 5
        ? classEvidence(typechecker, contextData, explicit.get(2),
            pmIntoOr, "PMIntoOr") : null;
    if (explicit.size() == 5 && evidence == null) return null;
    CoreExpression left = evidence != null ? classField(evidence, "Q") : or == null ? null
        : or.getDefCallArguments().get(or.getDefCallArguments().size() - 2);
    CoreExpression right = evidence != null ? classField(evidence, "R") : or == null
        ? null : or.getDefCallArguments().getLast();
    if (evidence != null && (left == null || right == null)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMIntoOr evidence", contextData.getMarker()));
      return null;
    }
    ConcreteExpression explicitLeft = explicit.size() == 6 ? explicit.get(2) : null;
    ConcreteExpression explicitRight = explicit.size() == 6 ? explicit.get(3) : null;
    ConcreteExpression leftContinuation = explicit.get(explicit.size() - 2);
    ConcreteExpression rightContinuation = explicit.getLast();

    ConcreteExpression into;
    if (evidence == null) {
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      into = factory.app(factory.ref(entailmentRefl), reflArgs);
    } else {
      into = evidence.term();
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, leftName), true));
    args.add(factory.arg(name(contextData, rightName), true));
    args.add(factory.arg(explicitLeft != null ? explicitLeft : left == null
        ? factory.hole() : factory.core(left.computeTyped()), false));
    args.add(factory.arg(explicitRight != null ? explicitRight : right == null
        ? factory.hole() : factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(leftContinuation, true));
    args.add(factory.arg(rightContinuation, true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmDestructOr : pmDestructIntoOr), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructSep(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression sep,
      String requested, String pattern, @Nullable ConcreteExpression explicitLeft,
      @Nullable ConcreteExpression explicitRight, ConcreteExpression continuation) {
    String[] names = pattern.split("\\s+");
    if (names.length != 2 || names[0].isEmpty() || names[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Separating-conjunction iDestruct expects exactly two names",
          contextData.getMarker()));
      return null;
    }
    if (names[0].equals(names[1])) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + names[0] + "'",
          contextData.getMarker()));
      return null;
    }
    if ((!names[0].equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), names[0]))
        || (!names[1].equals(requested)
          && environmentContainsName(typechecker, resolved.environment(), names[1]))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iDestruct would introduce a duplicate proof-mode name",
          contextData.getMarker()));
      return null;
    }
    SepEvidence evidence = explicitLeft != null && explicitRight == null
        ? sepEvidence(typechecker, contextData, explicitLeft) : null;
    if (explicitLeft != null && explicitRight == null && evidence == null) {
      return null;
    }
    if (explicitLeft == null && explicitRight != null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Explicit separating-conjunction iDestruct expects both propositions",
          contextData.getMarker()));
      return null;
    }
    CoreExpression left = evidence != null ? evidence.left() : sep == null ? null
        : sep.getDefCallArguments().get(sep.getDefCallArguments().size() - 2);
    CoreExpression right = evidence != null ? evidence.right() : sep == null
        ? null : sep.getDefCallArguments().getLast();
    var factory = contextData.getFactory();
    ConcreteExpression split;
    if (evidence == null) {
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      split = factory.app(factory.ref(entailmentRefl), reflArgs);
    } else {
      split = evidence.term();
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, names[0]), true));
    args.add(factory.arg(name(contextData, names[1]), true));
    args.add(factory.arg(evidence == null && explicitLeft != null ? explicitLeft : left == null
        ? factory.hole() : factory.core(left.computeTyped()), false));
    args.add(factory.arg(evidence == null && explicitRight != null ? explicitRight : right == null
        ? factory.hole() : factory.core(right.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(split, true));
    args.add(factory.arg(continuation, true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmDestructSep : pmDestructFromSep), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructExist(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression exists,
      String requested, String introduced, @Nullable ConcreteExpression explicitFamily,
      ConcreteExpression continuation) {
    return destructExist(typechecker, contextData, resolved, proposition, exists,
        requested, introduced, explicitFamily, continuation, false);
  }

  private @Nullable TypedExpression destructExist(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression exists,
      String requested, String introduced, @Nullable ConcreteExpression explicitFamily,
      ConcreteExpression continuation, boolean universeOne) {
    if (explicitArguments(contextData).size() > 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Existential iDestruct accepts at most one explicit family",
          contextData.getMarker()));
      return null;
    }
    if (introduced.isEmpty() || introduced.contains(" ") || introduced.equals("%")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Existential iDestruct expects one proof-mode name",
          contextData.getMarker()));
      return null;
    }
    if (!introduced.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), introduced)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + introduced + "'",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    ExistEvidence evidence = explicitFamily == null ? null
        : existEvidence(typechecker, contextData, explicitFamily);
    boolean useUniverseOne = evidence != null ? evidence.universeOne() : universeOne;
    if (evidence != null && resolved.persistent() && useUniverseOne) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Set1 existential evidence is not supported in the intuitionistic context",
          contextData.getMarker()));
      return null;
    }
    CoreExpression carrier = evidence != null ? evidence.carrier() : exists == null ? null
        : exists.getDefCallArguments().get(exists.getDefCallArguments().size() - 2);
    CoreExpression family = evidence != null ? evidence.family() : exists == null ? null
        : exists.getDefCallArguments().getLast();
    ConcreteExpression into;
    if (evidence == null) {
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      into = factory.app(factory.ref(entailmentRefl), reflArgs);
    } else {
      into = evidence.term();
    }
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced), true));
    args.add(factory.arg(carrier == null ? factory.hole()
        : factory.core(carrier.computeTyped()), false));
    args.add(factory.arg(evidence == null && explicitFamily != null ? explicitFamily : family == null
        ? factory.hole() : factory.core(family.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(continuation, true));
    ArendRef lemma = resolved.persistent()
        ? evidence == null ? pmDestructExistIntuitionistic
            : pmDestructIntoExistIntuitionistic
        : useUniverseOne
            ? evidence == null ? pmDestructExist1 : pmDestructIntoExist1
            : evidence == null ? pmDestructExist : pmDestructIntoExist;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructPure(ExpressionTypechecker typechecker,
      ContextData contextData, ResolvedSelection resolved,
      CoreExpression proposition, @Nullable CoreFunCallExpression pure,
      String pattern, @Nullable ConcreteExpression explicitFact,
      ConcreteExpression continuation) {
    if (explicitArguments(contextData).size() > 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure iDestruct accepts at most one explicit fact",
          contextData.getMarker()));
      return null;
    }
    if (!pattern.equals("%")) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Pure iDestruct expects the '%' pattern", contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    PureEvidence evidence = explicitFact == null ? null
        : pureEvidence(typechecker, contextData, explicitFact);
    CoreExpression fact = evidence != null ? evidence.fact() : pure == null
        ? null : pure.getDefCallArguments().getLast();
    ConcreteExpression into;
    if (evidence == null) {
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      into = factory.app(factory.ref(entailmentRefl), reflArgs);
    } else {
      into = evidence.term();
    }
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(evidence == null && explicitFact != null ? explicitFact : fact == null
        ? factory.hole() : factory.core(fact.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(into, true));
    args.add(factory.arg(continuation, true));
    return typechecker.typecheck(factory.app(factory.ref(evidence == null
            ? pmDestructPure : pmDestructIntoPure), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression destructPersistent(
      ExpressionTypechecker typechecker, ContextData contextData,
      String requested, String introducedPattern) {
    String[] introduced = introducedPattern.trim().split("\\s+");
    if (introduced.length < 1 || introduced.length > 2
        || introduced[0].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Persistent iDestruct expects one persistent name and an optional spatial-copy name after '#'",
          contextData.getMarker()));
      return null;
    }
    String persistentName = introduced[0];
    String copyName = introduced.length == 2 ? introduced[1] : null;
    if (copyName != null && (copyName.isEmpty()
        || copyName.equals(persistentName))) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Persistent and spatial-copy names must be distinct",
          contextData.getMarker()));
      return null;
    }
    ResolvedSelection resolved = resolveNamed(typechecker, contextData, requested);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "The hypothesis '" + requested + "' is already intuitionistic",
          contextData.getMarker()));
      return null;
    }
    if (!persistentName.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), persistentName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + persistentName + "'",
          contextData.getMarker()));
      return null;
    }
    if (copyName != null && !copyName.equals(requested)
        && environmentContainsName(typechecker, resolved.environment(), copyName)) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Duplicate proof-mode hypothesis name '" + copyName + "'",
          contextData.getMarker()));
      return null;
    }
    var factory = contextData.getFactory();
    var explicit = explicitArguments(contextData);
    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    CoreExpression body = null;
    ConcreteExpression persistent;
    boolean classEvidence = false;
    if (explicit.size() == 4) {
      ClassEvidence evidence = tryClassEvidence(typechecker, contextData,
          explicit.get(2), pmIntoPersistent);
      if (evidence != null) {
        body = classField(evidence, "Q");
        if (body == null) {
          typechecker.getErrorReporter().report(new TypecheckingError(
              "Cannot inspect PMIntoPersistent evidence",
              contextData.getMarker()));
          return null;
        }
        persistent = evidence.term();
        classEvidence = true;
      } else {
        TypedExpression typedPersistent = typechecker.typecheck(explicit.get(2), null);
        if (typedPersistent == null) return null;
        CoreExpression persistentType = weakHead(typechecker,
            typedPersistent.getType());
        if (!(persistentType instanceof CoreFunCallExpression entailment)
            || !entailment.getDefinition().getName().equals("properUPred_ent")
            || entailment.getDefCallArguments().size() < 3) {
          typechecker.getErrorReporter().report(new TypecheckingError(
              "Explicit persistence rule must be an entailment or PMIntoPersistent evidence",
              contextData.getMarker()));
          return null;
        }
        CoreExpression conclusion = weakHead(typechecker,
            entailment.getDefCallArguments().getLast());
        if (!(conclusion instanceof CoreFunCallExpression persistently)
            || !persistently.getDefinition().getName().equals(mkProperPersistently.getName())
            || persistently.getDefCallArguments().size() < 2) {
          typechecker.getErrorReporter().report(new TypecheckingError(
              "Explicit persistence rule must conclude a persistently proposition",
              contextData.getMarker()));
          return null;
        }
        body = persistently.getDefCallArguments().getLast();
        persistent = factory.core(typedPersistent);
      }
    } else {
      if (!(proposition instanceof CoreFunCallExpression persistently)
          || !persistently.getDefinition().getName().equals(mkProperPersistently.getName())
          || persistently.getDefCallArguments().size() < 2) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Persistent iDestruct expected a persistently proposition or an explicit persistence rule",
            contextData.getMarker()));
        return null;
      }
      body = persistently.getDefCallArguments().getLast();
      var reflArgs = new ArrayList<ConcreteArgument>();
      reflArgs.add(factory.arg(factory.hole(), false));
      reflArgs.add(factory.arg(factory.core(proposition.computeTyped()), true));
      persistent = factory.app(factory.ref(entailmentRefl), reflArgs);
    }

    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, persistentName), true));
    if (copyName != null) {
      args.add(factory.arg(name(contextData, copyName), true));
    }
    args.add(factory.arg(body == null ? factory.hole()
        : factory.core(body.computeTyped()), false));
    args.add(factory.arg(factory.core(resolved.target().computeTyped()), false));
    args.add(factory.arg(persistent, true));
    args.add(factory.arg(explicit.getLast(), true));
    ArendRef lemma = copyName == null
        ? classEvidence ? pmDestructIntoPersistent : pmDestructPersistent
        : classEvidence ? pmDestructIntoPersistentCopy : pmDestructPersistentCopy;
    return typechecker.typecheck(factory.app(factory.ref(lemma), args),
        contextData.getExpectedType());
  }
}
