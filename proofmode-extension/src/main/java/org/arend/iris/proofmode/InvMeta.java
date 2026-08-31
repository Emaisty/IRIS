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
import java.util.List;

final class InvMeta extends ExactMeta {
  @Dependency(name = "pm_wp_inv")
  private ArendRef pmWpInv;

  @Dependency(name = "PMIntoInvariant")
  private CoreClassDefinition pmIntoInvariant;

  @Dependency(name = "pm_into_invariant_direct")
  private ArendRef pmIntoInvariantDirect;

  @Dependency(name = "PMIntoAccessor")
  private CoreClassDefinition pmIntoAccessor;

  @Dependency(name = "pm_wp_accessor")
  private ArendRef pmWpAccessor;

  @Dependency(name = "PMTimeless")
  private CoreClassDefinition pmTimeless;

  @Dependency(name = "pm_wp_inv_timeless")
  private ArendRef pmWpInvTimeless;

  @Dependency(name = "inv")
  private CoreFunctionDefinition invariant;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData) {
    List<ConcreteExpression> arguments = explicitArguments(contextData);
    if (arguments.size() < 2 || arguments.size() > 7) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv expects a quoted hypothesis and opening pattern",
          contextData.getMarker()));
      return null;
    }
    String invariantName = stringArgument(typechecker, contextData, 0);
    String pattern = stringArgument(typechecker, contextData, 1);
    if (invariantName == null || pattern == null) return null;
    String[] introduced = pattern.trim().isEmpty()
        ? new String[0] : pattern.trim().split("\\s+");
    boolean timelessPattern = introduced.length > 0
        && introduced[0].startsWith(">");
    if (timelessPattern) introduced[0] = introduced[0].substring(1);
    boolean validCount = timelessPattern
        ? arguments.size() == 6 || arguments.size() == 7
        : arguments.size() == 5 || arguments.size() == 6;
    if (!validCount) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv expects optional PMIntoInvariant evidence, optional "
              + "PMTimeless evidence for a '>H' pattern, a mask proof, "
              + "atomicity proof, and continuation",
          contextData.getMarker()));
      return null;
    }
    if (introduced.length != 2 || introduced[0].equals(introduced[1])
        || introduced[0].isEmpty() || introduced[1].isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv expects two distinct names, for example \"HP Hclose\"",
          contextData.getMarker()));
      return null;
    }

    ResolvedSelection resolved = resolveNamed(typechecker, contextData, invariantName);
    if (resolved == null) return null;
    if (resolved.persistent()) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv currently opens a spatial invariant hypothesis",
          contextData.getMarker()));
      return null;
    }
    for (String name : introduced) {
      if (!name.equals(invariantName)
          && environmentContainsName(typechecker, resolved.environment(), name)) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "A proof-mode hypothesis named '" + name + "' already exists",
            contextData.getMarker()));
        return null;
      }
    }

    boolean withEvidence = arguments.size() == (timelessPattern ? 7 : 6);
    ClassEvidence evidence = withEvidence
        ? classEvidence(typechecker, contextData, arguments.get(2),
            pmIntoInvariant, "PMIntoInvariant") : null;
    if (withEvidence && evidence == null) return null;

    int evidenceOffset = withEvidence ? 1 : 0;
    ClassEvidence timelessEvidence = timelessPattern
        ? classEvidence(typechecker, contextData,
            arguments.get(2 + evidenceOffset), pmTimeless, "PMTimeless")
        : null;
    if (timelessPattern && timelessEvidence == null) return null;

    CoreExpression proposition = weakHead(typechecker,
        resolved.selection().proposition());
    ClassEvidence accessorEvidence = !timelessPattern && arguments.size() == 5
        ? tryClassEvidence(typechecker, contextData, arguments.get(2),
            pmIntoAccessor) : null;

    CoreExpression target = weakHead(typechecker, resolved.target());
    if (!(target instanceof CoreFunCallExpression wpCall)
        || !(wpCall.getDefinition().getName().equals("wp")
          || wpCall.getDefinition().getName().equals("pm_wp"))
        || wpCall.getDefCallArguments().size() < 4) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "iInv requires a weakest-precondition goal", contextData.getMarker()));
      return null;
    }
    var wpArgs = wpCall.getDefCallArguments();
    CoreExpression iris = wpArgs.get(wpArgs.size() - 4);
    CoreExpression mask = wpArgs.get(wpArgs.size() - 3);
    CoreExpression expression = wpArgs.get(wpArgs.size() - 2);
    CoreExpression post = wpArgs.getLast();

    if (accessorEvidence != null) {
      return invokeAccessor(typechecker, contextData, resolved, introduced,
          arguments, accessorEvidence, iris, expression, post);
    }

    CoreExpression world;
    CoreExpression namespace;
    CoreExpression body;
    if (evidence == null) {
      if (!(proposition instanceof CoreFunCallExpression invCall)
          || invCall.getDefinition() != invariant
          || invCall.getDefCallArguments().size() < 3) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "iInv expected an invariant hypothesis or PMIntoInvariant evidence",
            contextData.getMarker()));
        return null;
      }
      var invArgs = invCall.getDefCallArguments();
      world = invArgs.get(invArgs.size() - 3);
      namespace = invArgs.get(invArgs.size() - 2);
      body = invArgs.getLast();
    } else {
      world = classField(evidence, "W");
      namespace = classField(evidence, "N");
      body = classField(evidence, "Q");
      if (classField(evidence, "P") == null || world == null
          || namespace == null || body == null) {
        typechecker.getErrorReporter().report(new TypecheckingError(
            "Cannot inspect PMIntoInvariant evidence", contextData.getMarker()));
        return null;
      }
    }
    if (timelessEvidence != null && classField(timelessEvidence, "P") == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMTimeless evidence", contextData.getMarker()));
      return null;
    }

    var factory = contextData.getFactory();
    ConcreteExpression instance;
    if (evidence != null) {
      instance = evidence.term();
    } else {
      var directArgs = new ArrayList<ConcreteArgument>();
      directArgs.add(factory.arg(factory.hole(), false));
      directArgs.add(factory.arg(factory.core(world.computeTyped()), true));
      directArgs.add(factory.arg(factory.core(namespace.computeTyped()), true));
      directArgs.add(factory.arg(factory.core(body.computeTyped()), true));
      instance = factory.app(factory.ref(pmIntoInvariantDirect), directArgs);
    }

    int timelessOffset = timelessPattern ? 1 : 0;
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(iris.computeTyped()), true));
    args.add(factory.arg(factory.core(mask.computeTyped()), true));
    args.add(factory.arg(factory.core(namespace.computeTyped()), true));
    args.add(factory.arg(factory.core(body.computeTyped()), true));
    args.add(factory.arg(factory.core(expression.computeTyped()), true));
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    args.add(factory.arg(arguments.get(2 + evidenceOffset + timelessOffset), true));
    args.add(factory.arg(arguments.get(3 + evidenceOffset + timelessOffset), true));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced[0]), true));
    args.add(factory.arg(name(contextData, introduced[1]), true));
    args.add(factory.arg(instance, true));
    if (timelessEvidence != null) {
      args.add(factory.arg(timelessEvidence.term(), true));
    }
    args.add(factory.arg(arguments.get(4 + evidenceOffset + timelessOffset), true));
    return typechecker.typecheck(factory.app(factory.ref(
            timelessPattern ? pmWpInvTimeless : pmWpInv), args),
        contextData.getExpectedType());
  }

  private @Nullable TypedExpression invokeAccessor(
      @NotNull ExpressionTypechecker typechecker,
      @NotNull ContextData contextData,
      @NotNull ResolvedSelection resolved,
      @NotNull String[] introduced,
      @NotNull List<ConcreteExpression> arguments,
      @NotNull ClassEvidence evidence,
      @NotNull CoreExpression iris,
      @NotNull CoreExpression expression,
      @NotNull CoreExpression post) {
    CoreExpression world = classField(evidence, "W");
    CoreExpression sourceMask = classField(evidence, "E1");
    CoreExpression targetMask = classField(evidence, "E2");
    CoreExpression body = classField(evidence, "Q");
    CoreExpression close = classField(evidence, "Close");
    if (classField(evidence, "P") == null || world == null
        || sourceMask == null || targetMask == null
        || body == null || close == null) {
      typechecker.getErrorReporter().report(new TypecheckingError(
          "Cannot inspect PMIntoAccessor evidence", contextData.getMarker()));
      return null;
    }

    var factory = contextData.getFactory();
    var args = new ArrayList<ConcreteArgument>();
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.hole(), false));
    args.add(factory.arg(factory.core(iris.computeTyped()), true));
    args.add(factory.arg(factory.core(sourceMask.computeTyped()), true));
    args.add(factory.arg(factory.core(targetMask.computeTyped()), true));
    args.add(factory.arg(factory.core(body.computeTyped()), true));
    args.add(factory.arg(factory.core(close.computeTyped()), true));
    args.add(factory.arg(factory.core(expression.computeTyped()), true));
    args.add(factory.arg(factory.core(post.computeTyped()), true));
    args.add(factory.arg(arguments.get(3), true));
    args.add(factory.arg(factory.core(resolved.environment().computeTyped()), false));
    args.add(factory.arg(resolved.selection().term(), true));
    args.add(factory.arg(name(contextData, introduced[0]), true));
    args.add(factory.arg(name(contextData, introduced[1]), true));
    args.add(factory.arg(evidence.term(), true));
    args.add(factory.arg(arguments.get(4), true));
    return typechecker.typecheck(factory.app(factory.ref(pmWpAccessor), args),
        contextData.getExpectedType());
  }
}
