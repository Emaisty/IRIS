package org.arend.iris.proofmode;

import org.arend.ext.DefaultArendExtension;
import org.arend.ext.DefinitionContributor;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.definition.ConcreteMetaDefinition;
import org.arend.ext.module.ModulePath;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.meta.DependencyMetaTypechecker;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;
import java.util.function.Supplier;

import static org.arend.ext.prettyprinting.doc.DocFactory.text;

public final class ProofModeExtension extends DefaultArendExtension {
  private ConcreteFactory factory;

  @Override
  public void setConcreteFactory(@NotNull ConcreteFactory factory) {
    this.factory = factory;
  }

  private ConcreteMetaDefinition meta(ModulePath module, String name,
      DependencyMetaTypechecker typechecker) {
    MetaRef ref = factory.metaRef(factory.moduleRef(module), name,
        Precedence.DEFAULT, null, null, null, typechecker);
    return factory.metaDef(ref, Collections.emptyList(), typechecker.makeBody(factory));
  }

  private void dependencyMeta(DefinitionContributor contributor, ModulePath module,
      String name, Class<? extends MetaDefinition> container,
      Supplier<MetaDefinition> supplier) {
    contributor.declare(text("IRIS proof-mode tactic `" + name + "`"),
        meta(module, name, new DependencyMetaTypechecker(container, supplier)));
  }

  @Override
  public void declareDefinitions(@NotNull DefinitionContributor contributor) {
    ModulePath module = new ModulePath("iris", "proofmode", "Meta");
    contributor.declare(module, new ModulePath("iris", "proofmode", "core"));
    contributor.declare(module, new ModulePath("iris", "base_logic", "upred"));
    contributor.declare(module, new ModulePath("iris", "bi", "updates"));
    contributor.declare(module, new ModulePath("iris", "base_logic", "lib", "invariants"));
    contributor.declare(module, new ModulePath("stdpp", "namespaces"));
    contributor.declare(module, new ModulePath("iris_heap_lang", "lang"));
    contributor.declare(module, new ModulePath("iris_heap_lang", "lang_ectx"));
    contributor.declare(module, new ModulePath("iris", "program_logic", "lifting"));
    contributor.declare(module, new ModulePath("iris", "proofmode", "heap_lang"));
    contributor.declare(module, new ModulePath("Function", "Meta"));
    contributor.declare(module, new ModulePath("Data", "List"));

    dependencyMeta(contributor, module, "ipm", IpmMeta.class, IpmMeta::new);
    dependencyMeta(contributor, module, "iStopProof", StopMeta.class, StopMeta::new);
    dependencyMeta(contributor, module, "iIntros", IntrosMeta.class, IntrosMeta::new);
    dependencyMeta(contributor, module, "iExact", ExactMeta.class, ExactMeta::new);
    dependencyMeta(contributor, module, "iDestruct", DestructMeta.class, DestructMeta::new);
    dependencyMeta(contributor, module, "iClear", ClearMeta.class, ClearMeta::new);
    dependencyMeta(contributor, module, "iRename", RenameMeta.class, RenameMeta::new);
    dependencyMeta(contributor, module, "iFrame", FrameMeta.class, FrameMeta::new);
    dependencyMeta(contributor, module, "iLeft", LeftMeta.class, LeftMeta::new);
    dependencyMeta(contributor, module, "iRight", RightMeta.class, RightMeta::new);
    dependencyMeta(contributor, module, "iExists", ExistsMeta.class, ExistsMeta::new);
    dependencyMeta(contributor, module, "iPureIntro", PureIntroMeta.class, PureIntroMeta::new);
    dependencyMeta(contributor, module, "iEmpIntro", EmpIntroMeta.class, EmpIntroMeta::new);
    dependencyMeta(contributor, module, "iAssumption", AssumptionMeta.class, AssumptionMeta::new);
    dependencyMeta(contributor, module, "iApply", ApplyWandMeta.class, ApplyWandMeta::new);
    dependencyMeta(contributor, module, "iSpecialize", SpecializeMeta.class, SpecializeMeta::new);
    dependencyMeta(contributor, module, "iSplitL", SplitLeftMeta.class, SplitLeftMeta::new);
    dependencyMeta(contributor, module, "iSplitR", SplitRightMeta.class, SplitRightMeta::new);
    dependencyMeta(contributor, module, "iAssert", AssertMeta.class, AssertMeta::new);
    dependencyMeta(contributor, module, "iPoseProof", AssertMeta.class, AssertMeta::new);
    dependencyMeta(contributor, module, "iNext", NextMeta.class, NextMeta::new);
    dependencyMeta(contributor, module, "iModIntro", ModIntroMeta.class, ModIntroMeta::new);
    dependencyMeta(contributor, module, "iMod", ModMeta.class, ModMeta::new);
    dependencyMeta(contributor, module, "iRewrite", RewriteMeta.class, RewriteMeta::new);
    dependencyMeta(contributor, module, "iLob", LobMeta.class, LobMeta::new);
    dependencyMeta(contributor, module, "iInv", InvMeta.class, InvMeta::new);
    dependencyMeta(contributor, module, "wp_pures", WpPuresMeta.class, WpPuresMeta::new);
    dependencyMeta(contributor, module, "wp_bind", WpBindMeta.class, WpBindMeta::new);
    dependencyMeta(contributor, module, "wp_value", WpValueMeta.class, WpValueMeta::new);
    dependencyMeta(contributor, module, "wp_if", WpIfMeta.class, WpIfMeta::new);
    dependencyMeta(contributor, module, "wp_apply", WpApplyMeta.class, WpApplyMeta::new);
    dependencyMeta(contributor, module, "wp_smart_apply",
        WpSmartApplyMeta.class, WpSmartApplyMeta::new);
    dependencyMeta(contributor, module, "iEval", WpApplyMeta.class, WpApplyMeta::new);
    String[] explicitWpRules = {
        "wp_lam", "wp_rec", "wp_let", "wp_alloc", "wp_allocN",
        "wp_load", "wp_store", "wp_faa", "wp_fork", "wp_new_proph", "wp_resolve"
    };
    for (String name : explicitWpRules) {
      dependencyMeta(contributor, module, name, WpApplyMeta.class, WpApplyMeta::new);
    }
  }
}
