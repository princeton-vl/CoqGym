CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  lib GeneralLogic MinimunLogic PropositionalLogic ModalLogic SeparationLogic \
  QuantifierLogic Extensions HoareLogic

INCLUDE_DEMO = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_DIR) Logic
DEP_FLAG = $(DEP_DEMO) 

lib_FILES = \
  Coqlib.v Ensembles_ext.v EnsemblesProperties.v Relation_ext.v Equivalence_ext.v List_Func_ext.v \
  Bijection.v Countable.v NatChoice.v StrongInduction.v \
  Bisimulation.v RelationPairs_ext.v \
  SublistT.v \
  Stream/SigStream.v Stream/StreamFunctions.v Stream/StreamSplit.v 

GeneralLogic_ProofTheory_FILES = \
  BasicSequentCalculus.v TheoryOfSequentCalculus.v

GeneralLogic_Semantics_FILES = \
  Kripke.v

GeneralLogic_Complete_FILES = \
  ContextProperty_Trivial.v ContextProperty_Kripke.v ContextProperty.v \
  Canonical_Kripke.v \
  Lindenbaum.v Lindenbaum_Kripke.v \
  Complete_Kripke.v 

GeneralLogic_ShallowEmbedded_FILES = \
  PredicateAsLang.v MonoPredicateAsLang.v

GeneralLogic_FILES = \
  Base.v HenkinCompleteness.v \
  KripkeModel.v \
  $(GeneralLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(GeneralLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(GeneralLogic_Complete_FILES:%.v=Complete/%.v) \
  $(GeneralLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

MinimunLogic_ProofTheory_FILES = \
  Minimun.v ProofTheoryPatterns.v \
  RewriteClass.v TheoryOfSequentCalculus.v

MinimunLogic_Semantics_FILES = \
  Kripke.v Trivial.v SemanticEquiv.v

MinimunLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

MinimunLogic_Complete_FILES = \
  ContextProperty_Kripke.v Lindenbaum_Kripke.v Truth_Kripke.v

MinimunLogic_ShallowEmbedded_FILES = \

MinimunLogic_DeepEmbedded_FILES = \
  MinimunLanguage.v KripkeSemantics.v MinimunLogic.v \
  Complete_Kripke.v Soundness.v

MinimunLogic_FILES = \
  Syntax.v \
  $(MinimunLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(MinimunLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(MinimunLogic_Sound_FILES:%.v=Sound/%.v) \
  $(MinimunLogic_Complete_FILES:%.v=Complete/%.v) \
  $(MinimunLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v)

PropositionalLogic_ProofTheory_FILES = \
  Intuitionistic.v DeMorgan.v \
  GodelDummett.v Classical.v \
  RewriteClass.v ProofTheoryPatterns.v

PropositionalLogic_Semantics_FILES = \
  Kripke.v Trivial.v

PropositionalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

PropositionalLogic_Complete_FILES = \
  ContextProperty_Kripke.v \
  Lindenbaum_Kripke.v Canonical_Kripke.v Truth_Kripke.v \
  ContextProperty_Trivial.v \
  Lindenbaum_Trivial.v Truth_Trivial.v Complete_Trivial.v

PropositionalLogic_DeepEmbedded_FILES = \
  PropositionalLanguage.v ProofTheories.v \
  KripkeSemantics.v TrivialSemantics.v \
  Soundness.v Complete_Kripke.v Complete_Classical_Trivial.v

PropositionalLogic_ShallowEmbedded_FILES = \
  PredicatePropositionalLogic.v \
  MonoPredicatePropositionalLogic.v

PropositionalLogic_FILES = \
  Syntax.v\
  $(PropositionalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(PropositionalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(PropositionalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(PropositionalLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(PropositionalLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v) \
  $(PropositionalLogic_Complete_FILES:%.v=Complete/%.v)

ModalLogic_ProofTheory_FILES = \
  ModalLogic.v RewriteClass.v \
  ClassicalDerivedRules.v IntuitionisticDerivedRules.v

ModalLogic_Model_FILES = \
  KripkeModel.v OrderedKripkeModel.v

ModalLogic_Semantics_FILES = \
  Kripke.v Flat.v

ModalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Flat.v

ModalLogic_ShallowEmbedded_FILES = \
  PredicateModalLogic.v \
  MonoPredicateModalLogic.v

ModalLogic_FILES = \
  Syntax.v \
  $(ModalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(ModalLogic_Model_FILES:%.v=Model/%.v) \
  $(ModalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(ModalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(ModalLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

QuantifierLogic_ProofTheory_FILES = \
  QuantifierLogic.v

QuantifierLogic_DeepEmbedded_FILES = \
  FirstOrderLanguage.v FirstOrderLogic.v

QuantifierLogic_ShallowEmbedded_FILES = \
  PredicateAsBLang.v PredicateQuantifierLogic.v

QuantifierLogic_FILES = \
  Syntax.v \
  $(QuantifierLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(QuantifierLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(QuantifierLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

SeparationLogic_ProofTheory_FILES = \
  SeparationLogic.v SeparationLogicExtension.v \
  RewriteClass.v DerivedRules.v IterSepcon.v WandFrame.v

SeparationLogic_Model_FILES = \
  SeparationAlgebra.v OrderedSA.v \
  UpwardsClosure.v DownwardsClosure.v \
  OSAGenerators.v OSAExamples.v

SeparationLogic_Semantics_FILES = \
  WeakSemantics.v StrongSemantics.v \
  UpwardsSemantics.v DownwardsSemantics.v FlatSemantics.v \
  DownUpSemantics_Fail.v \
  Down2Flat.v Up2Flat.v \
  SemanticsExtension.v

SeparationLogic_Sound_FILES = \
  Sound_Downwards.v Sound_Upwards.v Sound_Flat.v \
  Sound_DownUp_Fail.v

SeparationLogic_Complete_FILES = \
  ContextProperty_Flat.v \
  Lindenbaum_Flat.v Truth_Flat.v Canonical_Flat.v

SeparationLogic_DeepEmbedded_FILES = \
  SeparationLanguage.v SeparationEmpLanguage.v \
  Parameter.v \
  ParametricSeparationLogic.v SeparationLogicsInLiteratures.v \
  FlatSemantics.v ParametricCompleteness.v

SeparationLogic_ShallowEmbedded_FILES = \
  PredicateSeparationLogic.v MonoPredicateSeparationLogic.v

SeparationLogic_FILES = \
  Syntax.v \
  $(SeparationLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(SeparationLogic_Model_FILES:%.v=Model/%.v) \
  $(SeparationLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(SeparationLogic_Sound_FILES:%.v=Sound/%.v) \
  $(SeparationLogic_Complete_FILES:%.v=Complete/%.v) \
  $(SeparationLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(SeparationLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

Extentions_ProofTheory_FILES = \
  Stable.v ModalSeparation.v Corable.v CoreTransit.v

Extentions_Semantics_FILES = \
  SemanticStable.v

Extentions_Sound_FILES = \
  StableSound.v

Extentions_ShallowEmbedded_FILES = \
  MonoPredicateStable.v

Extentions_FILES = \
  Syntax_CoreTransit.v \
  $(Extentions_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(Extentions_Semantics_FILES:%.v=Semantics/%.v) \
  $(Extentions_Sound_FILES:%.v=Sound/%.v) \
  $(Extentions_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

HoareLogic_FILES = \
  ImperativeLanguage.v ProgramState.v Trace.v \
  SimpleSmallStepSemantics.v SmallStepSemantics.v \
  BigStepSemantics.v ConcurrentSemantics_Angelic.v \
  TraceSemantics.v \
  OperationalSemanticsGenerator.v \
  HoareLogic.v GuardedHoareLogic.v \
  HoareTriple_BigStepSemantics.v GuardedHoareTriple_Angelic.v GuardedHoareTriple_TraceSemantics.v \
  Sound_Basic.v Sound_Imp.v Sound_Frame.v \
  Sound_Resource_Angelic.v Sound_Resource_TraceSemantics.v

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(GeneralLogic_FILES:%.v=GeneralLogic/%.v) \
  $(MinimunLogic_FILES:%.v=MinimunLogic/%.v) \
  $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.v) \
  $(ModalLogic_FILES:%.v=ModalLogic/%.v) \
  $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.v) \
  $(SeparationLogic_FILES:%.v=SeparationLogic/%.v) \
  $(Extentions_FILES:%.v=Extensions/%.v) \
  $(HoareLogic_FILES:%.v=HoareLogic/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

lib: \
  .depend $(lib_FILES:%.v=lib/%.vo)

GeneralLogic: \
  .depend $(GeneralLogic_FILES:%.v=GeneralLogic/%.vo)

MinimunLogic: \
  .depend $(MinimunLogic_FILES:%.v=MinimunLogic/%.vo)

PropositionalLogic: \
  .depend $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.vo)

ModalLogic: \
  .depend $(ModalLogic_FILES:%.v=ModalLogic/%.vo)

QuantifierLogic: \
  .depend $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.vo)

SeparationLogic: \
  .depend $(SeparationLogic_FILES:%.v=SeparationLogic/%.vo)

all: \
  $(FILES:%.v=%.vo) \

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob */*/*.vo */*/*.glob

.DEFAULT_GOAL := all

include .depend


#COQC = coqc
# 
#%.vo: %.v
# 	@echo COQC $*.v
# 	@$(COQC) -q -R "." -as Logic $*.v
# 
#all: 
#     
#     SeparationLogic/Syntax.vo SeparationLogic/SeparationLogic.vo \
#     SeparationLogic/QinxiangSantiagoSemantics.vo
