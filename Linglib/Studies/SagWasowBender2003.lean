import Linglib.Syntax.HPSG.Coreference
import Linglib.Syntax.HPSG.Binding
import Linglib.Syntax.HPSG.HeadFiller
import Linglib.Syntax.HPSG.Construction
import Linglib.Studies.Chomsky1981
import Linglib.Studies.Ross1967
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Features.MinimalPairs

/-!
# Sag, Wasow & Bender (2003) — Syntactic Theory: A Formal Introduction
[sag-wasow-bender-2003] [chomsky-1981] [pollard-sag-1994] [hofmeister-sag-2010]

Consolidated study of three strands of the HPSG textbook *Syntactic Theory: A Formal Introduction*
(2nd ed.):

- **Binding Theory** (Ch. 7) — the `MODE`-based reduction of the Chomskyan three-way
  anaphor/pronoun/R-expression classification (Principles A/B/C) to two ARG-ST outranking principles,
  verified against the [chomsky-1981] minimal-pair paradigm (`Studies/Chomsky1981`) via the
  `Features.MinimalPairs` vocabulary. Implementation: `Syntax/HPSG/Coreference`.
- **Long-Distance Dependencies** (Ch. 15) — the Head-Filler Schema and the list-valued `GAP`/SLASH
  mechanism, with the island taxonomy of `Studies/Ross1967` mapped to GAP restrictions, and the
  island-blocking grounded **model-theoretically** in the RSRL gap-list (the canonical
  `Syntax/HPSG/Construction` signature).
- **Relative Clauses** — a relative clause modifies a head noun via the Head-Modifier Schema, grounded
  **model-theoretically** in the RSRL `head-modifier-cxt` (the canonical `Syntax/HPSG/Construction`
  signature); category preservation falls out of the Head Feature Principle.
-/

namespace SagWasowBender2003

/-! ### Binding Theory (Ch. 7)

The HPSG binding theory reduces the Chomskyan three-way classification (anaphor / pronoun /
R-expression → Principles A/B/C) to two `MODE`-based ARG-ST principles:

- **Principle A**: `[MODE ana]` must be outranked on ARG-ST by a coindexed element;
- **Principle B**: `[MODE ref]` must NOT be outranked on ARG-ST by a coindexed element.

Both pronouns and R-expressions are `[MODE ref]`, so Principle B subsumes Principle C. -/

section Binding

open Features.MinimalPairs
open HPSG.Coreference
open Chomsky1981 (reflexiveCoreferenceData pronominalDisjointReferenceData
  complementaryDistributionData reciprocalCoreferenceData)

/-- English binding under HPSG (ARG-ST outranking): the framework-neutral engine
    (`Binding.grammaticalForCoreference`) applied with HPSG's `CommandRelation`
    instance (in scope via `open HPSG.Coreference`) and English's binding-class
    classifier. `Bool`-valued for `capturesPhenomenonData`. -/
private def grammaticalForCoreference (ws : List Word) : Bool :=
  decide (Binding.grammaticalForCoreference Binding.bindingClassOf ws)

/-- Coverage of a `PhenomenonData` set under HPSG binding. -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  capturesPhenomenonData grammaticalForCoreference phenom

/-- HPSG captures `reflexiveCoreferenceData`. -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  decide

/-- HPSG captures `complementaryDistributionData`. -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  decide

/-- HPSG captures `pronominalDisjointReferenceData`. -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
  decide

private abbrev john := English.Nouns.john.toWordSg
private abbrev mary := English.Nouns.mary.toWordSg
private abbrev they := English.Pronouns.they.toWord
private abbrev sees := English.Predicates.Verbal.see.toWord3sg
private abbrev see := English.Predicates.Verbal.see.toWordPl
private abbrev himself := English.Pronouns.himself.toWord
private abbrev herself := English.Pronouns.herself.toWord
private abbrev themselves := English.Pronouns.themselves.toWord
private abbrev them := English.Pronouns.them.toWord
private abbrev eachOther := English.Pronouns.eachOther.toWord

/-- Per-pair verification of reflexive binding judgments. -/
theorem reflexive_pairs_captured :
    -- Pair 1: john sees himself vs himself sees john
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [himself, sees, john] = false) ∧
    -- Pair 2: mary sees herself vs herself sees mary
    (grammaticalForCoreference [mary, sees, herself] = true ∧
     grammaticalForCoreference [herself, sees, mary] = false) ∧
    -- Pair 3: they see themselves vs themselves see them
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [themselves, see, them] = false) ∧
    -- Pair 4: agreement - john sees himself vs john sees herself
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [john, sees, herself] = false) ∧
    -- Pair 5: agreement - they see themselves vs they see himself
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [they, see, himself] = false) := by
  decide

/-- Reciprocal binding: plural antecedent required, singular blocked.
    (Pairs 1–2 of `reciprocalCoreferenceData` use 5-word coordinated
    sentences that exceed the simple clause parser.) -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] = true ∧
    grammaticalForCoreference [john, sees, eachOther] = false := by
  decide

/-! #### Model-theoretic grounding (RSRL Principles A/B)

The ARG-ST outranking judgments above are the parser-facing shadow of the **model-theoretic** Binding
Theory (`Syntax/HPSG/Binding`): Principles A and B as RSRL descriptions (`Desc`) over a sort hierarchy
of anaphors/pronouns/indices with a local-o-command relation. The two formalizations — computational
ARG-ST outranking here, model-theoretic `Models` there — agree on the diagnostic cases. -/

/-- The reflexive (Principle A) judgments are grounded in the RSRL model theory: the computational
ARG-ST account (a coindexed reflexive object is bound, a reflexive subject is not) and the RSRL
Principle-A model (a coindexed, φ-agreeing anaphor satisfies the grammar; a disjoint one violates it)
agree. -/
theorem reflexive_binding_grounded_in_rsrl :
    grammaticalForCoreference [john, sees, himself] = true ∧
    grammaticalForCoreference [himself, sees, john] = false ∧
    (_root_.HPSG.RSRL.Binding.clause .ana .iSubj .gMasc .nSing).Models
      _root_.HPSG.RSRL.Binding.bindingGrammar ∧
    ¬ (_root_.HPSG.RSRL.Binding.clause .ana .iObj .gMasc .nSing).Models
      [_root_.HPSG.RSRL.Binding.principleA] := by
  decide

/-- Principle B grounded in RSRL: a coindexed personal pronoun violates the model-theoretic
Principle B (a pronoun must be locally o-free), the counterpart of the ARG-ST disjoint-reference data. -/
theorem pronoun_binding_grounded_in_rsrl :
    ¬ (_root_.HPSG.RSRL.Binding.clause .ppro .iSubj .gMasc .nSing).Models
      [_root_.HPSG.RSRL.Binding.principleB] := by
  decide

/-- **φ-agreement grounded in RSRL.** The gender/number agreement of binding (the `Word.Agree` check in
the computational engine) is the model-theoretic requirement that the bound anaphor's `GEND`/`NUM` are
token-identical to the binder's: a *coindexed but φ-clashing* anaphor (feminine — *John likes herself*;
or plural — *they like himself*) is not locally o-bound, violating Principle A. -/
theorem agreement_binding_grounded_in_rsrl :
    ¬ (_root_.HPSG.RSRL.Binding.clause .ana .iSubj .gFem .nSing).Models
      [_root_.HPSG.RSRL.Binding.principleA] ∧
    ¬ (_root_.HPSG.RSRL.Binding.clause .ana .iSubj .gMasc .nPlur).Models
      [_root_.HPSG.RSRL.Binding.principleA] := by
  decide

end Binding

/-! ### Long-Distance Dependencies: extraction and islands (Ch. 15)

The Head-Filler Schema and SLASH mechanism. The empirical island taxonomy is stated **model-
theoretically** over the canonical RSRL signature (`islands_rsrl_grounded` below), which subsumes the
former coarse `GapRestriction` enum — a dependency penetrates a domain iff its `GAP` survives
amalgamation. -/

section Extraction

open HPSG

/-- The gap introduction mechanism correctly removes complements. -/
theorem gap_removes_complement :
    let see_ss : Synsem := { cat := .VERB, val := { subj := [.NOUN], comps := [.NOUN] } }
    let see_w : Word := { form :="see", cat := .VERB, features := {}}
    (gapComplement see_w see_ss 0).map
      (fun p => p.1.synsem.val.comps.isEmpty && p.2.gaps == [.NOUN]) = some true := by
  decide

/-! #### Long-distance dependencies in the RSRL model theory — the full island taxonomy

Extraction licensing is stated directly over the **model-theoretic** RSRL list-valued `GAP`
(the canonical `Syntax/HPSG/Construction` signature): filler-gap category matching is gap amalgamation,
and island permeability is the island/weak-island principles. The whole taxonomy is *derived* from
amalgamation ([sag-2010] (67); after [bouma-malouf-sag-2001]), not stipulated as Subjacency — a
dependency penetrates a domain iff its `GAP` survives amalgamation. -/

/-- The island taxonomy as RSRL `Models` facts (the three cases of the now-retired coarse
`GapRestriction` enum: unrestricted / absolute / weak). A free filler-head construct licenses
extraction; an absolute island (`[GAP ⟨⟩]`) blocks a second gap; a weak island lets an NP gap pass but
blocks a PP gap — each over the canonical construction grammar. -/
theorem islands_rsrl_grounded :
    Construction.goodTwoGap.Models Construction.grammar ∧
    ¬ Construction.islandTwoGap.Models Construction.grammar ∧
    Construction.weakIslandNPGap.Models Construction.grammar ∧
    ¬ Construction.weakIslandPPGap.Models Construction.grammar := by decide

end Extraction

/-! ### Relative Clauses (Ch. 14)

SWB2003 defers relative-clause analysis ("beyond the scope of this text", p. 442). The standard HPSG
treatment — a relative clause is a filler-gap construct that modifies a head noun via the Head-Modifier
Schema — is grounded **model-theoretically** in the canonical RSRL signature (`Syntax/HPSG/Construction`:
`head-modifier-cxt` for the modification, `wh-rel-cl` for the clause-internal gap). The relativizer
inventory and the Keenan–Comrie accessibility-hierarchy typology live, framework-neutrally, in
`Fragments/English/Relativization` and `Typology/RelativeClause`, not here. -/

section RelativeClauses

/-- **Model-theoretic grounding (RSRL head-modifier).** The relative-clause head-modification above is
grounded in the canonical RSRL signature (`Syntax/HPSG/Construction`'s `head-modifier-cxt`): a relative
clause whose `MOD` value selects the noun head is licensed and the mother is a noun (modification
preserves category — `headModifierPrinciple`); a modifier selecting the wrong category is rejected. -/
theorem relatives_rsrl_grounded :
    HPSG.Construction.goodHeadMod.Models HPSG.Construction.grammar ∧
    ¬ HPSG.Construction.headModWrongCat.Models HPSG.Construction.grammar := by decide

end RelativeClauses

end SagWasowBender2003
