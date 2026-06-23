import Linglib.Syntax.HPSG.Coreference
import Linglib.Syntax.HPSG.HeadFiller
import Linglib.Syntax.HPSG.RelativeClauses
import Linglib.Syntax.HPSG.GapAmalgamation
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
  island-blocking grounded **model-theoretically** in the RSRL gap-list (`Syntax/HPSG/GapAmalgamation`).
- **Relative Clauses** — the `MOD` + Head-Modifier mechanism for object/subject/PP relatives
  (`Syntax/HPSG/RelativeClauses`).
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

end Binding

/-! ### Long-Distance Dependencies: extraction and islands (Ch. 15)

The Head-Filler Schema and SLASH mechanism, with the empirical island taxonomy of `Studies/Ross1967`
mapped to GAP feature values. -/

section Extraction

open HPSG

/-- Model of a filler-gap dependency: a wh-filler, a gapped clause,
and an optional island restriction on the embedded domain. -/
structure ExtractionConfig where
  /-- Category of the filler (wh-phrase) -/
  fillerCat : UD.UPOS
  /-- Category of the gap (missing complement) -/
  gapCat : UD.UPOS
  /-- GAP restriction on intervening domain (if any) -/
  restriction : GapRestriction := .unrestricted

/-- Is extraction licensed under HPSG?

1. The filler's category must be compatible with the gap
2. The SLASH value must survive any island restrictions -/
def extractionLicensed (cfg : ExtractionConfig) : Bool :=
  -- The filler must match the gap
  categoriesMatch cfg.fillerCat cfg.gapCat &&
  -- SLASH must survive island restrictions
  (propagateSlash ⟨[cfg.gapCat]⟩ cfg.restriction).isEmpty == false

/-- Object wh-question: "What did John see ___?"
NP gap, NP filler, no island → licensed. -/
def objectWhQuestion : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .unrestricted }

/-- Subject wh-question: "Who saw Mary?"
In HPSG, subject questions don't need extraction — the wh-word IS the
subject. But we can model it as NP gap + NP filler for uniformity. -/
def subjectWhQuestion : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .unrestricted }

-- Object and subject extraction are both licensed
example : extractionLicensed objectWhQuestion = true := rfl
example : extractionLicensed subjectWhQuestion = true := rfl

/-- Extraction from an embedded question (wh-island): blocked.
"*What did John wonder who saw ___?" -/
def whIslandExtraction : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .noGap }

/-- Extraction from a topicalized clause: blocked.
"*What did this book, John read ___?" -/
def topicIslandExtraction : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .noGap }

-- Island extractions are blocked
example : extractionLicensed whIslandExtraction = false := rfl
example : extractionLicensed topicIslandExtraction = false := rfl

/-- NP extraction from a weak island: allowed.
"Which employee did Albert learn whether they dismissed ___?" -/
def weakIslandNP : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .npOnly }

/-- PP extraction from a weak island: blocked.
"*In which city did you wonder whether John lives ___?" -/
def weakIslandPP : ExtractionConfig :=
  { fillerCat := .ADP, gapCat := .ADP, restriction := .npOnly }

-- NP extraction from weak island: ok; PP extraction: blocked
example : extractionLicensed weakIslandNP = true := rfl
example : extractionLicensed weakIslandPP = false := rfl

/-- Map island constraint types to HPSG GAP restrictions.

This is the key connection: empirical island classifications map to
specific GAP feature values in HPSG. -/
def islandToGapRestriction : ConstraintType → GapRestriction
  | .embeddedQuestion  => .noGap     -- absolute barrier (but see weak island analysis)
  | .complexNP         => .noGap     -- absolute barrier
  | .adjunct           => .noGap     -- absolute barrier
  | .coordinate        => .noGap     -- absolute barrier
  | .subject           => .npOnly    -- weak: some NP extraction ok
  | .sententialSubject => .noGap     -- absolute barrier
  | .mannerOfSpeaking  => .npOnly    -- weak: ameliorable with focus
  | .definiteNominal   => .npOnly    -- weak: ameliorated by VOCs ([shen-huang-2026])

/-- HPSG predicts all absolute islands block extraction. -/
theorem absolute_islands_block :
    let cnpc : ExtractionConfig := ⟨.PRON, .NOUN, islandToGapRestriction .complexNP⟩
    let adj : ExtractionConfig := ⟨.PRON, .NOUN, islandToGapRestriction .adjunct⟩
    let coord : ExtractionConfig := ⟨.PRON, .NOUN, islandToGapRestriction .coordinate⟩
    extractionLicensed cnpc = false ∧
    extractionLicensed adj = false ∧
    extractionLicensed coord = false := by
  decide

/-- The gap introduction mechanism correctly removes complements. -/
theorem gap_removes_complement :
    let see_ss : Synsem := { cat := .VERB, val := { subj := [.NOUN], comps := [.NOUN] } }
    let see_w : Word := { form :="see", cat := .VERB, features := {}}
    (gapComplement see_w see_ss 0).map
      (fun p => p.1.synsem.val.comps.isEmpty && p.2.gaps == [.NOUN]) = some true := by
  decide

/-- End-to-end: extraction is licensed iff not blocked by an island. -/
theorem extraction_and_island_complementary :
    let free : ExtractionConfig := ⟨.PRON, .NOUN, .unrestricted⟩  -- no island → licensed
    let abs  : ExtractionConfig := ⟨.PRON, .NOUN, .noGap⟩         -- absolute island → blocked
    let weakNP : ExtractionConfig := ⟨.PRON, .NOUN, .npOnly⟩      -- weak island + NP → licensed
    let weakPP : ExtractionConfig := ⟨.ADP, .ADP, .npOnly⟩        -- weak island + PP → blocked
    extractionLicensed free = true ∧
    extractionLicensed abs = false ∧
    extractionLicensed weakNP = true ∧
    extractionLicensed weakPP = false := by
  decide

/-! #### Model-theoretic grounding (RSRL)

The computational island-blocking above (`extractionLicensed = false` for an island-restricted
configuration) is the parser-facing shadow of a **model-theoretic** result on the RSRL list-valued
`GAP` (`Syntax/HPSG/GapAmalgamation`): a second gap cannot penetrate a `[GAP ⟨⟩]` construct, derived
from amalgamation ([sag-2010] (67)), not stipulated as Subjacency. -/

/-- The absolute-island blocking is grounded in the RSRL model theory: an island construct with a
second un-bound gap is rejected by the gap-amalgamation grammar (`GapAmalgamation.islandTwoGap`). -/
theorem absolute_island_rsrl_grounded :
    ¬ HPSG.GapAmalgamation.islandTwoGap.Models HPSG.GapAmalgamation.gGrammar := by decide

end Extraction

/-! ### Relative Clauses

The `MOD` feature + SLASH/GAP + Head-Modifier Schema for object/subject/PP relatives
([sag-wasow-bender-2003]; [pollard-sag-1994]). -/

section RelativeClauses

open HPSG
open HPSG.RelativeClauses

/-- Configuration for a relative clause dependency. -/
structure RelClauseConfig where
  /-- Category of the head noun being modified -/
  headCat : UD.UPOS
  /-- Category of the gap inside the clause -/
  gapCat : UD.UPOS
  /-- The relativizer used -/
  rel : Relativizer

/-- Is this relative clause configuration licensed?

A relative clause is licensed when:
1. There is a gap in the clause (modeled by gapCat)
2. The relativizer produces a modifier for the head noun's category
3. The MOD value matches the head noun -/
def relClauseLicensed (cfg : RelClauseConfig) : Bool :=
  -- The relativizer must target the right category
  categoriesMatch cfg.rel.modifiesCat cfg.headCat &&
  -- There must be a gap to fill
  cfg.gapCat != .X

/-- Object relative with "that": "the book that John read ___"
NP head, NP gap in object position, "that" relativizer. -/
def objectRelThat : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relThat }

/-- Object relative with "which": "the book which John read ___" -/
def objectRelWhich : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relWhich }

/-- Subject relative with "who": "the boy who saw Mary"
NP head, NP gap in subject position, "who" relativizer. -/
def subjectRelWho : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relWho }

/-- Subject relative with "that": "the boy that saw Mary" -/
def subjectRelThat : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relThat }

/-- PP relative: "the person who(m) John talked to ___"
NP head, PP gap (prep stranded), "who" relativizer. -/
def ppRelWho : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .ADP, rel := relWho }

-- PP relatives are licensed (gap is PP but head is still NP); object/subject relatives are covered by
-- `object_relative_licensed`/`subject_relative_licensed` below.
example : relClauseLicensed ppRelWho = true := by decide

/-- Object relative clause data matches HPSG derivation.

  "the book that John reads" ✓
is licensed by the HPSG derivation:
  gap(read, obj) → S[GAP ⟨NP⟩] → that + S[GAP ⟨NP⟩] → [MOD NP]
  → book + [MOD NP] → NP -/
theorem object_relative_licensed :
    relClauseLicensed objectRelThat = true ∧
    relClauseLicensed objectRelWhich = true := by
  decide

/-- Subject relative clause data matches HPSG derivation.

The empirical observation:
  "the boy that sees Mary" ✓
is licensed by the HPSG derivation:
  gap(see, subj) → S[GAP ⟨NP⟩] → that + S[GAP ⟨NP⟩] → [MOD NP]
  → boy + [MOD NP] → NP -/
theorem subject_relative_licensed :
    relClauseLicensed subjectRelWho = true ∧
    relClauseLicensed subjectRelThat = true := by
  decide

/-- Every relative clause derivation produces a modifier (has MOD set). -/
theorem relClause_always_modifies (d : RelClauseDerivation) :
    d.result.sign.synsem.mod.isSome = true := by
  simp [RelClauseDerivation.result, Sign.synsem]

/-- The Head-Modifier Schema preserves the head noun's category.

This is the Head Feature Principle applied to Head-Modifier structures:
when a relative clause modifies a noun, the result is still a noun. -/
theorem modification_preserves_head_cat (headNoun : Sign)
    (relClause : TrackedSign) (result : Sign)
    (hMod : relClauseModifies headNoun relClause = some result) :
    result.synsem.cat = headNoun.synsem.cat :=
  headMod_preserves_cat headNoun relClause result hMod

end RelativeClauses

end SagWasowBender2003
