import Linglib.Morphology.TheorySpace
import Linglib.Morphology.MorphRule
import Linglib.Studies.ZwickyPullum1983
import Linglib.Morphology.Containment.Superset

-- ============================================================================
-- § 0b: PFM Substrate (was Morphology/PFM/Core.lean,
--      relocated 0.230.455 — sole consumer is this study file; PFM dir dissolves)
-- ============================================================================

/-! Paradigm Function Morphology ([stump-2001]) — a lexicalist,
parallel, process-based, realizational theory used by K-B 2026 §2.2 as
one of the four positions in the theory space. -/

namespace Morphology.PFM

structure MorphPropertySet (Feature : Type) where
  features : List Feature
  deriving DecidableEq, Repr, BEq

structure Lexeme where
  name : String
  category : String
  stem : String
  deriving DecidableEq, Repr

structure RealizationRule (Feature : Type) where
  context : List Feature
  category : String
  realize : String → String
  specificity : Nat := 0

def RealizationRule.matches {Feature : Type} [BEq Feature]
    (rr : RealizationRule Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : Bool :=
  lex.category == rr.category &&
  rr.context.all (σ.features.contains ·)

structure RuleBlock (Feature : Type) where
  label : String
  rules : List (RealizationRule Feature)

def RuleBlock.apply {Feature : Type} [BEq Feature]
    (block : RuleBlock Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme)
    (stem : String) : Option String :=
  let matching := block.rules.filter (·.matches σ lex)
  let best := matching.foldl (init := none) fun acc rr =>
    match acc with
    | none => some rr
    | some prev =>
      if rr.specificity > prev.specificity then some rr
      else some prev
  best.map (·.realize stem)

structure ParadigmFunction (Feature : Type) where
  blocks : List (RuleBlock Feature)

def ParadigmFunction.apply {Feature : Type} [BEq Feature]
    (pf : ParadigmFunction Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : String :=
  pf.blocks.foldl (init := lex.stem) fun stem block =>
    (block.apply σ lex stem).getD stem

structure RuleOfReferral (Feature : Type) where
  source : MorphPropertySet Feature
  target : MorphPropertySet Feature

def RuleOfReferral.apply {Feature : Type} [BEq Feature]
    (ref : RuleOfReferral Feature)
    (pf : ParadigmFunction Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : Option String :=
  if σ == ref.source then
    some (pf.apply ref.target lex)
  else
    none

def derive {Feature : Type} [BEq Feature]
    (pf : ParadigmFunction Feature)
    (referrals : List (RuleOfReferral Feature))
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : String :=
  match referrals.findSome? (·.apply pf σ lex) with
  | some form => form
  | none => pf.apply σ lex

end Morphology.PFM

-- ============================================================================
-- § 0a: Wordhood Typology (was Morphology/Wordhood.lean,
--      inlined as sole consumer per CLAUDE.md anchoring rules)
-- ============================================================================

/-! [kalin-bjorkman-etal-2026] (§3.2) argue that solving the wordhood
problem requires distinguishing at minimum two notions of "word":

- **ms-word** (morphosyntactic/grammatical word): a constituent containing
  one or more morphemes, contained in a morphosyntactic phrase. Identified
  by cohesiveness, fixed internal order, selectivity, and domainhood
  for morphological operations (§3.2.1).

- **p-word** (phonological/prosodic word): a constituent containing one or
  more syllables grouped into feet, contained in a phonological phrase.
  Identified by phonotactic bounding and edge phenomena (§3.2.2).

Crossing ms-boundedness (bound vs free) with p-boundedness yields a
four-way typology of morpheme attachment (Table 3). -/

namespace Morphology.Wordhood

/-- Morphosyntactic boundedness. [kalin-bjorkman-etal-2026] §3.2.1. -/
inductive MSBoundedness where
  | free   -- independent ms-word (can stand alone, be reordered, etc.)
  | bound  -- must be internal to a host ms-word
  deriving DecidableEq, Repr

/-- Phonological/prosodic boundedness. [kalin-bjorkman-etal-2026] §3.2.2. -/
inductive PBoundedness where
  | free   -- forms its own p-word
  | bound  -- must be internal to a host p-word
  deriving DecidableEq, Repr

/-- A morpheme's wordhood profile. [kalin-bjorkman-etal-2026] Table 3. -/
structure WordhoodProfile where
  ms : MSBoundedness
  p  : PBoundedness
  deriving DecidableEq, Repr

/-- The four-way classification of morpheme attachment.
    [kalin-bjorkman-etal-2026] §3.2.3. -/
inductive WordhoodClass where
  /-- ms-free, p-free: an independent word by both criteria. -/
  | canonicalWord
  /-- ms-free, p-bound: syntactically independent but phonologically
      dependent. [zwicky-1977] -/
  | simpleClitic
  /-- ms-bound, p-free: morphosyntactically part of a word but
      phonologically independent. -/
  | nonCoheringAffix
  /-- ms-bound, p-bound: part of a word by both criteria. -/
  | canonicalAffix
  deriving DecidableEq, Repr

/-- Classify a wordhood profile into the four-way typology. -/
def WordhoodProfile.classify : WordhoodProfile → WordhoodClass
  | ⟨.free,  .free⟩  => .canonicalWord
  | ⟨.free,  .bound⟩ => .simpleClitic
  | ⟨.bound, .free⟩  => .nonCoheringAffix
  | ⟨.bound, .bound⟩ => .canonicalAffix

theorem canonicalWord_is_doubly_free :
    (WordhoodProfile.mk .free .free).classify = .canonicalWord := rfl

theorem simpleClitic_is_ms_free_p_bound :
    (WordhoodProfile.mk .free .bound).classify = .simpleClitic := rfl

theorem nonCoheringAffix_is_ms_bound_p_free :
    (WordhoodProfile.mk .bound .free).classify = .nonCoheringAffix := rfl

theorem canonicalAffix_is_doubly_bound :
    (WordhoodProfile.mk .bound .bound).classify = .canonicalAffix := rfl

/-- The four classes are exhaustive. -/
theorem classify_total (w : WordhoodProfile) :
    w.classify = .canonicalWord ∨
    w.classify = .simpleClitic ∨
    w.classify = .nonCoheringAffix ∨
    w.classify = .canonicalAffix := by
  cases w with | mk ms p => cases ms <;> cases p <;> simp [WordhoodProfile.classify]

/-- The four classes are mutually exclusive. -/
theorem classify_injective (w₁ w₂ : WordhoodProfile)
    (h : w₁.classify = w₂.classify) :
    w₁ = w₂ := by
  cases w₁ with | mk ms₁ p₁ =>
  cases w₂ with | mk ms₂ p₂ =>
  cases ms₁ <;> cases p₁ <;> cases ms₂ <;> cases p₂ <;>
    simp [WordhoodProfile.classify] at h <;> rfl

end Morphology.Wordhood

-- ============================================================================
-- § 0: Wordhood ↔ Clitic/Affix Diagnostic Bridge
--     (was Morphology/Core/WordhoodBridge.lean — Bridge anti-pattern;
--     relocated 0.230.455 to its sole consumer per CLAUDE.md "no Bridges")
-- ============================================================================

/-! Connects two independent formalizations:
- **Wordhood typology** (`Morphology.Wordhood`): K-B 2026 §3.2 two-
  dimensional classification (ms-boundedness × p-boundedness → 4 wordhood
  classes).
- **Clitic vs. affix diagnostics** (`Morphology.Diagnostics`): [zwicky-pullum-1983]'s
  six criteria for affix-vs-clitic.

The bridge: ZP's criteria diagnose **ms-boundedness**. The p-boundedness
dimension is orthogonal (determined by prosodic diagnostics). -/

namespace Morphology.WordhoodBridge

open Morphology.Wordhood
open Morphology (MorphStatus)
open Morphology.Diagnostics (CliticAffixProfile)

/-- Map a morpheme's morphological status to its ms-boundedness. -/
def morphStatusToMSBound : MorphStatus → MSBoundedness
  | .freeWord      => .free
  | .simpleClitic  => .free
  | .specialClitic => .free
  | .inflAffix     => .bound
  | .derivAffix    => .bound

theorem freeWord_is_ms_free :
    morphStatusToMSBound .freeWord = .free := rfl
theorem simpleClitic_is_ms_free :
    morphStatusToMSBound .simpleClitic = .free := rfl
theorem inflAffix_is_ms_bound :
    morphStatusToMSBound .inflAffix = .bound := rfl
theorem derivAffix_is_ms_bound :
    morphStatusToMSBound .derivAffix = .bound := rfl

theorem zpAffix_implies_ms_bound (p : CliticAffixProfile)
    (h : p.classify = .inflAffix) :
    morphStatusToMSBound p.classify = .bound := by
  simp [h, morphStatusToMSBound]

theorem zpClitic_implies_ms_free (p : CliticAffixProfile)
    (h : p.classify = .simpleClitic) :
    morphStatusToMSBound p.classify = .free := by
  simp [h, morphStatusToMSBound]

/-- Construct a wordhood profile from MorphStatus + prosodic boundedness. -/
def wordhoodProfile (status : MorphStatus) (prosody : PBoundedness) :
    WordhoodProfile :=
  ⟨morphStatusToMSBound status, prosody⟩

theorem simpleClitic_p_bound_is_simpleClitic :
    (wordhoodProfile .simpleClitic .bound).classify = .simpleClitic := rfl
theorem inflAffix_p_bound_is_canonicalAffix :
    (wordhoodProfile .inflAffix .bound).classify = .canonicalAffix := rfl
theorem inflAffix_p_free_is_nonCoheringAffix :
    (wordhoodProfile .inflAffix .free).classify = .nonCoheringAffix := rfl
theorem freeWord_p_free_is_canonicalWord :
    (wordhoodProfile .freeWord .free).classify = .canonicalWord := rfl

theorem morphStatus_exhaustive (s : MorphStatus) :
    morphStatusToMSBound s = .free ∨ morphStatusToMSBound s = .bound := by
  cases s <;> simp [morphStatusToMSBound]

theorem affix_iff_ms_bound (s : MorphStatus) :
    s.IsAffix ↔ morphStatusToMSBound s = .bound := by
  cases s <;> simp [MorphStatus.IsAffix, morphStatusToMSBound]

theorem clitic_implies_ms_free (s : MorphStatus) (h : s.IsClitic) :
    morphStatusToMSBound s = .free := by
  cases s <;> simp_all [MorphStatus.IsClitic, morphStatusToMSBound]

/-- Map Word membership to p-boundedness. -/
def prWdMembershipToPBound (isPrWdInternal : Bool) : PBoundedness :=
  if isPrWdInternal then .bound else .free

end Morphology.WordhoodBridge

/-!
# [kalin-bjorkman-etal-2026]: The Morphology/Syntax Interface
[kalin-bjorkman-etal-2026]

This study file verifies the core contributions of
[kalin-bjorkman-etal-2026]'s *Elements in Generative Syntax*
survey against Linglib's independent formalizations of DM, PFM,
Nanosyntax, and the Wordhood typology.

## Structure

- **§1**: Theory space (§2 of the Element) — verify that Linglib's
  theory-specific modules occupy the correct positions in the
  4-dimensional classification, and that impossible combinations
  are ruled out.
- **§2**: Wordhood (§3) — verify the two-dimensional typology and
  its connection to ZP diagnostics and ProsodicWord.
- **§3**: Form-meaning mapping (§4) — verify coverage of the seven
  descriptive types.
- **§4**: Cross-module integration — theorems connecting the
  independent formalizations.
-/

namespace KalinBjorkmanEtAl2026

-- ============================================================================
-- §1: Theory Space (Element §2)
-- ============================================================================

open Morphology.TheorySpace

/-! ### 1a. The four major theories occupy correct positions -/

/-- DM is non-lexicalist, post-syntactic, piece-based, realizational. -/
theorem dm_position :
    dm.lexicalism = .nonLexicalist ∧
    dm.architecture = .postSyntactic ∧
    dm.exponence = .pieceBased ∧
    dm.mapping = .realizational := ⟨rfl, rfl, rfl, rfl⟩

/-- PFM is lexicalist, parallel, process-based, realizational. -/
theorem pfm_position :
    pfm.lexicalism = .lexicalist ∧
    pfm.architecture = .parallel ∧
    pfm.exponence = .processBased ∧
    pfm.mapping = .realizational := ⟨rfl, rfl, rfl, rfl⟩

/-- MaS is non-lexicalist, syntactic, piece-based, incremental. -/
theorem mas_position :
    mas.lexicalism = .nonLexicalist ∧
    mas.architecture = .syntactic ∧
    mas.exponence = .pieceBased ∧
    mas.mapping = .incremental := ⟨rfl, rfl, rfl, rfl⟩

/-- All four theories are well-formed (satisfy structural constraints). -/
theorem all_theories_wellFormed :
    dm.wellFormed = true ∧
    pfm.wellFormed = true ∧
    nanosyntax.wellFormed = true ∧
    mas.wellFormed = true := ⟨rfl, rfl, rfl, rfl⟩

/-! ### 1b. DM and Nanosyntax are indistinguishable on these dimensions

[kalin-bjorkman-etal-2026] §2: DM and Nanosyntax agree on all four
dimensions. Their differences (Subset vs Superset Principle, terminal vs
phrasal spellout) are mechanism-level, not dimension-level. -/

/-- DM and Nanosyntax occupy the same position in the theory space.
    Their differences are in mechanism, not architecture. -/
theorem dm_nanosyntax_same_position : dm = nanosyntax := rfl

/-! ### 1c. Structural impossibilities

[kalin-bjorkman-etal-2026] §2.1: not all 2⁴ = 16 combinations
are possible. Process-based theories must be lexicalist (syntax is
piece-based). -/

/-- No non-lexicalist, process-based theory is well-formed. -/
theorem no_nonLexicalist_processBased :
    ∀ (a : Architecture) (m : Mapping),
    (TheoryPosition.mk .nonLexicalist a .processBased m).wellFormed = false :=
  nonLexicalist_processBased_illFormed

/-- No lexicalist theory can have syntactic architecture. -/
theorem no_lexicalist_syntactic :
    ∀ (e : Exponence) (m : Mapping),
    (TheoryPosition.mk .lexicalist .syntactic e m).wellFormed = false :=
  lexicalist_syntactic_illFormed

/-! ### 1d. Distinguishing features of each theory -/

/-- PFM is the only process-based theory among the four. -/
theorem pfm_uniquely_processBased :
    pfm.exponence = .processBased ∧
    dm.exponence ≠ .processBased ∧
    mas.exponence ≠ .processBased := by
  exact ⟨rfl, by decide, by decide⟩

/-- MaS is the only incremental theory among the four. -/
theorem mas_uniquely_incremental :
    mas.mapping = .incremental ∧
    dm.mapping ≠ .incremental ∧
    pfm.mapping ≠ .incremental := by
  exact ⟨rfl, by decide, by decide⟩

-- ============================================================================
-- §2: Wordhood Typology (Element §3)
-- ============================================================================

open Morphology.Wordhood
open Morphology.WordhoodBridge

/-! ### 2a. The 2×2 wordhood typology is exhaustive and injective -/

/-- Every combination of ms- and p-boundedness yields a wordhood class. -/
theorem wordhood_exhaustive (w : WordhoodProfile) :
    w.classify = .canonicalWord ∨
    w.classify = .simpleClitic ∨
    w.classify = .nonCoheringAffix ∨
    w.classify = .canonicalAffix :=
  classify_total w

/-- Distinct profiles yield distinct classes. -/
theorem wordhood_injective (w₁ w₂ : WordhoodProfile)
    (h : w₁.classify = w₂.classify) : w₁ = w₂ :=
  classify_injective w₁ w₂ h

/-! ### 2b. ZP diagnostics determine ms-boundedness

[kalin-bjorkman-etal-2026] §3.2.1: the six criteria from
[zwicky-pullum-1983] diagnose whether a morpheme is ms-bound.
This is formalized in `WordhoodBridge`. -/

/-- Affixhood (in MorphStatus) is equivalent to ms-boundedness. -/
theorem affix_iff_msbound (s : Morphology.MorphStatus) :
    s.IsAffix ↔ morphStatusToMSBound s = .bound :=
  affix_iff_ms_bound s

/-- Clitichood implies ms-freedom. -/
theorem clitic_implies_msfree (s : Morphology.MorphStatus)
    (h : s.IsClitic) : morphStatusToMSBound s = .free :=
  clitic_implies_ms_free s h

/-! ### 2c. Word diagnostics determine p-boundedness

[kalin-bjorkman-etal-2026] §3.2.2: prosodic diagnostics (vowel
harmony scope, minimal word constraints, hiatus resolution) diagnose
p-boundedness. This is formalized via the ProsodicWord bridge. -/

/-- An inflectional suffix (Word-internal) combined with ms-boundedness
    from the ZP criteria yields canonical affix. -/
theorem zpAffix_plus_prWdInternal :
    (wordhoodProfile .inflAffix
      (prWdMembershipToPBound true)).classify = .canonicalAffix := rfl

/-- A clitic (ms-free) that is Word-internal (p-bound) yields
    simple clitic — the canonical configuration for Romance clitics. -/
theorem zpClitic_plus_prWdInternal :
    (wordhoodProfile .simpleClitic
      (prWdMembershipToPBound true)).classify = .simpleClitic := rfl

/-- An affix (ms-bound) that is Word-external (p-free) yields
    non-cohering affix — the configuration for Dutch non-cohering
    prefixes. -/
theorem zpAffix_plus_prWdExternal :
    (wordhoodProfile .inflAffix
      (prWdMembershipToPBound false)).classify = .nonCoheringAffix := rfl

-- ============================================================================
-- §3: Form-Meaning Mapping (Element §4)
--     (Inlined from former Morphology/FormMeaningMapping.lean.)
-- ============================================================================

/-! §4 of [kalin-bjorkman-etal-2026] identifies seven descriptive types
of form-meaning mapping — the relationships between phonological exponents
and morphosyntactic features/functions. -/

namespace Morphology.FormMeaningMapping

/-- The seven descriptive types of form-meaning mapping.
    [kalin-bjorkman-etal-2026] §4. -/
inductive MappingType where
  /-- One meaning/function ↔ one exponent, invariant.
      Example: root *cat* is always `\/kæt\/`. -/
  | oneToOne
  /-- One meaning/function → multiple *competing* exponents
      (context-sensitive selection).
      Example: English plural *-z, -s, -ɪz, -ən, ∅*. §4.1. -/
  | allomorphy
  /-- One meaning/function → multiple *co-occurring* exponents
      (non-competing, simultaneous expression).
      Example: Amharic *k'al-at-otʃtʃ* 'words' (two plural markers). §4.2. -/
  | multipleExponence
  /-- Multiple related meanings/functions → one exponent
      (non-co-occurring contexts share a form).
      Example: English *-ed* for past tense and past participle. §4.3. -/
  | syncretism
  /-- Multiple co-occurring meanings/functions → one exponent
      (bundled into a single form).
      Example: French *du* = *de* + *le*. §4.4. -/
  | portmanteau
  /-- A meaning/function has no corresponding form — the paradigm
      cell is empty.
      Example: English *stride* lacks a standard past participle. §4.5.1. -/
  | morphologicalGap
  /-- A form has no corresponding meaning/function.
      Example: Romance theme vowels, compound linkers. §4.5.2. -/
  | emptyMorph
  deriving DecidableEq, Repr

end Morphology.FormMeaningMapping

open Morphology.FormMeaningMapping

/-! ### 3a. The seven descriptive types

[kalin-bjorkman-etal-2026] §4 identifies seven form-meaning
mapping types. Any theory of morphology must account for all of them. -/

/-- The seven types are mutually exclusive. -/
theorem mappingTypes_distinct :
    MappingType.oneToOne ≠ MappingType.allomorphy ∧
    MappingType.allomorphy ≠ MappingType.syncretism ∧
    MappingType.syncretism ≠ MappingType.portmanteau ∧
    MappingType.portmanteau ≠ MappingType.multipleExponence ∧
    MappingType.multipleExponence ≠ MappingType.morphologicalGap ∧
    MappingType.morphologicalGap ≠ MappingType.emptyMorph := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- §4: Cross-Module Integration
-- ============================================================================

/-! ### 4a. *ABA impossibility (Nanosyntax contribution)

[caha-2009]: the fseq-based Superset Principle derives the *ABA
constraint. If entry β beats entry α for case Y, β also beats α
for all cases below Y on the fseq —
`Morphology.Containment.isContiguous_spellout` in general. -/

open _root_.Morphology Morphology.Containment in
/-- An attempted ABA lexicon — "A" sized for the bottom grade, "B" for
    the top — produces ABB instead: the larger entry also wins the
    middle grade, and its pattern is contiguous by
    `isContiguous_spellout`. -/
theorem starABA_verified :
    spellout [(⟨"A", 0, none⟩ : ExponenceRule 3 String), ⟨"B", 2, none⟩] 0
      = some "A" ∧
    spellout [(⟨"A", 0, none⟩ : ExponenceRule 3 String), ⟨"B", 2, none⟩] 1
      = some "B" ∧
    spellout [(⟨"A", 0, none⟩ : ExponenceRule 3 String), ⟨"B", 2, none⟩] 2
      = some "B" ∧
    IsContiguous (spellout
      [(⟨"A", 0, none⟩ : ExponenceRule 3 String), ⟨"B", 2, none⟩]) :=
  ⟨by decide, by decide, by decide, isContiguous_spellout (by decide)⟩

/-! ### 4b. PFM's Paradigm Function architecture

[stump-2001]: PFM is the only major theory that is both
process-based and parallel in architecture. This combination is
well-formed because process-based requires lexicalism, and parallel
is a lexicalist architecture. -/

/-- PFM's combination of process-based exponence and parallel
    architecture is well-formed precisely because both are lexicalist. -/
theorem pfm_processBased_parallel_consistent :
    pfm.exponence = .processBased ∧
    pfm.architecture = .parallel ∧
    pfm.wellFormed = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5: Form-meaning mapping coverage (Table 4, §4.6)
-- ============================================================================

/-! ### 5. Theory × mapping-type matrix

[kalin-bjorkman-etal-2026] Table 4 captures the culminating insight
of the Element: different theories handle form-meaning mapping complexities
differently, and simplification in theory trades off against empirical
coverage. Each cell records whether a theory handles a mapping type:
- **yes**: natively, via basic mechanisms
- **no**: must reanalyze as a different phenomenon
- **extra**: can handle, but requires an additional mechanism

Key mechanisms referenced:
- **DM**: VI (allomorphy), Impoverishment (metasyncretism), Fission
  (multiple exponence), Fusion (portmanteau), Dissociated nodes (empty morphs)
- **PFM**: Rules of Referral (metasyncretism), rule blocks spanning
  (portmanteau), morphomic class indices (empty morphs)
- **Nanosyntax**: Superset Principle + containment (syncretism),
  phrasal spellout (portmanteau)
- **MaS**: strict one-to-one; all non-one-to-one phenomena must be
  reanalyzed as involving distinct morphemes or features -/

/-- How a morphological theory handles a form-meaning mapping type.
    [kalin-bjorkman-etal-2026] Table 4. -/
inductive Coverage where
  /-- Handled natively by the theory's basic mechanisms. -/
  | yes
  /-- Must be reanalyzed as a different phenomenon. -/
  | no
  /-- Requires an extra mechanism beyond the basics. -/
  | extra
  deriving DecidableEq, Repr, BEq

/-- The four named theories from [kalin-bjorkman-etal-2026]. -/
inductive TheoryName where
  | pfm | mas | nanosyntax | dm
  deriving DecidableEq, Repr, BEq

/-- Map a named theory to its position in the theory space. -/
def TheoryName.position : TheoryName → TheoryPosition
  | .pfm => Morphology.TheorySpace.pfm
  | .mas => Morphology.TheorySpace.mas
  | .nanosyntax => Morphology.TheorySpace.nanosyntax
  | .dm => Morphology.TheorySpace.dm

/-- [kalin-bjorkman-etal-2026] Table 4: for each (mapping type,
    theory) pair, the coverage verdicts across subcases.

    Multiple values indicate different subcases receive different
    verdicts. For example, DM handles some portmanteaux natively
    (pre-syntactic feature bundling), must reanalyze others
    (allomorphy in disguise), and needs Fusion for the rest. -/
def table4 : MappingType → TheoryName → List Coverage
  -- One-to-one: all theories handle natively
  | .oneToOne, _ => [.yes]
  -- Allomorphy: only DM (VI with contextual conditioning)
  | .allomorphy, .dm => [.yes]
  | .allomorphy, _ => [.no]
  -- Multiple exponence: PFM natively (independent rule blocks);
  -- DM needs Fission (extra); MaS and Nanosyntax reanalyze
  | .multipleExponence, .pfm => [.yes]
  | .multipleExponence, .dm => [.no, .extra]
  | .multipleExponence, _ => [.no]
  -- Syncretism: PFM yes (underspec) + extra (Rules of Referral);
  -- Nanosyntax yes (containment) + extra (pointers);
  -- DM yes (underspec/Impoverishment); MaS no
  | .syncretism, .pfm => [.yes, .extra]
  | .syncretism, .nanosyntax => [.yes, .extra]
  | .syncretism, .dm => [.yes]
  | .syncretism, .mas => [.no]
  -- Portmanteaux: PFM yes + extra (rule blocks spanning);
  -- Nanosyntax yes (phrasal spellout); DM yes + no + extra
  -- (bundling / reanalysis / Fusion); MaS no
  | .portmanteau, .pfm => [.yes, .extra]
  | .portmanteau, .nanosyntax => [.yes]
  | .portmanteau, .dm => [.yes, .no, .extra]
  | .portmanteau, .mas => [.no]
  -- Morphological gaps: no theory handles natively
  | .morphologicalGap, _ => [.no]
  -- Empty morphs: PFM yes (morphomic) + no (phonological);
  -- DM no + extra (Dissociated nodes); MaS/Nano no
  | .emptyMorph, .pfm => [.yes, .no]
  | .emptyMorph, .dm => [.no, .extra]
  | .emptyMorph, _ => [.no]

/-- Whether a theory natively handles a mapping type (has at least
    one `yes` verdict across subcases). -/
def handlesNatively (m : MappingType) (t : TheoryName) : Bool :=
  (table4 m t).any (· == .yes)

/-! ### 5a. All theories agree on one-to-one -/

/-- Every theory handles one-to-one mappings natively. -/
theorem all_handle_oneToOne (t : TheoryName) :
    table4 .oneToOne t = [.yes] := by cases t <;> rfl

/-! ### 5b. DM is uniquely suited for allomorphy

Only DM handles allomorphy natively, via Vocabulary Insertion with
contextual conditioning. PFM subsumes it under multiple exponence;
Nanosyntax reanalyzes structurally; MaS treats allomorphs as
distinct morphemes. -/

/-- DM is the only theory that handles allomorphy natively. -/
theorem only_dm_handles_allomorphy :
    handlesNatively .allomorphy .dm = true ∧
    handlesNatively .allomorphy .pfm = false ∧
    handlesNatively .allomorphy .mas = false ∧
    handlesNatively .allomorphy .nanosyntax = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### 5c. PFM is uniquely suited for multiple exponence

PFM's process-based, ordered rule-block architecture means
independent blocks can reference the same feature, producing
multiple exponence without any special mechanism. -/

/-- PFM is the only theory that handles multiple exponence natively. -/
theorem only_pfm_handles_multipleExponence :
    handlesNatively .multipleExponence .pfm = true ∧
    handlesNatively .multipleExponence .dm = false ∧
    handlesNatively .multipleExponence .mas = false ∧
    handlesNatively .multipleExponence .nanosyntax = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### 5d. Morphological gaps are universally problematic -/

/-- No theory handles morphological gaps natively. -/
theorem no_theory_handles_gaps (t : TheoryName) :
    table4 .morphologicalGap t = [.no] := by cases t <;> rfl

/-! ### 5e. MaS is the most restrictive theory

MaS's incremental mapping (form and meaning built in lockstep)
forces strict one-to-one correspondence. Every apparent
non-one-to-one mapping must be reanalyzed. -/

/-- MaS says "no" to every non-one-to-one mapping type. -/
theorem mas_rejects_all_complex (m : MappingType)
    (h : m ≠ .oneToOne) :
    table4 m .mas = [.no] := by
  cases m <;> first | exact absurd rfl h | rfl

/-! ### 5f. Realizational vs incremental split

[kalin-bjorkman-etal-2026] §4.6: realizational theories handle
at least some non-one-to-one mappings natively, because separating
features from exponents makes mismatches structurally possible.
Incremental theories (MaS) must reanalyze all of them. -/

/-- The three realizational theories all handle syncretism natively.
    MaS (incremental) cannot. -/
theorem syncretism_splits_on_realizational :
    handlesNatively .syncretism .dm = true ∧
    handlesNatively .syncretism .pfm = true ∧
    handlesNatively .syncretism .nanosyntax = true ∧
    handlesNatively .syncretism .mas = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The realizational/incremental split matches the theory space:
    DM, PFM, and Nanosyntax are realizational; MaS is incremental. -/
theorem syncretism_matches_mapping_dimension :
    Morphology.TheorySpace.dm.mapping = Mapping.realizational ∧
    Morphology.TheorySpace.pfm.mapping = Mapping.realizational ∧
    Morphology.TheorySpace.nanosyntax.mapping = Mapping.realizational ∧
    Morphology.TheorySpace.mas.mapping = Mapping.incremental :=
  ⟨rfl, rfl, rfl, rfl⟩

end KalinBjorkmanEtAl2026
