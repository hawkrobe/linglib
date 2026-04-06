import Linglib.Theories.Morphology.TheorySpace
import Linglib.Theories.Morphology.Core.WordhoodBridge
import Linglib.Core.Morphology.FormMeaningMapping
import Linglib.Theories.Morphology.Nanosyntax.Core
import Linglib.Theories.Morphology.PFM.Core

/-!
# @cite{kalin-bjorkman-etal-2026}: The Morphology/Syntax Interface
@cite{kalin-bjorkman-etal-2026}

This study file verifies the core contributions of
@cite{kalin-bjorkman-etal-2026}'s *Elements in Generative Syntax*
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

namespace Phenomena.Morphology.Studies.KalinBjorkmanEtAl2026

-- ============================================================================
-- §1: Theory Space (Element §2)
-- ============================================================================

open Theories.Morphology.TheorySpace

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

@cite{kalin-bjorkman-etal-2026} §2: DM and Nanosyntax agree on all four
dimensions. Their differences (Subset vs Superset Principle, terminal vs
phrasal spellout) are mechanism-level, not dimension-level. -/

/-- DM and Nanosyntax occupy the same position in the theory space.
    Their differences are in mechanism, not architecture. -/
theorem dm_nanosyntax_same_position : dm = nanosyntax := rfl

/-! ### 1c. Structural impossibilities

@cite{kalin-bjorkman-etal-2026} §2.1: not all 2⁴ = 16 combinations
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

open Core.Morphology.Wordhood
open Theories.Morphology.WordhoodBridge

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

@cite{kalin-bjorkman-etal-2026} §3.2.1: the six criteria from
@cite{zwicky-pullum-1983} diagnose whether a morpheme is ms-bound.
This is formalized in `WordhoodBridge`. -/

/-- Affixhood (in MorphStatus) is equivalent to ms-boundedness. -/
theorem affix_iff_msbound (s : Core.Morphology.MorphStatus) :
    s.isAffix = true ↔ morphStatusToMSBound s = .bound :=
  affix_iff_ms_bound s

/-- Clitichood implies ms-freedom. -/
theorem clitic_implies_msfree (s : Core.Morphology.MorphStatus)
    (h : s.isClitic = true) : morphStatusToMSBound s = .free :=
  clitic_implies_ms_free s h

/-! ### 2c. PrWd diagnostics determine p-boundedness

@cite{kalin-bjorkman-etal-2026} §3.2.2: prosodic diagnostics (vowel
harmony scope, minimal word constraints, hiatus resolution) diagnose
p-boundedness. This is formalized via the ProsodicWord bridge. -/

/-- An inflectional suffix (PrWd-internal) combined with ms-boundedness
    from the ZP criteria yields canonical affix. -/
theorem zpAffix_plus_prWdInternal :
    (wordhoodProfile .inflAffix
      (prWdMembershipToPBound true)).classify = .canonicalAffix := rfl

/-- A clitic (ms-free) that is PrWd-internal (p-bound) yields
    simple clitic — the canonical configuration for Romance clitics. -/
theorem zpClitic_plus_prWdInternal :
    (wordhoodProfile .simpleClitic
      (prWdMembershipToPBound true)).classify = .simpleClitic := rfl

/-- An affix (ms-bound) that is PrWd-external (p-free) yields
    non-cohering affix — the configuration for Dutch non-cohering
    prefixes. -/
theorem zpAffix_plus_prWdExternal :
    (wordhoodProfile .inflAffix
      (prWdMembershipToPBound false)).classify = .nonCoheringAffix := rfl

-- ============================================================================
-- §3: Form-Meaning Mapping (Element §4)
-- ============================================================================

open Core.Morphology.FormMeaningMapping

/-! ### 3a. The seven descriptive types

@cite{kalin-bjorkman-etal-2026} §4 identifies seven form-meaning
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

@cite{caha-2009}: the fseq-based Superset Principle derives the *ABA
constraint. If entry β beats entry α for case Y, β also beats α
for all cases below Y on the fseq. -/

/-- The *ABA derivation is verified by example:
    attempting an ABA lexicon produces ABB instead. -/
theorem starABA_verified :
    Theories.Morphology.Nanosyntax.abaViolation
      Theories.Morphology.Nanosyntax.attemptedABA 0 1 2 = false := by
  native_decide

/-! ### 4b. PFM's Paradigm Function architecture

@cite{stump-2001}: PFM is the only major theory that is both
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

@cite{kalin-bjorkman-etal-2026} Table 4 captures the culminating insight
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
    @cite{kalin-bjorkman-etal-2026} Table 4. -/
inductive Coverage where
  /-- Handled natively by the theory's basic mechanisms. -/
  | yes
  /-- Must be reanalyzed as a different phenomenon. -/
  | no
  /-- Requires an extra mechanism beyond the basics. -/
  | extra
  deriving DecidableEq, Repr, BEq

/-- The four named theories from @cite{kalin-bjorkman-etal-2026}. -/
inductive TheoryName where
  | pfm | mas | nanosyntax | dm
  deriving DecidableEq, Repr, BEq

/-- Map a named theory to its position in the theory space. -/
def TheoryName.position : TheoryName → TheoryPosition
  | .pfm => Theories.Morphology.TheorySpace.pfm
  | .mas => Theories.Morphology.TheorySpace.mas
  | .nanosyntax => Theories.Morphology.TheorySpace.nanosyntax
  | .dm => Theories.Morphology.TheorySpace.dm

/-- @cite{kalin-bjorkman-etal-2026} Table 4: for each (mapping type,
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

@cite{kalin-bjorkman-etal-2026} §4.6: realizational theories handle
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
    Theories.Morphology.TheorySpace.dm.mapping = Mapping.realizational ∧
    Theories.Morphology.TheorySpace.pfm.mapping = Mapping.realizational ∧
    Theories.Morphology.TheorySpace.nanosyntax.mapping = Mapping.realizational ∧
    Theories.Morphology.TheorySpace.mas.mapping = Mapping.incremental :=
  ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Morphology.Studies.KalinBjorkmanEtAl2026
