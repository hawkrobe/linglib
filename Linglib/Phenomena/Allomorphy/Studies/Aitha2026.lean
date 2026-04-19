import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment
import Linglib.Core.Constraint.System
import Linglib.Theories.Phonology.Prosodic.Syllable.Foot
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Theories.Phonology.StratalOT
import Linglib.Theories.Phonology.Prosodic.Word
import Linglib.Theories.Morphology.DM.RichExponent
import Linglib.Theories.Phonology.Prosodic.Moraic.CompensatoryLengthening
open Interfaces.Morphosyntax.CaseContainment

/-!
# The Nouns that Say *-ni* @cite{aitha-2026}

Aitha, A. (2026). The nouns that say *-ni*: Morpheme-specific phonology
in Telugu. *Natural Language & Linguistic Theory* 44:16.

## Overview

Telugu nouns exhibit two stem alternation patterns:

1. **Strong alternation**: NOM *il-lu* vs oblique *in-ṭi* ('house').
   Genuine case-conditioned contextual allomorphy, analyzed via DM
   Vocabulary Insertion with @cite{mcfadden-2018}'s case containment
   hierarchy. The NOM-vs-oblique split follows from the Elsewhere
   Condition: a rule conditioned on [ACC] is more specific than an
   unconditioned default.

2. **Weak alternation**: NOM *samudr-am* vs ACC *samudr-āni* ('ocean').
   Surface pattern looks like case-conditioned allomorphy but is
   phonological. Three diagnostics show it cannot be case allomorphy:
   (a) the ABAB paradigm shape violates @cite{caha-2009}'s *ABA
   constraint; (b) noncase agreement suffixes trigger the alternation;
   (c) the conditioning requires strict linear adjacency (phonological,
   not structural locality).

   The alternation is derived in Stratal OT (@cite{kiparsky-2000}):
   both surface forms derive from a single underlying *-am-ni*, where
   *-ni* is a singular suffix with prespecified stress. The interaction
   of stress faithfulness with foot binarity constraints across three
   phonological strata (Stem, Word, Phrase) produces the alternation.

## Formalization

- §1: Telugu case system and paradigm data
- §2: Strong alternation — VI rules and Elsewhere Condition
- §3: Weak alternation — *ABA violation and syllable-weight conditioning
- §4: Stem-level metrical parsing (OT tableau)
- §5: Word-level phonology — NOM and DAT tableaux (Stratal OT)
- §6: PrWd-based surface form prediction
-/

namespace Aitha2026

open Core Core.OT Core.ConstraintEvaluation
open Morphology.DM.VI
open Phonology.Syllable

-- ============================================================================
-- § 1: Telugu Case System and Paradigm Data
-- ============================================================================

/-- Telugu case values relevant to nominal paradigms. -/
inductive TeluguCase where
  | nom   -- nominative
  | acc   -- accusative
  | gen   -- genitive
  | dat   -- dative
  | loc   -- postposition -lō 'in'
  deriving DecidableEq, Repr

/-- Map Telugu cases to the core `Case` type. -/
def TeluguCase.toCore : TeluguCase → Core.Case
  | .nom => .nom
  | .acc => .acc
  | .gen => .gen
  | .dat => .dat
  | .loc => .loc

/-- Does this Telugu case bear the ACC feature (nonnominative)?
    Under @cite{mcfadden-2018}'s containment analysis, all
    nonnominative cases include ACC in their representation. -/
def TeluguCase.hasACC : TeluguCase → Bool
  | .nom => false
  | .acc | .gen | .dat | .loc => true

-- ────────────────────────────────────────────────────────────────────
-- Strong noun paradigm: *illu* 'house'
-- ────────────────────────────────────────────────────────────────────

/-- Root class for strongly suppletive nouns.
    @cite{aitha-2026} lists 7 subclasses, all sharing the NOM-vs-oblique
    split. Multiple NOM subclasses share a single OBL form (-ṭi for all
    but the -u∼-i class), a prediction of the Elsewhere Condition:
    the more specific (OBL) rule can generalize across root sets.
    We formalize two representative classes; the analysis extends to all. -/
inductive StrongClass where
  | luTi   -- -lu~-ṭi class (illu 'house', villu 'bow')
  | uI     -- -u~-i class (ūru 'town', moguḍu 'husband')
  -- Also attested but not separately formalized:
  -- -nu~-ṭi (kannu 'eye'), -du~-ṭi (gūdu 'nest'),
  -- -ru~-ṭi (ēru 'stream'), -li~-ṭi (nāgali 'plough'),
  -- -yi~-ṭi (nēyi 'ghee')
  deriving DecidableEq, Repr

/-- Strong noun paradigm: the n-exponent for each case.
    All strong nouns share the NOM-vs-oblique split regardless of
    the actual surface shape of n. -/
structure StrongParadigm where
  nomForm : String
  oblForm : String
  deriving DecidableEq, Repr

/-- The *n*-exponent for the -lu∼-ṭi class. -/
def luTiParadigm : StrongParadigm := ⟨"lu", "ṭi"⟩

/-- The *n*-exponent for the -u∼-i class. -/
def uIParadigm : StrongParadigm := ⟨"u", "i"⟩

/-- Surface form of *n* given a strong paradigm and case. -/
def strongSurface (p : StrongParadigm) (c : TeluguCase) : String :=
  if c.hasACC then p.oblForm else p.nomForm

-- ────────────────────────────────────────────────────────────────────
-- Weak noun paradigm: *samudram* 'ocean'
-- ────────────────────────────────────────────────────────────────────

/-- Stem form in weakly suppletive nouns. -/
inductive WeakStemForm where
  | short  -- -am (before heavy σ or domain-finally)
  | long   -- -āni (before light σ within PrWd)
  deriving DecidableEq, Repr

/-- The weak noun paradigm for *samudram* 'ocean'.
    Data from @cite{krishnamurti-gwynn-1985}. -/
def weakParadigm : TeluguCase → WeakStemForm
  | .nom => .short   -- samudr-am-∅
  | .acc => .long    -- samudr-āni-ni
  | .gen => .short   -- samudr-am-∅
  | .dat => .long    -- samudr-āni-ki
  | .loc => .short   -- samudr-am-lō

-- ============================================================================
-- § 2: Strong Alternation — VI Rules and Elsewhere Condition
-- ============================================================================

/-- Morphosyntactic context for VI at the *n* head in Telugu.
    A context consists of a root class and case features. -/
structure NContext where
  rootClass : StrongClass
  hasAccFeature : Bool
  deriving DecidableEq, Repr

/-- VI rule for NOM *n* of the -lu∼-ṭi class.
    No ACC feature required → this is the elsewhere/default rule. -/
def viLuNom : VocabItem NContext Unit :=
  { exponent := "lu"
  , contextMatch := λ ctx => ctx.rootClass == .luTi
  , specificity := 1 }

/-- VI rule for oblique *n* of the -lu∼-ṭi class.
    Requires ACC → more specific, wins over `viLuNom` in non-NOM. -/
def viLuObl : VocabItem NContext Unit :=
  { exponent := "ṭi"
  , contextMatch := λ ctx => ctx.rootClass == .luTi && ctx.hasAccFeature
  , specificity := 2 }

/-- VI rule for NOM *n* of the -u∼-i class. -/
def viUNom : VocabItem NContext Unit :=
  { exponent := "u"
  , contextMatch := λ ctx => ctx.rootClass == .uI
  , specificity := 1 }

/-- VI rule for oblique *n* of the -u∼-i class. -/
def viUObl : VocabItem NContext Unit :=
  { exponent := "i"
  , contextMatch := λ ctx => ctx.rootClass == .uI && ctx.hasAccFeature
  , specificity := 2 }

/-- All VI rules for strong noun *n*-exponents. -/
def strongVIRules : List (VocabItem NContext Unit) :=
  [viLuNom, viLuObl, viUNom, viUObl]

/-- Build the morphosyntactic context for VI from Telugu case + root class. -/
def mkNContext (rc : StrongClass) (c : TeluguCase) : NContext :=
  ⟨rc, c.hasACC⟩

-- Elsewhere Condition: oblique rules override default in non-NOM contexts

theorem vi_luTi_nom :
    vocabularyInsertSimple strongVIRules (mkNContext .luTi .nom)
      = some "lu" := by native_decide

theorem vi_luTi_acc :
    vocabularyInsertSimple strongVIRules (mkNContext .luTi .acc)
      = some "ṭi" := by native_decide

theorem vi_luTi_gen :
    vocabularyInsertSimple strongVIRules (mkNContext .luTi .gen)
      = some "ṭi" := by native_decide

theorem vi_luTi_dat :
    vocabularyInsertSimple strongVIRules (mkNContext .luTi .dat)
      = some "ṭi" := by native_decide

theorem vi_uI_nom :
    vocabularyInsertSimple strongVIRules (mkNContext .uI .nom)
      = some "u" := by native_decide

theorem vi_uI_acc :
    vocabularyInsertSimple strongVIRules (mkNContext .uI .acc)
      = some "i" := by native_decide

/-- VI produces the correct strong paradigm for -lu∼-ṭi nouns. -/
theorem vi_matches_strong_luTi (c : TeluguCase) :
    vocabularyInsertSimple strongVIRules (mkNContext .luTi c)
      = some (strongSurface luTiParadigm c) := by
  cases c <;> native_decide

/-- VI produces the correct strong paradigm for -u∼-i nouns. -/
theorem vi_matches_strong_uI (c : TeluguCase) :
    vocabularyInsertSimple strongVIRules (mkNContext .uI c)
      = some (strongSurface uIParadigm c) := by
  cases c <;> native_decide

-- ============================================================================
-- § 3: Weak Alternation — *ABA Violation
-- ============================================================================

/-- The weak alternation's surface paradigm as an `AllomorphyPattern`.
    Short form = 0, long form = 1. -/
def weakAllomorphyPattern : AllomorphyPattern :=
  { nom := 0   -- short (-am)
  , acc := 1   -- long (-āni)
  , gen := 0   -- short (-am)
  , dat := 1 } -- long (-āni)

/-- The weak alternation violates @cite{caha-2009}'s *ABA constraint.
    The ABAB pattern contains the subsequence A–B–A at NOM–ACC–GEN:
    NOM and GEN share the short form, but intervening ACC has the long
    form. Since GEN's representation contains ACC's on the containment
    hierarchy, this cannot arise from case-conditioned VI. -/
theorem weak_violates_aba :
    weakAllomorphyPattern.ViolatesABA := by decide

/-- Therefore the weak alternation is not contiguous on the case
    containment hierarchy. -/
theorem weak_not_contiguous :
    ¬ weakAllomorphyPattern.IsContiguous := by decide

/-- In contrast, the strong alternation (ABB = NOM vs oblique) is
    contiguous — consistent with case-conditioned VI. -/
def strongAllomorphyPattern : AllomorphyPattern :=
  { nom := 0, acc := 1, gen := 1, dat := 1 }

theorem strong_contiguous :
    strongAllomorphyPattern.IsContiguous := by decide

-- ────────────────────────────────────────────────────────────────────
-- Formal connection: paradigm data → allomorphy pattern
-- ────────────────────────────────────────────────────────────────────

/-- Helper: encode WeakStemForm as a Nat for AllomorphyPattern comparison. -/
def WeakStemForm.toNat : WeakStemForm → Nat
  | .short => 0
  | .long => 1

/-- The `weakAllomorphyPattern` is not a separate stipulation — it is
    derived from `weakParadigm`. This theorem closes the gap between
    the paradigm data and the *ABA check. -/
theorem weak_pattern_from_paradigm :
    weakAllomorphyPattern =
      { nom := (weakParadigm .nom).toNat
      , acc := (weakParadigm .acc).toNat
      , gen := (weakParadigm .gen).toNat
      , dat := (weakParadigm .dat).toNat } := by native_decide

-- ────────────────────────────────────────────────────────────────────
-- Agreement suffixes trigger the weak alternation
-- ────────────────────────────────────────────────────────────────────

/-- Environments that trigger the long form in weak nouns.
    The long form surfaces when followed by a light syllable within the
    prosodic word — regardless of whether that syllable realizes a case
    suffix or an agreement suffix.

    Data from @cite{aitha-2026}'s full(er) paradigm including agreement:
    - ACC *-ni*: light σ within PrWd → long (*samudr-āni-ni*)
    - DAT *-ki*: light σ within PrWd → long (*samudr-āni-ki*)
    - 1SG *-ni*: light σ within PrWd → long (*samudr-āni-ni*)
    - 2SG *-vi*: light σ within PrWd → long (*samudr-āni-vi*)
    - NOM *-∅*: no following σ → short (*samudr-am-∅*)
    - GEN *-∅*: no following σ → short (*samudr-am-∅*)
    - 3SG *-∅*: no following σ → short (*samudr-am-∅*)
    - P *-lō*: separate PrWd → short (*samudr-am-lō*)
    - P *-gurinci*: separate PrWd → short (*samudr-am-gurinci*)
    - P *-eduru*: separate PrWd → short (*samudr-am-eduru*)

    Note: -gurinci and -eduru begin with light syllables, yet still
    trigger the short form. The conditioning factor is PrWd membership,
    not syllable weight of the following element per se. -/
inductive FollowingContext where
  | noSuffix           -- NOM, GEN, 3SG: no overt suffix
  | lightWithinPrWd    -- ACC -ni, DAT -ki, 1SG -ni, 2SG -vi
  | separatePrWd       -- postpositions (-lō, -gurinci, -eduru): separate PrWd
  deriving DecidableEq, Repr

/-- The phonological conditioning: long form iff followed by a light
    syllable within the same prosodic word. -/
def weakFormPredicted : FollowingContext → WeakStemForm
  | .lightWithinPrWd => .long
  | .noSuffix => .short
  | .separatePrWd => .short

/-- Both ACC *-ni* (case) and 1SG *-ni* (agreement) trigger the long
    form — the conditioning is phonological, not morphosyntactic. -/
theorem light_suffix_triggers_long :
    weakFormPredicted .lightWithinPrWd = .long := rfl

/-- No following suffix → short form. -/
theorem no_suffix_triggers_short :
    weakFormPredicted .noSuffix = .short := rfl

/-- Postposition in a separate PrWd → short form (regardless of
    whether the postposition starts with a light or heavy syllable). -/
theorem separate_prwd_triggers_short :
    weakFormPredicted .separatePrWd = .short := rfl

-- ────────────────────────────────────────────────────────────────────
-- Telugu nominal agreement paradigm
-- ────────────────────────────────────────────────────────────────────

/-- Telugu nominal predicative agreement suffixes.
    Only 1SG and 2SG are overt; 3SG and all plurals are null.
    Data from @cite{aitha-2026}. -/
inductive AgrSuffix where
  | sg1   -- -ni (overt, light σ)
  | sg2   -- -vi (overt, light σ)
  | sg3   -- -∅ (null)
  deriving DecidableEq, Repr

/-- Classify agreement suffixes by their phonological context:
    overt light suffixes pattern identically to overt light case suffixes. -/
def AgrSuffix.toFollowing : AgrSuffix → FollowingContext
  | .sg1 => .lightWithinPrWd    -- -ni
  | .sg2 => .lightWithinPrWd    -- -vi
  | .sg3 => .noSuffix           -- -∅

/-- 1SG *-ni* triggers the long form, just like ACC *-ni*.
    Both are light syllables within PrWd — the conditioning is
    phonological, not morphosyntactic. -/
theorem agr_1sg_triggers_long :
    weakFormPredicted (AgrSuffix.sg1).toFollowing = .long := rfl

/-- 3SG *-∅* triggers the short form, just like NOM *-∅*. -/
theorem agr_3sg_triggers_short :
    weakFormPredicted (AgrSuffix.sg3).toFollowing = .short := rfl

/-- The decisive argument: case and agreement suffixes with identical
    phonological shape produce identical stem forms. ACC *-ni* and 1SG *-ni*
    both map to `lightWithinPrWd`, so both trigger the long form.
    If the alternation were case-conditioned, agreement suffixes (which bear
    no case features) could not trigger it. -/
theorem case_agr_identity :
    (AgrSuffix.sg1).toFollowing = FollowingContext.lightWithinPrWd ∧
    weakFormPredicted (AgrSuffix.sg1).toFollowing =
      weakFormPredicted .lightWithinPrWd := ⟨rfl, rfl⟩

-- ────────────────────────────────────────────────────────────────────
-- Underlying form: -am-ni (§4.2)
-- ────────────────────────────────────────────────────────────────────

/-- The underlying representation of the weak noun stem.
    @cite{aitha-2026} argues (§4.2) that the surface alternants *-am* and
    *-āni* derive from a single underlying form: the concatenation of
    *-am* (exponent of *n*) + *-ni* (singular suffix, exponent of Num).

    The surface forms result from TWO independent phonological processes:
    1. The *-am* ~ *-ā* alternation: compensatory lengthening after
       deletion of the coda nasal (Stem-level vowel hiatus resolution)
    2. The *-ni* ~ *-∅* alternation: deletion of stressed light syllables
       that cannot form a binary foot (Word-level phonology)

    This unified underlying form means the "stem alternation" is not a
    single alternation at all, but the combined effect of two regular
    phonological processes acting on the same input. -/
structure WeakUnderlying where
  nExponent : String     -- the exponent of n: always "-am"
  sgSuffix  : String     -- the singular suffix: always "-ni"

/-- All weak nouns share the same underlying *-am-ni*. -/
def weakUnderlying : WeakUnderlying := ⟨"am", "ni"⟩

-- ────────────────────────────────────────────────────────────────────
-- Locality: strong is structural, weak is linear (§4.1)
-- ────────────────────────────────────────────────────────────────────

/-- The two alternations differ in their sensitivity to locality.
    @cite{aitha-2026} (§4.1) shows this via Q-postposing constructions:
    - Strong: oblique can be triggered *across* an intervening quantifier
      (structural locality — the case head c-commands *n*)
    - Weak: the alternation is determined by the *linearly adjacent*
      syllable, not by structural position

    This difference supports the claim that the strong alternation is
    morphosyntactic (structural, can skip intervening material) while the
    weak alternation is phonological (linear adjacency required). -/
inductive LocalityType where
  | structural   -- can skip intervening material (c-command)
  | linear       -- requires strict linear adjacency
  deriving DecidableEq, Repr

def strongLocality : LocalityType := .structural
def weakLocality : LocalityType := .linear

theorem locality_differs : strongLocality ≠ weakLocality := by decide

-- ============================================================================
-- § 4: Stem-Level Metrical Parsing (OT Tableau)
-- ============================================================================

/-- Candidates for the Stem-level metrical parse of *samudr-am*
    'ocean-n' (underlying syllable weights: CV.CV.CVC = L.L.H). -/
inductive StemCandidate where
  /-- (ˈsa.mu).dram — one bimoraic foot, final H unparsed. -/
  | llU_H
  /-- (ˈsa).(ˌmu).(ˌdram) — two degenerate feet + one bimoraic. -/
  | l_l_H
  /-- (ˈsa.mu).(ˌdram) — two bimoraic feet. Optimal. -/
  | ll_H
  deriving DecidableEq, Repr

/-- Map each candidate to its `MetricalParse` representation. -/
def StemCandidate.toParse : StemCandidate → MetricalParse
  | .llU_H => [.foot [.light, .light], .unfooted .heavy]
  | .l_l_H => [.foot [.light], .foot [.light], .foot [.heavy]]
  | .ll_H  => [.foot [.light, .light], .foot [.heavy]]

/-- FT-BIN(μ): penalizes non-bimoraic feet. -/
def cFtBin : NamedConstraint StemCandidate :=
  { name := "FT-BIN(μ)", family := .markedness
  , eval := λ c => ftBinViolations c.toParse }

/-- PARSE-SYL: penalizes unparsed syllables. -/
def cParseSyl : NamedConstraint StemCandidate :=
  { name := "PARSE-SYL", family := .markedness
  , eval := λ c => parseSylViolations c.toParse }

/-- ALL-FT-LEFT: penalizes feet distant from the left edge. -/
def cAllFtLeft : NamedConstraint StemCandidate :=
  { name := "ALL-FT-LEFT", family := .markedness
  , eval := λ c => allFtLeftViolations c.toParse }

/-- Stem-level constraint ranking: FT-BIN ≫ PARSE-SYL ≫ ALL-FT-LEFT.

    FT-BIN dominates PARSE-SYL: it is better to leave a syllable
    unparsed than to create a degenerate (monomoraic) foot. -/
def stemRanking : List (NamedConstraint StemCandidate) :=
  [cFtBin, cParseSyl, cAllFtLeft]

def stemCandidates : List StemCandidate := [.llU_H, .l_l_H, .ll_H]
theorem stemCandidates_ne : stemCandidates ≠ [] := by decide

/-- Violation profiles for Stem-level candidates:

    | Candidate         | FT-BIN | PARSE-SYL | ALL-FT-LEFT |
    |--------------------|--------|-----------|-------------|
    | (ˈsa.mu).dram      |   0    |    1*     |     0       |
    | (ˈsa).(ˌmu).(ˌdram)|   2*   |    0      |     0+1+2   |
    | ☞ (ˈsa.mu).(ˌdram) |   0    |    0      |     0+2     | -/
theorem stem_ftbin_violations :
    stemCandidates.map cFtBin.eval = [0, 2, 0] := by native_decide

theorem stem_parsesyl_violations :
    stemCandidates.map cParseSyl.eval = [1, 0, 0] := by native_decide

/-- The optimal Stem-level parse is (ˈsa.mu).(ˌdram): two well-formed
    moraic trochees, (LL)(H), with no unparsed syllables. -/
theorem stem_optimal :
    (mkTableau stemCandidates stemRanking stemCandidates_ne).optimal
      = {.ll_H} := by native_decide

-- ============================================================================
-- § 5: Word-Level Phonology (Stratal OT)
-- ============================================================================

section WordLevel

open Phonology.StratalOT
open Phonology.ProsodicWord
open Morphology.DM.RichRepresentation

/-- The singular suffix *-ni* carries prespecified stress.
    This prespecification, interacting with FT-BIN(μ) and IDENT-STRESS
    at the Word level, drives deletion of *-ni* when it is PrWd-final
    and cannot form a binary foot. -/
def sgNiExponent : RichExponent := .stressed "ni"

theorem sgNi_is_stressed :
    sgNiExponent.prosody.inherentStress = some true := rfl

-- ────────────────────────────────────────────────────────────────────
-- § 5.1: NOM — PrWd-final stressed -ni (no following light suffix)
-- ────────────────────────────────────────────────────────────────────

/-- Word-level candidates for the NOM input (ˈsa.mu).(ˌdram).ní.
    Stressed *-ni* is PrWd-final: no following suffix to pair with. -/
inductive WordCandNom where
  /-- (ˈsa.mu).(ˌdram).ni — stress on *-ni* removed. -/
  | destress
  /-- (ˈsa.mu).(ˌdram).(ˌní) — *-ni* as degenerate (monomoraic) foot. -/
  | degenerateFoot
  /-- (ˈsa.mu).(ˌdramn) — nucleic /i/ deleted, /n/ joins coda → complex. -/
  | deleteI_coda
  /-- (ˈsa.mu).(ˌdran) — /i/ and /m/ deleted, Stem edge misaligned. -/
  | deleteIM
  /-- ☞ (ˈsa.mu).(ˌdram) — /ni/ fully deleted. -/
  | deleteNi
  deriving DecidableEq, Repr

/-- Word-level ranking for NOM.

    | Candidate      | ID-STR | FT-BIN | \*CxCODA | AL-R | MAX(μ) | MAX |
    |----------------|--------|--------|----------|------|--------|-----|
    | destress       |  1\*   |        |          |      |        |     |
    | degenerateFoot |        |  1\*   |          |      |        |     |
    | deleteI\_coda  |        |        |   1\*    |      |   1    |  1  |
    | deleteIM       |        |        |          |  1\* |   2    |  2  |
    | ☞ deleteNi     |        |        |          |      |   1    |  2  | -/
def wordNomRanking : List (NamedConstraint WordCandNom) :=
  [ { name := "IDENT-STRESS", family := .faithfulness
    , eval := λ | .destress => 1 | _ => 0 }
  , { name := "FT-BIN(μ)", family := .markedness
    , eval := λ | .degenerateFoot => 1 | _ => 0 }
  , { name := "*COMPLEXCODA", family := .markedness
    , eval := λ | .deleteI_coda => 1 | _ => 0 }
  , { name := "ALIGN-RIGHT(Stem,σ)", family := .markedness
    , eval := λ | .deleteIM => 1 | _ => 0 }
  , { name := "MAX(μ)", family := .faithfulness
    , eval := λ | .deleteI_coda => 1 | .deleteIM => 2 | .deleteNi => 1 | _ => 0 }
  , { name := "MAX", family := .faithfulness
    , eval := λ | .deleteI_coda => 1 | .deleteIM => 2 | .deleteNi => 2 | _ => 0 } ]

def wordNomCands : List WordCandNom :=
  [.destress, .degenerateFoot, .deleteI_coda, .deleteIM, .deleteNi]

theorem wordNomCands_ne : wordNomCands ≠ [] := by decide

/-- Word level, NOM: PrWd-final stressed *-ni* is deleted.
    Surface: *samudr-am* (short form). -/
theorem wordNom_optimal :
    (mkTableau wordNomCands wordNomRanking wordNomCands_ne).optimal
      = {.deleteNi} := by native_decide

-- ────────────────────────────────────────────────────────────────────
-- § 5.2: DAT — light -ki follows within PrWd
-- ────────────────────────────────────────────────────────────────────

/-- Word-level candidates for the DAT input (ˈsa.mu).(ˌdram).ní.ki.
    The light suffix *-ki* is PrWd-internal, so *-ni* can form a
    bimoraic foot (ˌní.ki) — but the /mn/ boundary violates \*DIST-0. -/
inductive WordCandDat where
  /-- (ˈsa.mu).(ˌdram).(ˌní.ki) — faithful. /mn/ boundary retained. -/
  | faithful
  /-- (ˈsa.mu).(ˌdra).(ˌmí.ki) — /m/ resyllabified as onset. -/
  | resyllabify
  /-- (ˈsa.mu).(ˌdram).ki — /ni/ deleted, *-ki* degenerate. -/
  | deleteNi
  /-- ☞ (ˈsa.mu).(ˌdrā).(ˌní.ki) — /m/ deleted, /a/→/ā/ (CL). -/
  | compLengthen
  deriving DecidableEq, Repr

/-- Word-level ranking for DAT. Same constraint set as NOM, with
    \*DIST-0 additionally relevant (eliminates faithful candidate).

    | Candidate       | \*DIST-0 | AL-R | ID-STR | FT-BIN | MAX(μ) | MAX |
    |-----------------|----------|------|--------|--------|--------|-----|
    | faithful        |   1\*    |      |        |        |        |     |
    | resyllabify     |          |  1\* |        |        |        |     |
    | deleteNi        |          |      |        |   1\*  |   1    |  2  |
    | ☞ compLengthen  |          |      |        |        |   1    |  1  | -/
def wordDatRanking : List (NamedConstraint WordCandDat) :=
  [ { name := "*DIST-0", family := .markedness
    , eval := λ | .faithful => 1 | _ => 0 }
  , { name := "ALIGN-RIGHT(Stem,σ)", family := .markedness
    , eval := λ | .resyllabify => 1 | _ => 0 }
  , { name := "IDENT-STRESS", family := .faithfulness
    , eval := λ _ => 0 }
  , { name := "FT-BIN(μ)", family := .markedness
    , eval := λ | .deleteNi => 1 | _ => 0 }
  , { name := "MAX(μ)", family := .faithfulness
    , eval := λ | .deleteNi => 1 | .compLengthen => 1 | _ => 0 }
  , { name := "MAX", family := .faithfulness
    , eval := λ | .deleteNi => 2 | .compLengthen => 1 | _ => 0 } ]

def wordDatCands : List WordCandDat :=
  [.faithful, .resyllabify, .deleteNi, .compLengthen]

theorem wordDatCands_ne : wordDatCands ≠ [] := by decide

/-- Word level, DAT: /mn/ boundary repaired by compensatory lengthening.
    Surface: *samudr-āni-ki* (long form). -/
theorem wordDat_optimal :
    (mkTableau wordDatCands wordDatRanking wordDatCands_ne).optimal
      = {.compLengthen} := by native_decide

-- ────────────────────────────────────────────────────────────────────
-- § 5.3: Core result — same constraints, different outputs
-- ────────────────────────────────────────────────────────────────────

/-- The same constraint system derives both surface forms from the same
    underlying *-am-ni*. The difference is purely phonological: whether
    a light suffix follows within the PrWd.

    - NOM (no suffix): *-ni* is PrWd-final → deleted → **short**
    - DAT (*-ki* follows): *-ni* pairs with *-ki* → /mn/ repaired → **long**

    This completes the derivation that the `weakFormPredicted` function
    (§3) stipulates: the alternation is now DERIVED from OT constraint
    interaction, not encoded by fiat. -/
theorem word_level_derives_alternation :
    (mkTableau wordNomCands wordNomRanking wordNomCands_ne).optimal
      = {.deleteNi} ∧
    (mkTableau wordDatCands wordDatRanking wordDatCands_ne).optimal
      = {.compLengthen} :=
  ⟨wordNom_optimal, wordDat_optimal⟩

/-- Map Word-level optimal outputs to `WeakStemForm`.
    NOM deleteNi = short (the -ni is gone, surface is -am).
    DAT compLengthen = long (the -am becomes -ā, -ni survives as -āni). -/
def WordCandNom.toStemForm : WordCandNom → WeakStemForm
  | .deleteNi => .short
  | _ => .long  -- non-optimal; included for totality

def WordCandDat.toStemForm : WordCandDat → WeakStemForm
  | .compLengthen => .long
  | _ => .short  -- non-optimal; included for totality

theorem nom_produces_short : WordCandNom.deleteNi.toStemForm = .short := rfl
theorem dat_produces_long : WordCandDat.compLengthen.toStemForm = .long := rfl

end WordLevel

-- ============================================================================
-- § 6: PrWd-Based Surface Form Prediction
-- ============================================================================

section PrWdIntegration

open Phonology.ProsodicWord

/-- Predict the weak stem form from the following morphological element.
    Uses `MorphElement.triggersLongForm` from `ProsodicWord`: the long
    form surfaces iff the following element is PrWd-internal AND begins
    with a light syllable. -/
def weakSurfaceFromPrWd : Option MorphElement → WeakStemForm
  | some m => if m.triggersLongForm then .long else .short
  | none   => .short  -- no following element → PrWd-final → short

-- Case suffixes

theorem acc_ni_long :
    weakSurfaceFromPrWd (some ⟨"-ni", .inflectional, .light⟩) = .long := rfl

theorem dat_ki_long :
    weakSurfaceFromPrWd (some ⟨"-ki", .inflectional, .light⟩) = .long := rfl

theorem nom_null_short :
    weakSurfaceFromPrWd none = .short := rfl

theorem gen_null_short :
    weakSurfaceFromPrWd none = .short := rfl

-- Agreement suffixes (the decisive diagnostic)

theorem agr_1sg_ni_long :
    weakSurfaceFromPrWd (some ⟨"-ni", .agreement, .light⟩) = .long := rfl

theorem agr_2sg_vi_long :
    weakSurfaceFromPrWd (some ⟨"-vi", .agreement, .light⟩) = .long := rfl

-- Postpositions (PrWd-external → always short)

theorem postp_lo_short :
    weakSurfaceFromPrWd (some ⟨"-lō", .postposition, .heavy⟩) = .short := rfl

/-- Postposition *-gurinci* 'about' begins with a light syllable, yet
    triggers the short form — because it is PrWd-external. This is
    the key evidence that the conditioning is PrWd membership, not
    syllable weight alone. -/
theorem postp_gurinci_short :
    weakSurfaceFromPrWd (some ⟨"-gurinci", .postposition, .light⟩) = .short := rfl

/-- The PrWd-based prediction matches the original paradigm data for
    all five cases in the canonical weak paradigm. -/
theorem prwd_matches_paradigm :
    weakSurfaceFromPrWd (some ⟨"-ni", .inflectional, .light⟩) = .long ∧
    weakSurfaceFromPrWd (some ⟨"-ki", .inflectional, .light⟩) = .long ∧
    weakSurfaceFromPrWd none = .short ∧
    weakSurfaceFromPrWd none = .short ∧
    weakSurfaceFromPrWd (some ⟨"-lō", .postposition, .heavy⟩) = .short :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The PrWd-based prediction agrees with the original `weakParadigm`
    for all five cases. This closes the gap between the phonological
    derivation (OT + PrWd) and the empirical data (paradigm). -/
theorem prwd_agrees_with_paradigm :
    (weakSurfaceFromPrWd (some ⟨"-ni", .inflectional, .light⟩) = weakParadigm .acc) ∧
    (weakSurfaceFromPrWd (some ⟨"-ki", .inflectional, .light⟩) = weakParadigm .dat) ∧
    (weakSurfaceFromPrWd none = weakParadigm .nom) ∧
    (weakSurfaceFromPrWd none = weakParadigm .gen) ∧
    (weakSurfaceFromPrWd (some ⟨"-lō", .postposition, .heavy⟩) = weakParadigm .loc) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end PrWdIntegration

-- ============================================================================
-- § 7: Summary Theorems
-- ============================================================================

/-- The two alternation patterns have fundamentally different analyses:

    1. Strong alternation: ABB pattern (contiguous on containment
       hierarchy) → case-conditioned contextual allomorphy (VI).
    2. Weak alternation: ABAB pattern (violates *ABA) → phonological
       alternation conditioned by syllable weight within PrWd.

    The strong alternation depends on structural position (Elsewhere
    Condition + ACC feature); the weak alternation depends on linear
    adjacency to a light syllable (phonological locality). -/
theorem strong_vs_weak_distinction :
    strongAllomorphyPattern.IsContiguous ∧
    ¬ weakAllomorphyPattern.IsContiguous := ⟨by decide, by decide⟩

/-- The outward sensitivity of the weak alternation: the form of *n*
    (closer to root) depends on material further from the root (case
    and agreement suffixes). Under root-out VI, this is impossible —
    suffixes are not yet inserted when *n* receives its exponent. -/
theorem weak_is_outward_sensitive :
    isOutwardSensitive (conditioningPos := 2) (targetPos := 1) = true := rfl

-- ============================================================================
-- § 8: Integration with Core Infrastructure
-- ============================================================================

/-- Telugu's `hasACC` exactly mirrors `Core.Case.IsNonnominative` via `toCore`.
    This confirms the study's case-feature assignments are consistent with
    the containment hierarchy infrastructure. -/
theorem hasACC_eq_isNonnom (c : TeluguCase) :
    c.hasACC = decide (Core.Case.IsNonnominative c.toCore) := by
  cases c <;> rfl

-- The Telugu 5-case inventory is contiguous on Blake's typological
-- hierarchy (@cite{blake-1994}).
example : Core.Case.IsValidInventory ({.nom, .acc, .gen, .dat, .loc} : Finset Core.Case) := by
  decide

/-- The strong alternation pattern derived from VI output matches the
    `strongAllomorphyPattern` used for the *ABA check.
    This is the end-to-end chain: VI rules → surface forms → ABB pattern → contiguous.

    The proof constructs the pattern from `strongSurface` by checking whether
    each case gets the NOM form (= 0) or the OBL form (= 1). -/
theorem vi_derives_strong_pattern :
    (if strongSurface luTiParadigm .nom == strongSurface luTiParadigm .nom then 0 else 1,
     if strongSurface luTiParadigm .acc == strongSurface luTiParadigm .nom then 0 else 1,
     if strongSurface luTiParadigm .gen == strongSurface luTiParadigm .nom then 0 else 1,
     if strongSurface luTiParadigm .dat == strongSurface luTiParadigm .nom then 0 else 1)
    = (0, 1, 1, 1) := by native_decide

/-- End-to-end argumentation chain:
    1. Strong alternation: VI derives ABB → contiguous → valid case allomorphy
    2. Weak alternation: ABAB pattern → non-contiguous → cannot be case allomorphy
    3. Weak alternation: outward-sensitive → incompatible with root-out VI
    4. THEREFORE: weak alternation is phonological, not morphological -/
theorem central_argument :
    -- (1) Strong is contiguous
    strongAllomorphyPattern.IsContiguous ∧
    -- (2) Weak is non-contiguous
    ¬ weakAllomorphyPattern.IsContiguous ∧
    -- (3) Weak is outward-sensitive
    isOutwardSensitive (conditioningPos := 2) (targetPos := 1) = true := by
  exact ⟨by decide, by decide, rfl⟩

-- ============================================================================
-- § 9: Connection to Moraic CL Theory (@cite{hayes-1989})
-- ============================================================================

section MoraicCLConnection

open Phonology (Segment)
open Phonology.Moraic (MoraicParams syllableToMoraic MoraicSyllable)
open Phonology.Moraic.CL (deleteMoraic spreadToFill)

/-- Telugu has Weight by Position: coda consonants bear morae, making
    CVC syllables heavy. This is assumed by the Stem-level parse, where
    *dram* (CVC) is treated as heavy (2μ). -/
def teluguMoraicParams : MoraicParams := { wbp := true }

/-- In a WBP language like Telugu, deleting a coda consonant strands one
    mora — this is @cite{hayes-1989}'s **classical CL** (§5.1.1).

    This grounds the DAT `compLengthen` candidate: /m/ deletion from
    /dram/ strands a mora, which spreads left to yield /drā/.
    The CL repair is not a stipulated candidate — it is available
    precisely because Telugu has WBP. -/
theorem telugu_coda_deletion_strands_mora (o n c : Segment) :
    (deleteMoraic (syllableToMoraic teluguMoraicParams ⟨[o], [n], [c]⟩) 1).2 = 1 := rfl

/-- Moraic conservation (Rule (64), @cite{hayes-1989}): the mora stranded
    by /m/ deletion is absorbed by leftward spreading to /a/, yielding /ā/
    (2μ). Total mora count is unchanged. -/
theorem telugu_cl_conservation (o n c : Segment) :
    let σ := syllableToMoraic teluguMoraicParams ⟨[o], [n], [c]⟩
    let (σ_del, stranded) := deleteMoraic σ 1
    σ.moraCount = (spreadToFill σ_del stranded .left).moraCount := rfl

end MoraicCLConnection

-- ============================================================================
-- § 10: Generic ConstraintSystem Predictions
-- ============================================================================

/-! All three Telugu OT tableaux lift to generic `ConstraintSystem`s via
`tableauSystem`. The Stratal-OT derivation of the weak alternation
becomes a probability-1 claim per stratum. -/

section PredictAPI
open Core.Constraint

/-- Stem-level metrical parse tableau as a generic `ConstraintSystem`. -/
noncomputable def stemSystem : ConstraintSystem StemCandidate (LexProfile Nat 3) :=
  tableauSystem (mkTableau stemCandidates stemRanking stemCandidates_ne)

/-- Probability 1 on (LL)(H): two well-formed moraic trochees. -/
theorem stemSystem_predict_ll_H :
    stemSystem.predict StemCandidate.ll_H = 1 :=
  tableauSystem_predict_unique_winner _ _ stem_optimal

/-- Word-level NOM tableau as a generic `ConstraintSystem`. -/
noncomputable def wordNomSystem : ConstraintSystem WordCandNom (LexProfile Nat 6) :=
  tableauSystem (mkTableau wordNomCands wordNomRanking wordNomCands_ne)

/-- Probability 1 on `deleteNi`: PrWd-final stressed *-ni* is deleted. -/
theorem wordNomSystem_predict_deleteNi :
    wordNomSystem.predict WordCandNom.deleteNi = 1 :=
  tableauSystem_predict_unique_winner _ _ wordNom_optimal

/-- Word-level DAT tableau as a generic `ConstraintSystem`. -/
noncomputable def wordDatSystem : ConstraintSystem WordCandDat (LexProfile Nat 6) :=
  tableauSystem (mkTableau wordDatCands wordDatRanking wordDatCands_ne)

/-- Probability 1 on `compLengthen`: /m/ deletion + CL yields *-āni*. -/
theorem wordDatSystem_predict_compLengthen :
    wordDatSystem.predict WordCandDat.compLengthen = 1 :=
  tableauSystem_predict_unique_winner _ _ wordDat_optimal

end PredictAPI

end Aitha2026
