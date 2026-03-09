import Linglib.Core.Case.Containment
import Linglib.Core.Logic.OT
import Linglib.Theories.Phonology.Syllable.Foot
import Linglib.Theories.Morphology.DM.VocabularyInsertion

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
-/

namespace Phenomena.Allomorphy.TeluguNounStems.Studies.Aitha2026

open Core Core.OT Core.ConstraintEvaluation
open Morphology.DM.VI
open Theories.Phonology.Syllable

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

/-- Strong noun paradigm: the n-exponent for each case.
    All strong nouns share the NOM-vs-oblique split regardless of
    the actual surface shape of n. -/
structure StrongParadigm where
  nomForm : String
  oblForm : String
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
    weakAllomorphyPattern.violatesABA = true := by native_decide

/-- Therefore the weak alternation is not contiguous on the case
    containment hierarchy. -/
theorem weak_not_contiguous :
    weakAllomorphyPattern.isContiguous = false := by native_decide

/-- In contrast, the strong alternation (ABB = NOM vs oblique) is
    contiguous — consistent with case-conditioned VI. -/
def strongAllomorphyPattern : AllomorphyPattern :=
  { nom := 0, acc := 1, gen := 1, dat := 1 }

theorem strong_contiguous :
    strongAllomorphyPattern.isContiguous = true := by native_decide

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
    (buildTableau stemCandidates stemRanking stemCandidates_ne).optimal
      = [.ll_H] := by native_decide

-- ============================================================================
-- § 5: Summary Theorems
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
    strongAllomorphyPattern.isContiguous = true ∧
    weakAllomorphyPattern.isContiguous = false := ⟨by native_decide, by native_decide⟩

/-- The outward sensitivity of the weak alternation: the form of *n*
    (closer to root) depends on material further from the root (case
    and agreement suffixes). Under root-out VI, this is impossible —
    suffixes are not yet inserted when *n* receives its exponent. -/
theorem weak_is_outward_sensitive :
    isOutwardSensitive (conditioningPos := 2) (targetPos := 1) = true := rfl

-- ============================================================================
-- § 6: Integration with Core Infrastructure
-- ============================================================================

/-- Telugu's `hasACC` exactly mirrors `Core.Case.isNonnom` via `toCore`.
    This confirms the study's case-feature assignments are consistent with
    the containment hierarchy infrastructure. -/
theorem hasACC_eq_isNonnom (c : TeluguCase) :
    c.hasACC = c.toCore.isNonnom := by
  cases c <;> rfl

/-- The Telugu 5-case inventory is contiguous on Blake's typological
    hierarchy (@cite{blake-1994}). -/
theorem telugu_inventory_valid :
    Core.validInventory [.nom, .acc, .gen, .dat, .loc] = true := by native_decide

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
    strongAllomorphyPattern.isContiguous = true ∧
    -- (2) Weak is non-contiguous
    weakAllomorphyPattern.isContiguous = false ∧
    -- (3) Weak is outward-sensitive
    isOutwardSensitive (conditioningPos := 2) (targetPos := 1) = true := by
  exact ⟨by native_decide, by native_decide, rfl⟩

end Phenomena.Allomorphy.TeluguNounStems.Studies.Aitha2026
