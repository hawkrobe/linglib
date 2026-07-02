import Linglib.Features.Case.Basic
import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Order
import Linglib.Morphology.Case.Allomorphy
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.OptimalityTheory.Predict
import Linglib.Phonology.Prosody.Foot
import Linglib.Morphology.DM.VocabularyInsertion
import Linglib.Phonology.OptimalityTheory.Stratal
open Morphology.Case.Allomorphy

/-!
# The Nouns that Say *-ni* [aitha-2026]

Aitha, A. (2026). The nouns that say *-ni*: Morpheme-specific phonology
in Telugu. *Natural Language & Linguistic Theory* 44:16.

## Overview

Telugu nouns exhibit two stem alternation patterns:

1. **Strong alternation**: NOM *il-lu* vs oblique *in-ṭi* ('house').
   Genuine case-conditioned contextual allomorphy, analyzed via DM
   Vocabulary Insertion with [mcfadden-2018]'s case containment
   hierarchy. The NOM-vs-oblique split follows from the Elsewhere
   Condition: a rule conditioned on [ACC] is more specific than an
   unconditioned default.

2. **Weak alternation**: NOM *samudr-am* vs ACC *samudr-āni* ('ocean').
   Surface pattern looks like case-conditioned allomorphy but is
   phonological. Three diagnostics show it cannot be case allomorphy:
   (a) the ABAB paradigm shape violates [caha-2009]'s *ABA
   constraint; (b) noncase agreement suffixes trigger the alternation;
   (c) the conditioning requires strict linear adjacency (phonological,
   not structural locality).

   The alternation is derived in Stratal OT ([kiparsky-2000]):
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
- §6: Word-based surface form prediction
-/

namespace Aitha2026

open Core Constraints OptimalityTheory Core.Optimization Core.Optimization.Evaluation
open Morphology.DM.VI
open Prosody

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
def TeluguCase.toCore : TeluguCase → Case
  | .nom => .nom
  | .acc => .acc
  | .gen => .gen
  | .dat => .dat
  | .loc => .loc

/-- Is this Telugu case nonnominative? Derived from
    `Case.IsNonnominative`, which is `(.acc : Case) ≤ c` under the
    [caha-2009]/[mcfadden-2018] containment ordering. The full
    containment hierarchy lives at `Syntax.Case.Order` (`containmentRank`,
    `cahaLE`); Aitha's *n*-head VI rules condition on this binary
    projection of the hierarchy down to a NOM-vs-oblique contrast at
    the *n* head — the layered hierarchy is the substrate, the binary
    split is the Telugu-*n*-specific reduction. -/
def TeluguCase.IsNonnom (c : TeluguCase) : Prop :=
  Case.IsNonnominative c.toCore

instance (c : TeluguCase) : Decidable (TeluguCase.IsNonnom c) :=
  inferInstanceAs (Decidable (Case.IsNonnominative c.toCore))

-- ────────────────────────────────────────────────────────────────────
-- Strong noun paradigm: *illu* 'house'
-- ────────────────────────────────────────────────────────────────────

/-- Root class for strongly suppletive nouns.
    [aitha-2026] lists 7 subclasses, all sharing the NOM-vs-oblique
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
  if c.IsNonnom then p.oblForm else p.nomForm

-- ────────────────────────────────────────────────────────────────────
-- Weak noun paradigm: *samudram* 'ocean'
-- ────────────────────────────────────────────────────────────────────

/-- Stem form in weakly suppletive nouns. -/
inductive WeakStemForm where
  | short  -- -am (before heavy σ or domain-finally)
  | long   -- -āni (before light σ within Word)
  deriving DecidableEq, Repr

/-- The weak noun paradigm for *samudram* 'ocean'.
    Data from [krishnamurti-gwynn-1985]. -/
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
    Carries the root class and the Telugu case directly; nonnominativity
    is derived from `case.IsNonnom` rather than stored as a Bool — so
    the McFadden 2018 / Caha 2009 containment substrate is the source of
    truth at every VI use site. -/
structure NContext where
  rootClass : StrongClass
  case : TeluguCase
  deriving DecidableEq, Repr

/-- VI rule for NOM *n* of the -lu∼-ṭi class.
    No nonnominative requirement → this is the elsewhere/default rule. -/
def viLuNom : VocabItem NContext Unit :=
  { exponent := "lu"
  , contextMatch := λ ctx => ctx.rootClass == .luTi
  , specificity := 1 }

/-- VI rule for oblique *n* of the -lu∼-ṭi class.
    Requires `case.IsNonnom` → more specific, wins over `viLuNom` in non-NOM. -/
def viLuObl : VocabItem NContext Unit :=
  { exponent := "ṭi"
  , contextMatch := λ ctx => ctx.rootClass == .luTi && decide ctx.case.IsNonnom
  , specificity := 2 }

/-- VI rule for NOM *n* of the -u∼-i class. -/
def viUNom : VocabItem NContext Unit :=
  { exponent := "u"
  , contextMatch := λ ctx => ctx.rootClass == .uI
  , specificity := 1 }

/-- VI rule for oblique *n* of the -u∼-i class. -/
def viUObl : VocabItem NContext Unit :=
  { exponent := "i"
  , contextMatch := λ ctx => ctx.rootClass == .uI && decide ctx.case.IsNonnom
  , specificity := 2 }

/-- All VI rules for strong noun *n*-exponents. -/
def strongVIRules : List (VocabItem NContext Unit) :=
  [viLuNom, viLuObl, viUNom, viUObl]

/-- Build the morphosyntactic context for VI from Telugu case + root class. -/
def mkNContext (rc : StrongClass) (c : TeluguCase) : NContext :=
  ⟨rc, c⟩

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

/-- The weak alternation violates [caha-2009]'s *ABA constraint.
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

    Data from [aitha-2026]'s full(er) paradigm including agreement:
    - ACC *-ni*: light σ within Word → long (*samudr-āni-ni*)
    - DAT *-ki*: light σ within Word → long (*samudr-āni-ki*)
    - 1SG *-ni*: light σ within Word → long (*samudr-āni-ni*)
    - 2SG *-vi*: light σ within Word → long (*samudr-āni-vi*)
    - NOM *-∅*: no following σ → short (*samudr-am-∅*)
    - GEN *-∅*: no following σ → short (*samudr-am-∅*)
    - 3SG *-∅*: no following σ → short (*samudr-am-∅*)
    - P *-lō*: separate Word → short (*samudr-am-lō*)
    - P *-gurinci*: separate Word → short (*samudr-am-gurinci*)
    - P *-eduru*: separate Word → short (*samudr-am-eduru*)

    Note: -gurinci and -eduru begin with light syllables, yet still
    trigger the short form. The conditioning factor is Word membership,
    not syllable weight of the following element per se. -/
inductive FollowingContext where
  | noSuffix           -- NOM, GEN, 3SG: no overt suffix
  | lightWithinPrWd    -- ACC -ni, DAT -ki, 1SG -ni, 2SG -vi
  | separatePrWd       -- postpositions (-lō, -gurinci, -eduru): separate Word
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

/-- Postposition in a separate Word → short form (regardless of
    whether the postposition starts with a light or heavy syllable). -/
theorem separate_prwd_triggers_short :
    weakFormPredicted .separatePrWd = .short := rfl

-- ────────────────────────────────────────────────────────────────────
-- Telugu nominal agreement paradigm
-- ────────────────────────────────────────────────────────────────────

/-- Telugu nominal predicative agreement suffixes.
    Only 1SG and 2SG are overt; 3SG and all plurals are null.
    Data from [aitha-2026]. -/
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
    Both are light syllables within Word — the conditioning is
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
    [aitha-2026] argues (§4.2) that the surface alternants *-am* and
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
    [aitha-2026] (§4.1) shows this via Q-postposing constructions:
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

/-- Map each candidate to its canonical `Prosody.Footing` over weighted σ
    (feet are `Prosody.Foot`s; an unfooted σ is a bare weight). -/
def StemCandidate.toFooting : StemCandidate → Footing Syllable.Weight
  | .llU_H => [.inl ⟨[.light, .light], 0⟩, .inr .heavy]
  | .l_l_H => [.inl ⟨[.light], 0⟩, .inl ⟨[.light], 0⟩, .inl ⟨[.heavy], 0⟩]
  | .ll_H  => [.inl ⟨[.light, .light], 0⟩, .inl ⟨[.heavy], 0⟩]

/-- ALL-FT-LEFT: per foot, the σ intervening from the left edge of the domain. -/
def allFtLeftOf (fc : Footing Syllable.Weight) : Nat :=
  let rec go : Footing Syllable.Weight → Nat → Nat
    | [], _ => 0
    | .inl f :: rest, pos => pos + go rest (pos + f.syllables.length)
    | .inr _ :: rest, pos => go rest (pos + 1)
  go fc 0

/-- FT-BIN(μ): penalizes non-bimoraic feet (a foot whose morae ≠ 2). -/
def cFtBin : Constraint StemCandidate :=
  λ c => (c.toFooting.feet.filter (fun f => decide (Foot.moraCount id f ≠ 2))).length

/-- PARSE-SYL: penalizes unparsed (stray) syllables. -/
def cParseSyl : Constraint StemCandidate :=
  λ c => c.toFooting.strays.length

/-- ALL-FT-LEFT: penalizes feet distant from the left edge. -/
def cAllFtLeft : Constraint StemCandidate :=
  λ c => allFtLeftOf c.toFooting

/-- Stem-level constraint ranking: FT-BIN ≫ PARSE-SYL ≫ ALL-FT-LEFT.

    FT-BIN dominates PARSE-SYL: it is better to leave a syllable
    unparsed than to create a degenerate (monomoraic) foot. -/
def stemRanking : List (Constraint StemCandidate) :=
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
    stemCandidates.map cFtBin = [0, 2, 0] := by decide

theorem stem_parsesyl_violations :
    stemCandidates.map cParseSyl = [1, 0, 0] := by decide

/-- The optimal Stem-level parse is (ˈsa.mu).(ˌdram): two well-formed
    moraic trochees, (LL)(H), with no unparsed syllables. -/
theorem stem_optimal :
    (Tableau.ofRanking stemCandidates stemRanking stemCandidates_ne).optimal
      = {.ll_H} := by decide

-- ============================================================================
-- § 5: Word-Level Phonology (Stratal OT)
-- ============================================================================

section WordLevel

open OptimalityTheory.Stratal
open Prosody

-- ────────────────────────────────────────────────────────────────────
-- Rich phonological exponent substrate ([alderete-1999])
-- ────────────────────────────────────────────────────────────────────

/-- Prosodic prespecification for a morphological exponent.
    `none` means the property is unspecified (determined by the
    phonological grammar alone). -/
structure ProsodicPrespec where
  inherentStress : Option Bool := none
  deriving DecidableEq, Repr

/-- A rich exponent: segmental content plus optional prosodic
    prespecification. Used here for Telugu singular *-ni*'s lexically
    prespecified stress ([aitha-2026] §5; precedent
    [alderete-1999] on English stress-shifting suffixes). -/
structure RichExponent where
  segments : String
  prosody : ProsodicPrespec := {}
  deriving DecidableEq, Repr

/-- Create a stressed exponent. -/
def RichExponent.stressed (s : String) : RichExponent :=
  ⟨s, { inherentStress := some true }⟩

-- ────────────────────────────────────────────────────────────────────
-- Word-level phonology
-- ────────────────────────────────────────────────────────────────────

/-- The singular suffix *-ni* carries prespecified stress.
    This prespecification, interacting with FT-BIN(μ) and IDENT-STRESS
    at the Word level, drives deletion of *-ni* when it is Word-final
    and cannot form a binary foot. -/
def sgNiExponent : RichExponent := .stressed "ni"

theorem sgNi_is_stressed :
    sgNiExponent.prosody.inherentStress = some true := rfl

-- ────────────────────────────────────────────────────────────────────
-- § 5.1: NOM — Word-final stressed -ni (no following light suffix)
-- ────────────────────────────────────────────────────────────────────

/-- Word-level candidates for the NOM input (ˈsa.mu).(ˌdram).ní.
    Stressed *-ni* is Word-final: no following suffix to pair with. -/
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
def wordNomRanking : List (Constraint WordCandNom) :=
  [ (λ | .destress => 1 | _ => 0)
  , (λ | .degenerateFoot => 1 | _ => 0)
  , (λ | .deleteI_coda => 1 | _ => 0)
  , (λ | .deleteIM => 1 | _ => 0)
  , (λ | .deleteI_coda => 1 | .deleteIM => 2 | .deleteNi => 1 | _ => 0)
  , (λ | .deleteI_coda => 1 | .deleteIM => 2 | .deleteNi => 2 | _ => 0) ]

def wordNomCands : List WordCandNom :=
  [.destress, .degenerateFoot, .deleteI_coda, .deleteIM, .deleteNi]

theorem wordNomCands_ne : wordNomCands ≠ [] := by decide

/-- Word level, NOM: Word-final stressed *-ni* is deleted.
    Surface: *samudr-am* (short form). -/
theorem wordNom_optimal :
    (Tableau.ofRanking wordNomCands wordNomRanking wordNomCands_ne).optimal
      = {.deleteNi} := by native_decide

-- ────────────────────────────────────────────────────────────────────
-- § 5.2: DAT — light -ki follows within Word
-- ────────────────────────────────────────────────────────────────────

/-- Word-level candidates for the DAT input (ˈsa.mu).(ˌdram).ní.ki.
    The light suffix *-ki* is Word-internal, so *-ni* can form a
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

/-- The constraint inventory of [aitha-2026], as a label type: cross-stratum identity
is by label, not by candidate type (the strata have different candidate types). The
paper's tables abbreviate stress faithfulness as both ID-STR and IDENT-STRESS; both
spellings are preserved as distinct labels. -/
inductive Con
  | distZero | alignR | idStress | ftBin | maxMora | max | identStress
  deriving DecidableEq, Repr

/-- Word-level ranking for DAT. Same constraint set as NOM, with
    \*DIST-0 additionally relevant (eliminates faithful candidate).

    | Candidate       | \*DIST-0 | AL-R | ID-STR | FT-BIN | MAX(μ) | MAX |
    |-----------------|----------|------|--------|--------|--------|-----|
    | faithful        |   1\*    |      |        |        |        |     |
    | resyllabify     |          |  1\* |        |        |        |     |
    | deleteNi        |          |      |        |   1\*  |   1    |  2  |
    | ☞ compLengthen  |          |      |        |        |   1    |  1  | -/
def wordDatRanking : List (Con × Constraint WordCandDat) :=
  [ (.distZero, λ | .faithful => 1 | _ => 0)
  , (.alignR,   λ | .resyllabify => 1 | _ => 0)
  , (.idStress, λ _ => 0)
  , (.ftBin,    λ | .deleteNi => 1 | _ => 0)
  , (.maxMora,  λ | .deleteNi => 1 | .compLengthen => 1 | _ => 0)
  , (.max,      λ | .deleteNi => 2 | .compLengthen => 1 | _ => 0) ]

def wordDatCands : List WordCandDat :=
  [.faithful, .resyllabify, .deleteNi, .compLengthen]

theorem wordDatCands_ne : wordDatCands ≠ [] := by decide

/-- Word level, DAT: /mn/ boundary repaired by compensatory lengthening.
    Surface: *samudr-āni-ki* (long form). -/
theorem wordDat_optimal :
    (Tableau.ofRanking wordDatCands (wordDatRanking.map (·.2)) wordDatCands_ne).optimal
      = {.compLengthen} := by native_decide

-- ────────────────────────────────────────────────────────────────────
-- § 5.3: Core result — same constraints, different outputs
-- ────────────────────────────────────────────────────────────────────

/-- The same constraint system derives both surface forms from the same
    underlying *-am-ni*. The difference is purely phonological: whether
    a light suffix follows within the Word.

    - NOM (no suffix): *-ni* is Word-final → deleted → **short**
    - DAT (*-ki* follows): *-ni* pairs with *-ki* → /mn/ repaired → **long**

    This completes the derivation that the `weakFormPredicted` function
    (§3) stipulates: the alternation is now DERIVED from OT constraint
    interaction, not encoded by fiat. -/
theorem word_level_derives_alternation :
    (Tableau.ofRanking wordNomCands wordNomRanking wordNomCands_ne).optimal
      = {.deleteNi} ∧
    (Tableau.ofRanking wordDatCands (wordDatRanking.map (·.2)) wordDatCands_ne).optimal
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
-- § 5b: Phrase-Level Phonology — Postpositional Case
-- ============================================================================

/-! Paper §5.3 develops the Phrase-level stratum, where constraint
ranking is *re*ranked relative to the Word level. This is the empirical
core of the "Stratal" claim: the same constraint inventory (`*DIST-0`,
`MAX`, `IDENT-STRESS`, ...) is *demoted* or *promoted* across the
Word→Phrase boundary, producing different optimal outputs for the
same segmental configuration.

Key reranking from paper §5.3: `*DIST-0` is **demoted** from above `MAX`
at the Word level (deriving m-deletion before singular *-ni*) to below
`MAX` at the Phrase level (tolerating m-n contact across postposition
boundary). This subsection encodes paper tableau (66) for `samudram nunci`
'from ocean': the Phrase-level grammar tolerates the m-n contact
across the postposition boundary that the Word-level grammar would have
repaired by compensatory lengthening. -/

section PhraseLevel

open OptimalityTheory.Stratal

/-- Phrase-level candidates for the postpositional input
    `('sa.mu).('dram).('nun).('ci)` ('ocean-from'), the Word-level
    output of the NOM stratum concatenated with the postposition
    *-nunci* 'from'. -/
inductive PhraseCandPostp where
  /-- (ˈsa.mu).(ˌdrā).(ˌnun).(ˌci) — /m/ deleted, /a/ → /ā/ via CL. -/
  | compLengthen
  /-- (ˈsa.mu).(ˌdra).(ˌnun).(ˌci) — /m/ deleted, no CL. -/
  | deleteM
  /-- (ˈsa.mu).(ˌdram).(ˌun).(ˌci) — /n/ of postposition deleted. -/
  | deleteN
  /-- ☞ (ˈsa.mu).(ˌdram).(ˌnun).(ˌci) — faithful; m-n contact retained. -/
  | faithful
  deriving DecidableEq, Repr

/-- Phrase-level ranking for postposition contexts.

    Crucially, `*DIST-0` is now *below* `MAX` — the reverse of the Word
    stratum (file:584). This is the headline cross-stratum reranking of
    paper §5.3.

    | Candidate     | IDENT-STRESS | MAX | *DIST-0 | AL-R |
    |---------------|--------------|-----|---------|------|
    | compLengthen  |              | 1*  |         | 1    |
    | deleteM       |              | 1   |         | 1    |
    | deleteN       |              | 1   |         |      |
    | ☞ faithful    |              |     | 1       |      | -/
def phrasePostpRanking : List (Con × Constraint PhraseCandPostp) :=
  [ (.identStress, λ _ => 0)
  , (.max,         λ | .compLengthen => 1 | .deleteM => 1 | .deleteN => 1 | _ => 0)
  , (.distZero,    λ | .faithful => 1 | _ => 0)
  , (.alignR,      λ | .compLengthen => 1 | .deleteM => 1 | _ => 0) ]

def phrasePostpCands : List PhraseCandPostp :=
  [.compLengthen, .deleteM, .deleteN, .faithful]

theorem phrasePostpCands_ne : phrasePostpCands ≠ [] := by decide

/-- Phrase level: postposition `nunci` 'from'. The faithful output wins —
    `*DIST-0` is demoted below MAX at Phrase level, so m-n contact
    is tolerated rather than repaired. Surface: *samudram nunci*. -/
theorem phrasePostp_optimal :
    (Tableau.ofRanking phrasePostpCands (phrasePostpRanking.map (·.2)) phrasePostpCands_ne).optimal
      = {.faithful} := by native_decide

end PhraseLevel

-- ============================================================================
-- § 5c: Stratal Derivation Records
-- ============================================================================

/-! Wires the existing per-stratum tableaux into `StratalDerivation`
records — making the file's "Stratal OT" claim explicit at the type
level. Each derivation records the optimal output at each cycle; the
candidate types differ across strata because GEN produces different
representations at each level. -/

section StratalRecords

open OptimalityTheory.Stratal

/-- The Stratal-OT derivation of NOM `samudram` 'ocean-NOM'.

    - **Stem**: input `/samudr-am/`, optimal parse `(ˈsa.mu).(ˌdram)` (= `.ll_H`).
    - **Word**: stem output combined with prosodified `-ni` singular suffix
      and a null NOM exponent; Word-final stressed `-ni` is deleted; output
      `samudram` (= `.deleteNi`).
    - **Phrase**: no overt postposition follows, so no Phrase-level repairs
      are required. Surface = Word output. -/
def nomDerivation : StratalDerivation StemCandidate WordCandNom WordCandNom where
  underlyingForm := .ll_H
  stemOutput     := .ll_H
  wordOutput     := .deleteNi
  phraseOutput   := .deleteNi

/-- DAT derivation `samudrāniki` — Word-level CL produces the long form
    via m-deletion + /a/ → /ā/. -/
def datDerivation : StratalDerivation StemCandidate WordCandDat WordCandDat where
  underlyingForm := .ll_H
  stemOutput     := .ll_H
  wordOutput     := .compLengthen
  phraseOutput   := .compLengthen

/-- Postpositional derivation `samudram nunci` — Phrase-level reranking
    blocks the Word-level CL repair. Same input segmental shape as DAT
    at the m-n contact, different output because `*DIST-0` is demoted
    at Phrase. -/
def postpDerivation : StratalDerivation StemCandidate WordCandNom PhraseCandPostp where
  underlyingForm := .ll_H
  stemOutput     := .ll_H
  wordOutput     := .deleteNi
  phraseOutput   := .faithful

/-- The three derivations agree at the stem stratum (same input shape)
    but diverge at later strata depending on what follows the noun. -/
theorem derivations_share_stem :
    nomDerivation.stemOutput = datDerivation.stemOutput ∧
    nomDerivation.stemOutput = postpDerivation.stemOutput := by
  exact ⟨rfl, rfl⟩

end StratalRecords

-- ============================================================================
-- § 5d: Cross-Stratum Reranking
-- ============================================================================

/-! Paper §5.3 (p. 31) makes the headline Stratal-OT claim that `*DIST-0`
is **demoted** going from the Word stratum to the Phrase stratum. The
substrate's `IsPromotedAcross` / `IsDemotedAcross` operate on constraint
*labels* — necessary here because `wordDatRanking` and `phrasePostpRanking`
have different candidate types (`WordCandDat` vs `PhraseCandPostp`),
so the same-`C` `isPromoted`/`isDemoted` would not typecheck. -/

section CrossStratumReranking

open OptimalityTheory.Stratal

/-- `*DIST-0` is at the *highest* rank in the Word DAT ranking
    (`wordDatRanking`, position 0) and at a *lower* rank in the Phrase
    postpositional ranking (`phrasePostpRanking`, position 2). This is
    the demotion across the Word→Phrase boundary that the paper's §5.3
    central reranking claim makes — and it is precisely what derives
    m-retention at phrase boundaries vs m-deletion + CL inside
    the prosodic word. -/
theorem dist0_demoted_phrase_relative_to_word :
    OptimalityTheory.Stratal.IsDemotedAcross .distZero phrasePostpRanking wordDatRanking := by
  decide

/-- Conversely, `MAX` is **promoted** going Word → Phrase. Dual aspect
    of the same reranking. -/
theorem max_promoted_phrase_relative_to_word :
    OptimalityTheory.Stratal.IsPromotedAcross .max phrasePostpRanking wordDatRanking := by
  decide

end CrossStratumReranking

-- ============================================================================
-- § 6: Word-Based Surface Form Prediction
-- ============================================================================

section PrWdIntegration

open Prosody

/-- Prosodic-word membership of a following element: parsed inside the host ω
    (stem, derivational/inflectional/agreement suffixes) or forming its own ω
    (postpositions). The conditioning dimension is prosodic, not morphosyntactic
    ([aitha-2026] §3.2). -/
inductive WordMembership where
  | internal | external
  deriving DecidableEq, Repr

/-- A following morphological element: its ω-membership and the weight of its
    initial syllable — the Telugu weak-noun long-form conditioning. -/
structure MorphElement where
  membership    : WordMembership
  initialWeight : Syllable.Weight
  deriving DecidableEq, Repr

/-- The long stem form surfaces iff the following element is ω-internal and
    begins with a light syllable; ω-external postpositions never trigger it,
    even with a light initial syllable. -/
abbrev MorphElement.triggersLongForm (m : MorphElement) : Prop :=
  m.membership = .internal ∧ m.initialWeight = .light

/-- Predict the weak stem form from the following morphological element: the
    long form surfaces iff the following element is ω-internal AND begins with a
    light syllable. -/
def weakSurfaceFromPrWd : Option MorphElement → WeakStemForm
  | some m => if m.triggersLongForm then .long else .short
  | none   => .short  -- no following element → Word-final → short

-- Case suffixes

theorem acc_ni_long :
    weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = .long := rfl

theorem dat_ki_long :
    weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = .long := rfl

theorem nom_null_short :
    weakSurfaceFromPrWd none = .short := rfl

theorem gen_null_short :
    weakSurfaceFromPrWd none = .short := rfl

-- Agreement suffixes (the decisive diagnostic)

theorem agr_1sg_ni_long :
    weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = .long := rfl

theorem agr_2sg_vi_long :
    weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = .long := rfl

-- Postpositions (Word-external → always short)

theorem postp_lo_short :
    weakSurfaceFromPrWd (some ⟨.external, .heavy⟩) = .short := rfl

/-- Postposition *-gurinci* 'about' begins with a light syllable, yet
    triggers the short form — because it is Word-external. This is
    the key evidence that the conditioning is Word membership, not
    syllable weight alone. -/
theorem postp_gurinci_short :
    weakSurfaceFromPrWd (some ⟨.external, .light⟩) = .short := rfl

/-- The Word-based prediction matches the original paradigm data for
    all five cases in the canonical weak paradigm. -/
theorem prwd_matches_paradigm :
    weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = .long ∧
    weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = .long ∧
    weakSurfaceFromPrWd none = .short ∧
    weakSurfaceFromPrWd none = .short ∧
    weakSurfaceFromPrWd (some ⟨.external, .heavy⟩) = .short :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The Word-based prediction agrees with the original `weakParadigm`
    for all five cases. This closes the gap between the phonological
    derivation (OT + Word) and the empirical data (paradigm). -/
theorem prwd_agrees_with_paradigm :
    (weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = weakParadigm .acc) ∧
    (weakSurfaceFromPrWd (some ⟨.internal, .light⟩) = weakParadigm .dat) ∧
    (weakSurfaceFromPrWd none = weakParadigm .nom) ∧
    (weakSurfaceFromPrWd none = weakParadigm .gen) ∧
    (weakSurfaceFromPrWd (some ⟨.external, .heavy⟩) = weakParadigm .loc) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end PrWdIntegration

-- ============================================================================
-- § 7: Summary Theorems
-- ============================================================================

/-- The two alternation patterns have fundamentally different analyses:

    1. Strong alternation: ABB pattern (contiguous on containment
       hierarchy) → case-conditioned contextual allomorphy (VI).
    2. Weak alternation: ABAB pattern (violates *ABA) → phonological
       alternation conditioned by syllable weight within Word.

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

-- The Telugu 5-case inventory is contiguous on Blake's typological
-- hierarchy ([blake-1994]).
example : Case.IsValidInventory ({.nom, .acc, .gen, .dat, .loc} : Finset Case) := by
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
-- § 9: Connection to Moraic CL Theory ([hayes-1989])
-- ============================================================================

section MoraicCLConnection

open Phonology (Segment)
open Prosody (Syllable)

/-- Telugu has Weight by Position: coda consonants bear morae, making CVC
    syllables heavy. This is assumed by the Stem-level parse, where *dram*
    (CVC) is treated as heavy (2μ). -/
def teluguWBP : Bool := true

/-- In a WBP language like Telugu, deleting a coda consonant strands one
    mora — this is [hayes-1989]'s **classical CL**.

    This grounds the DAT `compLengthen` candidate: /m/ deletion from /dram/
    strands a mora, which spreads left to yield /drā/. The CL repair is not a
    stipulated candidate — it is available precisely because Telugu has WBP. -/
theorem telugu_coda_deletion_strands_mora (o n c : Segment) :
    ((Syllable.ofCV [o] [n] [c] teluguWBP).strand 1).strandedCount = 1 := rfl

/-- Moraic conservation ([hayes-1989]): the mora stranded by /m/ deletion is
    absorbed by leftward spreading to /a/, yielding /ā/ (2μ). Total mora count
    is unchanged. -/
theorem telugu_cl_conservation (o n c : Segment) :
    let σ := Syllable.ofCV [o] [n] [c] teluguWBP
    σ.moraCount = ((σ.strand 1).relicense).moraCount := rfl

end MoraicCLConnection

-- ============================================================================
-- § 10: Generic ConstraintSystem Predictions
-- ============================================================================

/-! All three Telugu OT tableaux lift to generic `ConstraintSystem`s via
`tableauSystem`. The Stratal-OT derivation of the weak alternation
becomes a probability-1 claim per stratum. -/

section PredictAPI
open Core.Optimization Constraints

/-- Stem-level metrical parse tableau as a generic `ConstraintSystem`. -/
noncomputable def stemSystem : ConstraintSystem StemCandidate (LexProfile Nat 3) :=
  tableauSystem (Tableau.ofRanking stemCandidates stemRanking stemCandidates_ne)

/-- Probability 1 on (LL)(H): two well-formed moraic trochees. -/
theorem stemSystem_predict_ll_H :
    stemSystem.predict StemCandidate.ll_H = 1 :=
  tableauSystem_predict_unique_winner _ _ stem_optimal

/-- Word-level NOM tableau as a generic `ConstraintSystem`. -/
noncomputable def wordNomSystem : ConstraintSystem WordCandNom (LexProfile Nat 6) :=
  tableauSystem (Tableau.ofRanking wordNomCands wordNomRanking wordNomCands_ne)

/-- Probability 1 on `deleteNi`: Word-final stressed *-ni* is deleted. -/
theorem wordNomSystem_predict_deleteNi :
    wordNomSystem.predict WordCandNom.deleteNi = 1 :=
  tableauSystem_predict_unique_winner _ _ wordNom_optimal

/-- Word-level DAT tableau as a generic `ConstraintSystem`. -/
noncomputable def wordDatSystem : ConstraintSystem WordCandDat (LexProfile Nat 6) :=
  tableauSystem (Tableau.ofRanking wordDatCands (wordDatRanking.map (·.2)) wordDatCands_ne)

/-- Probability 1 on `compLengthen`: /m/ deletion + CL yields *-āni*. -/
theorem wordDatSystem_predict_compLengthen :
    wordDatSystem.predict WordCandDat.compLengthen = 1 :=
  tableauSystem_predict_unique_winner _ _ wordDat_optimal

end PredictAPI

end Aitha2026
