import Linglib.Typology.WordOrder
import Linglib.Typology.Adposition
import Linglib.Typology.Universal
import Linglib.Fragments.English.WordOrder
import Linglib.Fragments.English.Adposition
import Linglib.Fragments.Japanese.WordOrder
import Linglib.Fragments.Japanese.Adposition
import Linglib.Fragments.Mandarin.WordOrder
import Linglib.Fragments.Mandarin.Adposition
import Linglib.Fragments.Korean.WordOrder
import Linglib.Fragments.Korean.Adposition
import Linglib.Fragments.Arabic.ModernStandard.WordOrder
import Linglib.Fragments.Arabic.ModernStandard.Adposition
import Linglib.Fragments.Welsh.WordOrder
import Linglib.Fragments.Welsh.Adposition
import Linglib.Fragments.Irish.WordOrder
import Linglib.Fragments.Irish.Adposition
import Linglib.Fragments.Turkish.WordOrder
import Linglib.Fragments.Turkish.Adposition
import Linglib.Fragments.HindiUrdu.WordOrder
import Linglib.Fragments.HindiUrdu.Adposition
import Linglib.Fragments.Basque.WordOrder
import Linglib.Fragments.Basque.Adposition
import Linglib.Fragments.Slavic.Russian.WordOrder
import Linglib.Fragments.Slavic.Russian.Adposition
import Linglib.Fragments.Swahili.WordOrder
import Linglib.Fragments.Swahili.Adposition
import Linglib.Fragments.Indonesian.WordOrder
import Linglib.Fragments.Indonesian.Adposition
import Linglib.Fragments.Tzotzil.WordOrder
import Linglib.Fragments.Tzotzil.Adposition
import Linglib.Fragments.Hixkaryana.WordOrder
import Linglib.Fragments.Hixkaryana.Adposition

/-!
# Greenberg 1963: Implicational Universals on Basic Word Order
@cite{greenberg-1963} @cite{dryer-haspelmath-2013}

@cite{greenberg-1963} stated 45 cross-linguistic implicational universals on
basic constituent order, adposition order, and related construction-pair
correlations. This file formalises three of the most cited, tested over a
curated 15-language Fragment-derived sample:

- **Universal 1**: subject-before-object orders (SOV + SVO + VSO) dominate
  over object-before-subject orders (VOS + OVS + OSV).
- **Universal 3**: VSO languages are prepositional.
- **Universal 4**: SOV languages are postpositional (with overwhelmingly
  greater than chance frequency).

All three are tested over `fragmentSample`, a 15-language Fragment-derived
sample. The substrate type `ImplicationalUniversal` lives in
`Linglib/Typology/Universal.lean`. WALS-aggregate distributional claims
(SOV-most-common, SV-dominates-VS, etc.) live in
`Studies/DryerHaspelmath2013.lean`.

The 15-language sample bundles each language's Fragment-sourced
`WordOrderProfile` (Ch 81/82/83) and `Option AdpositionOrder` (Ch 85). Per-
language data lives in `Fragments/{Lang}/{WordOrder,Adposition}.lean`; the
sample just bundles them with an ISO code and a human-readable name. Sample
shape is hand-curated to span the four major basic-order classes — Tzotzil
(VOS) and Hixkaryana (OVS) are deliberately included so U1's "object-
initial languages exist but are rare" statistical character can be tested
non-vacuously.
-/

namespace Phenomena.WordOrder.Studies.Greenberg1963

open _root_.Typology (ImplicationalUniversal)

-- ============================================================================
-- §1. Sample: per-language data sourced from Fragment files
-- ============================================================================

/-- A sample-language entry for the Greenberg / cross-chapter theorems:
    Fragment-sourced word-order profile plus optional adposition order. -/
structure SampleEntry where
  iso : String
  name : String
  wordOrder : _root_.Typology.WordOrder.WordOrderProfile
  adposition : Option _root_.Typology.Adposition.AdpositionOrder
  deriving Repr, DecidableEq

/-- Hand-verified 15-language sample spanning the four major basic-order
    classes (SOV, SVO, VSO, plus a couple non-SVO entries) with adposition
    data attested in WALS. Used for stating cross-linguistic Greenbergian
    universals via `Typology.ImplicationalUniversal`. -/
def fragmentSample : Finset SampleEntry :=
  { ⟨ "eng", "English",    Fragments.English.wordOrder,         Fragments.English.adposition ⟩
  , ⟨ "jpn", "Japanese",   Fragments.Japanese.wordOrder,        Fragments.Japanese.adposition ⟩
  , ⟨ "cmn", "Mandarin",   Fragments.Mandarin.wordOrder,        Fragments.Mandarin.adposition ⟩
  , ⟨ "kor", "Korean",     Fragments.Korean.wordOrder,          Fragments.Korean.adposition ⟩
  , ⟨ "arb", "Arabic",     Fragments.Arabic.ModernStandard.wordOrder,          Fragments.Arabic.ModernStandard.adposition ⟩
  -- VSO + prepositional (Celtic):
  , ⟨ "cym", "Welsh",      Fragments.Welsh.wordOrder,           Fragments.Welsh.adposition ⟩
  , ⟨ "gle", "Irish",      Fragments.Irish.wordOrder,           Fragments.Irish.adposition ⟩
  -- Additional SOV + postpositional:
  , ⟨ "tur", "Turkish",    Fragments.Turkish.wordOrder,         Fragments.Turkish.adposition ⟩
  , ⟨ "hin", "Hindi",      Fragments.HindiUrdu.wordOrder,       Fragments.HindiUrdu.adposition ⟩
  , ⟨ "eus", "Basque",     Fragments.Basque.wordOrder,          Fragments.Basque.adposition ⟩
  -- Additional SVO + prepositional:
  , ⟨ "rus", "Russian",    Fragments.Slavic.Russian.wordOrder,  Fragments.Slavic.Russian.adposition ⟩
  , ⟨ "swh", "Swahili",    Fragments.Swahili.wordOrder,         Fragments.Swahili.adposition ⟩
  , ⟨ "ind", "Indonesian", Fragments.Indonesian.wordOrder,      Fragments.Indonesian.adposition ⟩
  -- Object-initial / verb-final-object orders for shape diversity:
  , ⟨ "tzo", "Tzotzil",    Fragments.Tzotzil.wordOrder,         Fragments.Tzotzil.adposition ⟩    -- VOS
  , ⟨ "hix", "Hixkaryana", Fragments.Hixkaryana.wordOrder,      Fragments.Hixkaryana.adposition ⟩ -- OVS
  }

-- ============================================================================
-- §2. Per-entry predicates on basic constituent order
-- ============================================================================

/-- Language has WALS basic order VSO. -/
abbrev isVSO (p : SampleEntry) : Prop := p.wordOrder.basicOrder.IsVSO

/-- Language has WALS basic order SOV. -/
abbrev isSOV (p : SampleEntry) : Prop := p.wordOrder.basicOrder.IsSOV

/-- Subject-before-object basic orders (SOV, SVO, VSO). -/
abbrev isSubjectBeforeObject (p : SampleEntry) : Prop :=
  p.wordOrder.basicOrder.IsSubjectBeforeObject

/-- Object-before-subject basic orders (VOS, OVS, OSV). -/
abbrev isObjectBeforeSubject (p : SampleEntry) : Prop :=
  p.wordOrder.basicOrder.IsObjectBeforeSubject

/-- Language is classified as prepositional in WALS Ch 85. -/
abbrev isPrepositional (p : SampleEntry) : Prop :=
  p.adposition = some .prepositional

/-- Language is classified as postpositional in WALS Ch 85. -/
abbrev isPostpositional (p : SampleEntry) : Prop :=
  p.adposition = some .postpositional

-- ============================================================================
-- §3. Greenberg's Universals 1, 3, 4 over `fragmentSample`
-- ============================================================================
-- The proofs decide a quotient over a 15-element `Finset` literal — bumping
-- `maxRecDepth` is the same idiom mathlib uses for similar `Finset.decide`
-- sites (see `Typology/Universal.lean` for the discussion).

set_option maxRecDepth 4096 in
/-- @cite{greenberg-1963} Universal 1: in declarative sentences with nominal
    subject and object, the subject almost always precedes the object.
    Tested over `fragmentSample`: subject-before-object entries (SOV + SVO +
    VSO) outnumber object-before-subject entries (VOS + OVS + OSV) by more
    than 6×. The sample includes Tzotzil (VOS) and Hixkaryana (OVS) so the
    margin is non-trivial. -/
theorem greenberg_universal_1 :
    (fragmentSample.filter isSubjectBeforeObject).card >
    (fragmentSample.filter isObjectBeforeSubject).card * 6 := by
  decide

set_option maxRecDepth 4096 in
/-- @cite{greenberg-1963} Universal 3: "Languages with dominant VSO order
    are always prepositional." Tested over `fragmentSample`; antecedent is
    triggered by Arabic, Welsh, Irish, all of which are prepositional. -/
theorem greenberg_universal_3 :
    ImplicationalUniversal isVSO isPrepositional fragmentSample := by
  decide

set_option maxRecDepth 4096 in
/-- @cite{greenberg-1963} Universal 4: "With overwhelmingly greater than
    chance frequency, languages with normal SOV order are postpositional."
    Tested over `fragmentSample`; antecedent triggers Japanese, Korean,
    Turkish, Hindi, and Basque — all postpositional in WALS. -/
theorem greenberg_universal_4 :
    ImplicationalUniversal isSOV isPostpositional fragmentSample := by
  decide

-- ============================================================================
-- §4. Sample-wide drift sentinels
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Every Fragment in `fragmentSample` has an internally consistent
    word-order profile (per `Typology.WordOrder.WordOrderProfile.IsConsistent`).
    Catches drift if a future Fragment edit produces a contradictory profile
    like `{basicOrder := .sov, svOrder := .vs}`. -/
theorem fragment_sample_word_order_consistent :
    ∀ p ∈ fragmentSample, p.wordOrder.IsConsistent := by decide

end Phenomena.WordOrder.Studies.Greenberg1963
