import Mathlib.Data.Finset.Card
import Linglib.Features.WordOrder
import Linglib.Syntax.Category.Adposition.Order
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
import Linglib.Fragments.Mayan.Kiche.WordOrder
import Linglib.Fragments.Mayan.Kiche.Adposition

/-!
# Greenberg 1963: Implicational Universals on Basic Word Order
[greenberg-1963] [dryer-haspelmath-2013]

[greenberg-1963] stated 45 cross-linguistic implicational universals on
basic constituent order, adposition order, and related construction-pair
correlations. This file formalises three of the most cited, tested over a
curated 15-language Fragment-derived sample:

- **Universal 1**: subject-before-object orders (SOV + SVO + VSO) dominate
  over object-before-subject orders (VOS + OVS + OSV).
- **Universal 3**: VSO languages are prepositional.
- **Universal 4**: SOV languages are postpositional (with overwhelmingly
  greater than chance frequency).

All three are tested over `fragmentSample`, a 15-language Fragment-derived
sample. The `ImplicationalUniversal` predicate (every `P`-language is also `Q`)
is defined study-locally below. WALS-aggregate distributional claims
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

namespace Greenberg1963

/-- A Greenbergian implicational universal: every language in sample `s` with
    property `P` also has `Q` (the "no `P`-but-not-`Q` counterexample" claim,
    [greenberg-1963]). -/
def ImplicationalUniversal {α : Type*} (P Q : α → Prop) (s : Finset α) : Prop :=
  ∀ l ∈ s, P l → Q l

instance {α : Type*} (P Q : α → Prop) (s : Finset α)
    [DecidablePred P] [DecidablePred Q] : Decidable (ImplicationalUniversal P Q s) :=
  Finset.decidableDforallFinset

-- ============================================================================
-- §1. Sample: per-language data sourced from Fragment files
-- ============================================================================

/-- A sample-language entry for the Greenberg / cross-chapter theorems:
    Fragment-sourced word-order profile plus adposition order. -/
structure SampleEntry where
  iso : String
  name : String
  wordOrder : _root_.WordOrder.WordOrderProfile
  adposition : _root_.Adposition.AdpositionOrder
  deriving Repr, DecidableEq

/-- Hand-verified 15-language sample spanning the four major basic-order
    classes (SOV, SVO, VSO, plus a couple non-SVO entries) with adposition
    data attested in WALS. Used for stating cross-linguistic Greenbergian
    universals via `Typology.ImplicationalUniversal`. -/
def fragmentSample : Finset SampleEntry :=
  { ⟨ "eng", "English",    English.wordOrder,         English.adposition ⟩
  , ⟨ "jpn", "Japanese",   Japanese.wordOrder,        Japanese.adposition ⟩
  , ⟨ "cmn", "Mandarin",   Mandarin.wordOrder,        Mandarin.adposition ⟩
  , ⟨ "kor", "Korean",     Korean.wordOrder,          Korean.adposition ⟩
  , ⟨ "arb", "Arabic",     Arabic.ModernStandard.wordOrder,          Arabic.ModernStandard.adposition ⟩
  -- VSO + prepositional (Celtic):
  , ⟨ "cym", "Welsh",      Welsh.wordOrder,           Welsh.adposition ⟩
  , ⟨ "gle", "Irish",      Irish.wordOrder,           Irish.adposition ⟩
  -- Additional SOV + postpositional:
  , ⟨ "tur", "Turkish",    Turkish.wordOrder,         Turkish.adposition ⟩
  , ⟨ "hin", "Hindi",      HindiUrdu.wordOrder,       HindiUrdu.adposition ⟩
  , ⟨ "eus", "Basque",     Basque.wordOrder,          Basque.adposition ⟩
  -- Additional SVO + prepositional:
  , ⟨ "rus", "Russian",    Russian.wordOrder,  Russian.adposition ⟩
  , ⟨ "swh", "Swahili",    Swahili.wordOrder,         Swahili.adposition ⟩
  , ⟨ "ind", "Indonesian", Indonesian.wordOrder,      Indonesian.adposition ⟩
  -- Object-initial / verb-final-object orders for shape diversity:
  , ⟨ "tzo", "Tzotzil",    Tzotzil.wordOrder,         Tzotzil.adposition ⟩    -- VOS
  , ⟨ "hix", "Hixkaryana", Hixkaryana.wordOrder,      Hixkaryana.adposition ⟩ -- OVS
  -- K'iche' (Mayan, ergative, VOS, prepositional per [mondloch-2017] Ch 85
  -- absence; classification contested per [clemens-coon-2018]):
  , ⟨ "quc", "K'iche'",    Kiche.wordOrder,     Kiche.adposition ⟩ -- VOS
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
  p.adposition.IsPrepositional

/-- Language is classified as postpositional in WALS Ch 85. -/
abbrev isPostpositional (p : SampleEntry) : Prop :=
  p.adposition.IsPostpositional

/-- Language is OV (object precedes verb) per WALS Ch 83.
    [dryer-1992]'s primary classification under BDT. -/
abbrev isOV (p : SampleEntry) : Prop := p.wordOrder.ovOrder.IsOV

-- ============================================================================
-- §3. Greenberg's Universals 1, 3, 4 over `fragmentSample`
-- ============================================================================
-- The proofs decide a quotient over a 15-element `Finset` literal — bumping
-- `maxRecDepth` is the same idiom mathlib uses for similar `Finset.decide`
-- sites.

set_option maxRecDepth 4096 in
/-- [greenberg-1963] Universal 1: in declarative sentences with nominal
    subject and object, the subject almost always precedes the object.
    Tested over `fragmentSample`: subject-before-object entries (SOV + SVO +
    VSO) outnumber object-before-subject entries (VOS + OVS + OSV) by more
    than 4×. The sample's three object-initial languages (Tzotzil VOS,
    Hixkaryana OVS, K'iche' VOS) give a non-trivial margin; the multiplier
    is sample-dependent (Greenberg's claim is "almost always", not a
    specific ratio). -/
theorem greenberg_universal_1 :
    (fragmentSample.filter isSubjectBeforeObject).card >
    (fragmentSample.filter isObjectBeforeSubject).card * 4 := by
  decide

set_option maxRecDepth 4096 in
/-- [greenberg-1963] Universal 3: "Languages with dominant VSO order
    are always prepositional." Tested over `fragmentSample`; antecedent is
    triggered by Arabic, Welsh, Irish, all of which are prepositional. -/
theorem greenberg_universal_3 :
    ImplicationalUniversal isVSO isPrepositional fragmentSample := by
  decide

set_option maxRecDepth 4096 in
/-- [greenberg-1963] Universal 4: "With overwhelmingly greater than
    chance frequency, languages with normal SOV order are postpositional."
    Tested over `fragmentSample`; antecedent triggers Japanese, Korean,
    Turkish, Hindi, and Basque — all postpositional in WALS. -/
theorem greenberg_universal_4 :
    ImplicationalUniversal isSOV isPostpositional fragmentSample := by
  decide

-- ============================================================================
-- §4. Dryer 1992 BDT cross-framework theorem
-- ============================================================================

set_option maxRecDepth 4096 in
/-- [dryer-1992]'s Branching Direction Theory primary correlation,
    stated as an implicational universal: in the sample, every OV
    (object-precedes-verb) language is postpositional.

    Greenbergian U4 above commits to `BasicOrder.IsSOV` (SOV-specific)
    as the antecedent; Dryer's BDT primary commits to `OVOrder.IsOV`
    (covers SOV + OVS + OSV under one head-direction predicate). Both
    hold over the curated sample; they would diverge on a language with
    `BasicOrder.noDominant` Ch 81 + dominant `.ov` Ch 83 — exactly the
    Greenbergian-vs-Dryerian primacy choice flagged in
    `WordOrder`'s module docstring. -/
theorem dryer_bdt_ov_postp :
    ImplicationalUniversal isOV isPostpositional fragmentSample := by
  decide

-- The per-Fragment `wordOrder_consistent : wordOrder.IsConsistent := by decide`
-- sentinel in each `Fragments/{Lang}/WordOrder.lean` already covers the drift
-- an aggregate sample-consistency theorem would catch.

end Greenberg1963
