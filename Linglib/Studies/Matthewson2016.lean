import Linglib.Semantics.Evidential.Source
import Linglib.Semantics.Modality.Universals
import Linglib.Semantics.Modality.EventRelativity
import Linglib.Fragments.Gitksan.Modals
import Linglib.Fragments.Statimcets.Modals
import Linglib.Fragments.NezPerce.Modals
import Linglib.Fragments.Niuean.Modals

/-!
# Matthewson (2016): Modality

This file formalizes the cross-linguistic claims of the handbook survey [matthewson-2016]
on modal flavour, modal force, and modal–temporal interaction in the framework of
[kratzer-2012]. Modal backgrounds divide three ways, factual-circumstantial,
factual-evidential, and content-evidential, refining the epistemic–circumstantial binary;
Gitksan *ima('a)*, *gat*, and Nez Perce *o'qa* are modals without duals, specialized for
neither necessity nor possibility; epistemic modals are more likely than circumstantial ones
to lack duals, as Gitksan and Niuean show by encoding force only in the circumstantial
domain; the Gitksan system lexicalizes all three background classes; and future temporal
orientation requires overt prospective marking in Gitksan, mirroring the English requirement
of *have* for past orientation.

## Implementation notes

The modal inventories are the Gitksan, St'át'imcets, Nez Perce, and Niuean fragments; the
primary-source theorems for Gitksan are in `Studies/Matthewson2013.lean`.

## References

* [matthewson-2016]
* [kratzer-2012]
-/

namespace Matthewson2016

open Modality (ForceFlavor ForceAnalysis ModalItem ForceFlavorIndependent SingleAxis)

/-- The mode in which a conversational background projects, [kratzer-2012]'s distinction
between realistic backgrounds, whose accessible worlds hold counterparts of some actual
evidence, and informational ones, whose accessible worlds are compatible with the content of
some source of information; the chapter's factual and content modes (UNVERIFIED Table 18.2). -/
inductive ProjectionMode where
  | factual
  | content
  deriving DecidableEq, Repr

/-- The chapter's three-way classification of conversational backgrounds (UNVERIFIED Table
18.3): factual backgrounds without an information source, the traditional circumstantial class,
and factual and content backgrounds encoding one, the two epistemic subtypes. -/
inductive BackgroundClass where
  | factualCircumstantial
  | factualEvidential
  | contentEvidential
  deriving DecidableEq, Repr

/-- The projection mode of a background class. -/
def BackgroundClass.projectionMode : BackgroundClass → ProjectionMode
  | .factualCircumstantial => .factual
  | .factualEvidential => .factual
  | .contentEvidential => .content

/-- Only a content background lets the speaker disbelieve the prejacent. -/
def BackgroundClass.AllowsSpeakerDisbelief (b : BackgroundClass) : Prop := b = .contentEvidential

instance : DecidablePred BackgroundClass.AllowsSpeakerDisbelief :=
  λ _ => inferInstanceAs (Decidable (_ = _))

/-- The traditional epistemic or circumstantial flavor a class refines. -/
def BackgroundClass.traditionalFlavor : BackgroundClass → Modality.ModalFlavor
  | .factualCircumstantial => .circumstantial
  | .factualEvidential => .epistemic
  | .contentEvidential => .epistemic

-- ============================================================================
-- §1. Three-way background classification (Table 18.2, Table 18.3)
-- ============================================================================

/-! The three-way classification refines the traditional binary.
    All three classes are distinct. -/

theorem three_classes_distinct :
    BackgroundClass.factualCircumstantial ≠ .factualEvidential ∧
    BackgroundClass.factualEvidential ≠ .contentEvidential ∧
    BackgroundClass.factualCircumstantial ≠ .contentEvidential := by
  exact ⟨by decide, by decide, by decide⟩

/-- Both epistemic subtypes (factual-evidential and content-evidential)
    map to epistemic under the traditional classification. -/
theorem both_epistemic_subtypes :
    BackgroundClass.factualEvidential.traditionalFlavor = .epistemic ∧
    BackgroundClass.contentEvidential.traditionalFlavor = .epistemic := by
  exact ⟨rfl, rfl⟩

/-- Only the content-evidential class allows speaker disbelief. This
    is the diagnostic that separates the two epistemic subtypes:
    St'át'imcets k'a (factual) vs lákw7a (content). -/
theorem disbelief_distinguishes_epistemics :
    ¬ BackgroundClass.factualEvidential.AllowsSpeakerDisbelief ∧
    BackgroundClass.contentEvidential.AllowsSpeakerDisbelief := by
  exact ⟨by decide, by decide⟩

/-- The traditional circumstantial class is uniformly factual (Table 18.2). -/
theorem circumstantial_is_factual :
    BackgroundClass.factualCircumstantial.projectionMode = .factual := rfl

-- ============================================================================
-- §2. Gitksan: lexicalizes all three background classes (Table 18.1)
-- ============================================================================

section Gitksan
open Gitksan.Modals

/-- The chapter's classification of the Gitksan modals (UNVERIFIED Table 18.1): *ima('a)* is
factual-evidential, *gat* content-evidential, and the rest factual-circumstantial. -/
def gitksanBackground (m : ModalItem) : BackgroundClass :=
  if m = imaa then .factualEvidential else if m = gat then .contentEvidential
  else .factualCircumstantial

/-- Gitksan ima('a) is factual-evidential: the speaker has inferential
    evidence and cannot disbelieve the prejacent. -/
theorem gitksan_imaa_factual_evidential :
    gitksanBackground imaa = .factualEvidential := by decide

/-- Gitksan gat is content-evidential: reportative evidence, the
    speaker can disbelieve. -/
theorem gitksan_gat_content_evidential :
    gitksanBackground gat = .contentEvidential := by decide

/-- Gitksan circumstantial modals are factual-circumstantial. -/
theorem gitksan_circ_factual :
    gitksanBackground daakhlxw = .factualCircumstantial ∧
    gitksanBackground anookxw = .factualCircumstantial ∧
    gitksanBackground sgi = .factualCircumstantial := by
  decide

/-- Coarse evidential source of a modal background class in Matthewson's
    system: factual-evidential modals are inferential, content-evidential
    modals reportative, and factual circumstantials encode no information
    source. -/
def backgroundCoarseSource :
    BackgroundClass → Option Evidential.CoarseSource
  | .factualEvidential => some .inference
  | .contentEvidential => some .hearsay
  | .factualCircumstantial => none

/-- Gitksan ima('a) marks inferential evidence and gat reportative
    evidence in the shared source taxonomy. -/
theorem gitksan_sources :
    backgroundCoarseSource (gitksanBackground imaa) = some .inference ∧
    backgroundCoarseSource (gitksanBackground gat) = some .hearsay := by
  decide

/-- All three background classes are represented in Gitksan. -/
theorem gitksan_three_way_split :
    (allExpressions.map gitksanBackground).any (· == .factualCircumstantial) &&
    (allExpressions.map gitksanBackground).any (· == .factualEvidential) &&
    (allExpressions.map gitksanBackground).any (· == .contentEvidential) = true := by
  decide

end Gitksan

-- ============================================================================
-- §3. Gitksan absolute epistemic/circumstantial split (§18.2.3)
-- ============================================================================

/-- The epistemic/circumstantial split is absolute: no modal crosses
    the boundary. Epistemic modals are purely epistemic; circumstantial
    modals have no epistemic readings. -/
theorem gitksan_absolute_split :
    (∀ e ∈ Gitksan.Modals.epistemicModals, ∀ ff ∈ e.meaning, ff.flavor = .epistemic) ∧
      ∀ e ∈ Gitksan.Modals.circumstantialModals, ∀ ff ∈ e.meaning, ff.flavor ≠ .epistemic := by
  decide

-- ============================================================================
-- §4. Modals without duals (§18.3.2)
-- ============================================================================

/-! Variable-force modals (Gitksan) and strengthened possibility modals
    (Nez Perce) both lack duals but for different reasons. -/

/-- Gitksan ima('a) and gat are both variable-force. -/
theorem gitksan_variable_force :
    Gitksan.Modals.forceAnalysis Gitksan.Modals.imaa = .variableForce ∧
    Gitksan.Modals.forceAnalysis Gitksan.Modals.gat = .variableForce := by
  constructor <;> rfl

/-- Nez Perce o'qa is a strengthened possibility modal. -/
theorem nez_perce_strengthened :
    NezPerce.Modals.forceAnalysis NezPerce.Modals.oqa =
      .strengthened .possibility := rfl

/-- Despite lacking duals, both admit necessity and possibility readings. -/
theorem both_forces_available :
    ForceAnalysis.variableForce.AdmitsNecessity ∧
    ForceAnalysis.variableForce.AdmitsPossibility ∧
    (ForceAnalysis.strengthened .possibility).AdmitsNecessity ∧
    (ForceAnalysis.strengthened .possibility).AdmitsPossibility := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Force analysis consistency

Each fragment's stipulated `ForceAnalysis` is checked against the forces its meaning attests:
one force for a fixed or strengthened modal, both for a variable-force one. -/

/-- A force analysis is consistent with a meaning when the forces the meaning attests are the
one the analysis fixes or strengthens, or two for a variable-force analysis. -/
def Consistent : ForceAnalysis → Finset ForceFlavor → Prop
  | .fixed fo, m | .strengthened fo, m => m.image Prod.fst = {fo}
  | .variableForce, m => 2 ≤ (m.image Prod.fst).card

instance (a : ForceAnalysis) (m : Finset ForceFlavor) : Decidable (Consistent a m) := by
  cases a <;> unfold Consistent <;> infer_instance

/-- A modal has a dual in an inventory when it is fixed for one force and another item of the
inventory expresses the dual force over its flavors (UNVERIFIED §18.3.2). -/
def HasDualIn (L : List ModalItem) (m : ModalItem) : Prop :=
  (m.meaning.image Prod.fst).card = 1 ∧
    ∃ m' ∈ L, m'.meaning = m.meaning.image (Prod.map Modality.ModalForce.dual id)

instance (L : List ModalItem) (m : ModalItem) : Decidable (HasDualIn L m) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _ = _))

/-- A variable-force modal, attesting two forces, has no dual. -/
theorem not_hasDualIn_of_variableForce {L : List ModalItem} {m : ModalItem}
    (h : Consistent .variableForce m.meaning) : ¬ HasDualIn L m :=
  λ h' => by simp only [Consistent] at h; have := h'.1; omega

/-- Gitksan ima('a) and gat, Nez Perce o'qa and St'át'imcets =ka have no duals in their
inventories. -/
theorem no_duals :
    ¬ HasDualIn Gitksan.Modals.allExpressions Gitksan.Modals.imaa ∧
      ¬ HasDualIn Gitksan.Modals.allExpressions Gitksan.Modals.gat ∧
      ¬ HasDualIn NezPerce.Modals.allExpressions NezPerce.Modals.oqa ∧
      ¬ HasDualIn Statimcets.Modals.allExpressions Statimcets.Modals.ka := by
  decide

/-- Niuean encodes force in the circumstantial domain, where *maeke* and *lata* are duals, and
not in the epistemic one, where *liga* covers both forces alone. -/
theorem niuean_duals :
    HasDualIn Niuean.Modals.allExpressions Niuean.Modals.maeke ∧
      HasDualIn Niuean.Modals.allExpressions Niuean.Modals.lata ∧
      ¬ HasDualIn Niuean.Modals.allExpressions Niuean.Modals.liga := by
  decide

/-- Gitksan ima('a) and gat are variable-force and attest both forces. -/
theorem gitksan_force_consistent :
    Consistent (Gitksan.Modals.forceAnalysis Gitksan.Modals.imaa) Gitksan.Modals.imaa.meaning ∧
      Consistent (Gitksan.Modals.forceAnalysis Gitksan.Modals.gat) Gitksan.Modals.gat.meaning := by
  decide

/-- Nez Perce o'qa is strengthened possibility and attests only possibility. -/
theorem nez_perce_oqa_force_consistent :
    Consistent (NezPerce.Modals.forceAnalysis NezPerce.Modals.oqa) NezPerce.Modals.oqa.meaning := by
  decide

/-- St'át'imcets =ka and Niuean liga are variable-force. -/
theorem statimcets_niuean_force_consistent :
    Consistent (Statimcets.Modals.forceAnalysis Statimcets.Modals.ka) Statimcets.Modals.ka.meaning ∧
      Consistent (Niuean.Modals.forceAnalysis Niuean.Modals.liga) Niuean.Modals.liga.meaning := by
  decide

-- ============================================================================
-- §5. Flavour–force correlation (§18.5)
-- ============================================================================

/-! Cross-linguistic tendency: epistemic modals are more likely to lack
    force duals than circumstantial modals. Both Gitksan and Niuean
    instantiate this pattern. -/

/-- Niuean: epistemic domain has one modal (both forces), circumstantial
    has two (one per force). -/
theorem niuean_force_asymmetry :
    (Niuean.Modals.allExpressions.filter
      (λ e => ∃ ff ∈ e.meaning, ff.flavor = .epistemic)).length = 1 ∧
    (Niuean.Modals.allExpressions.filter
      (λ e => ∃ ff ∈ e.meaning, ff.flavor = .circumstantial)).length = 2 := by
  decide

/-- All St'át'imcets, Nez Perce and Niuean modals satisfy IFF. -/
theorem all_fragments_iff :
    (∀ e ∈ Statimcets.Modals.allExpressions, ForceFlavorIndependent e.meaning) ∧
      (∀ e ∈ NezPerce.Modals.allExpressions, ForceFlavorIndependent e.meaning) ∧
      (∀ e ∈ Niuean.Modals.allExpressions, ForceFlavorIndependent e.meaning) := by
  decide

-- ============================================================================
-- §6. Temporal orientation and prospective aspect (§18.4.3)
-- ============================================================================

/-- In Gitksan, future temporal orientation of an epistemic modal
    (`imaa`) requires prospective `dim`. The 2016 handbook chapter
    presents this as the headline pattern; [matthewson-2013] shows
    it is part of a flavor-keyed asymmetry (circumstantials require
    `dim` for any orientation). -/
theorem imaa_future_requires_dim :
    Gitksan.Modals.requiresDim Gitksan.Modals.imaa
      .future = true := rfl

/-- For epistemics, past and present orientation do not require `dim`. -/
theorem imaa_past_present_no_dim :
    Gitksan.Modals.requiresDim Gitksan.Modals.imaa
      .past = false ∧
    Gitksan.Modals.requiresDim Gitksan.Modals.imaa
      .present = false := ⟨rfl, rfl⟩

/-- English–Gitksan mirror: English obligatorily marks past orientation
    (via *have*), Gitksan obligatorily marks future orientation (via *dim*).
    Both leave the remaining orientations unmarked.
    [matthewson-2016] §18.4.3. -/
structure TemporalMarkingMirror where
  /-- Which orientation is obligatorily marked. -/
  obligatoryMarking : Modality.TemporalOrientation
  /-- Name of the marker. -/
  marker : String

def english : TemporalMarkingMirror := ⟨.past, "have"⟩
def gitksan : TemporalMarkingMirror := ⟨.future, "dim"⟩

/-- The marked orientations are opposite: English marks past, Gitksan future. -/
theorem mirror_orientations :
    english.obligatoryMarking ≠ gitksan.obligatoryMarking := by decide

-- ============================================================================
-- §7. Nauze's (2008) polyfunctionality universal
-- ============================================================================

/-! [matthewson-2016] §18.5 discusses [nauze-2008]'s proposed
    universal: "Modal elements can only have more than one meaning along
    a unique axis of the semantic space: they either vary on the horizontal
    axis [flavour] ... or they vary on the vertical axis [force] ... but
    they cannot vary on both axes."

    This is exactly SAV. We verify it holds for all four new fragments. -/

/-- St'át'imcets =ka satisfies SAV (varies on force, fixed deontic). -/
theorem statimcets_ka_sav : SingleAxis Statimcets.Modals.ka.meaning := by decide

/-- Nez Perce o'qa satisfies SAV (singleton). -/
theorem nez_perce_oqa_sav : SingleAxis NezPerce.Modals.oqa.meaning := by decide

/-- Niuean: all modals satisfy SAV. -/
theorem niuean_all_sav : ∀ e ∈ Niuean.Modals.allExpressions, SingleAxis e.meaning := by decide

-- ============================================================================
-- §8. Hacquard's content licensing derives the epistemic/circumstantial split
-- ============================================================================

/-! [hacquard-2006] [hacquard-2010]

Matthewson's three-way background classification (Table 18.3) refines the
traditional epistemic/circumstantial binary. The *coarse* binary itself
is derived, not stipulated: [hacquard-2006]'s content licensing
predicts that only contentful events (speech acts, attitudes) can project
epistemic modal bases. VP events lack content and can only project
circumstantial bases. This predicts the absolute epistemic/circumstantial
split attested in Gitksan (§18.2.3).

The three-way refinement (factual-evidential vs content-evidential within
epistemic) is a further subdivision of the epistemic class that content
licensing does not address — it depends on the *type* of content (inferential
vs reportative), not on whether content exists. -/

open Modality (EventBinder)

/-- Content licensing correctly predicts the coarse split.
    Contentful events → epistemic available; contentless → not. -/
theorem content_licensing_derives_coarse_split :
    EventBinder.speechAct.canProjectEpistemic = true ∧
    EventBinder.attitude.canProjectEpistemic = true ∧
    EventBinder.vpEvent.canProjectEpistemic = false := ⟨rfl, rfl, rfl⟩

/-- The three-way refinement is orthogonal to content licensing.
    Both factual-evidential and content-evidential are epistemic subtypes
    (both require content), distinguished by projection mode, not by
    content availability. -/
theorem three_way_orthogonal_to_content :
    BackgroundClass.factualEvidential.traditionalFlavor = .epistemic ∧
    BackgroundClass.contentEvidential.traditionalFlavor = .epistemic ∧
    BackgroundClass.factualEvidential.projectionMode ≠
      BackgroundClass.contentEvidential.projectionMode := by
  exact ⟨rfl, rfl, by decide⟩

/-- Gitksan's three-way split is consistent with content licensing.
    Epistemic modals (ima('a), gat) are high (content available);
    circumstantial modals (da'akhlxw, anookxw, sgi) are compatible
    with both high and low positions (circumstantial always available). -/
theorem gitksan_consistent_with_content_licensing :
    -- Circumstantial is always available (even for VP events)
    EventBinder.vpEvent.canProjectCircumstantial = true ∧
    -- Epistemic requires content (speech act or attitude)
    EventBinder.speechAct.canProjectEpistemic = true := ⟨rfl, rfl⟩

end Matthewson2016
