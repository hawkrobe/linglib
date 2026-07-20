import Linglib.Semantics.Evidential.Source
import Linglib.Semantics.Modality.Typology
import Linglib.Semantics.Modality.EventRelativity
import Linglib.Fragments.Gitksan.Modals
import Linglib.Fragments.Statimcets.Modals
import Linglib.Fragments.NezPerce.Modals
import Linglib.Fragments.Niuean.Modals

/-!
# Matthewson (2016) — Modality

[matthewson-2016]

Lisa Matthewson. "Modality." Chapter 18 in *The Cambridge Handbook of
Formal Semantics*, ed. Maria Aloni and Paul Dekker. Cambridge University
Press. pp. 525–559. DOI: 10.1017/CBO9781139236157.019.

A survey of three core topics in modal semantics — modal flavour (§18.2),
modal force (§18.3), and modal–temporal interactions (§18.4) — presented
within the Kratzerian framework with cross-linguistic data from Gitksan,
St'át'imcets, Nez Perce, Niuean, and other languages.

## Key contributions formalized here

1. **Three-way background classification** (Table 18.3):
   factual-circumstantial, factual-evidential, content-evidential.
   Refines the traditional epistemic/circumstantial binary following
   [kratzer-2012].

2. **Modals without duals** (§18.3.2): Gitksan ima('a)/gat and Nez Perce
   o'qa are not specialized for necessity or possibility. Different
   analyses: variable force (Peterson 2010) vs. strengthened possibility
   (Deal 2011).

3. **Cross-linguistic flavour–force correlation** (§18.5): epistemic
   modals are more likely to lack duals than circumstantial modals.
   Gitksan and Niuean both encode force distinctions in the circumstantial
   domain but not the epistemic domain.

4. **Gitksan three-way split** (Table 18.1): the Gitksan modal system
   lexicalizes all three background classes — factual-circumstantial
   (da'akhlxw, anookxw, sgi), factual-evidential (ima('a)), and
   content-evidential (gat).

5. **Temporal orientation and prospective aspect** (§18.4.3): Gitksan
   requires overt prospective marking (*dim*) for future temporal
   orientation, mirroring English's requirement of *have* for past
   orientation.
-/

namespace Matthewson2016

open Semantics.Modality (ForceFlavor ForceAnalysis BackgroundClass ProjectionMode)
open Semantics.Modality.Typology (satisfiesIFF satisfiesSAV)

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

/-- Gitksan ima('a) is factual-evidential: the speaker has inferential
    evidence and cannot disbelieve the prejacent. -/
theorem gitksan_imaa_factual_evidential :
    backgroundClass imaa = .factualEvidential := rfl

/-- Gitksan gat is content-evidential: reportative evidence, the
    speaker can disbelieve. -/
theorem gitksan_gat_content_evidential :
    backgroundClass gat = .contentEvidential := rfl

/-- Gitksan circumstantial modals are factual-circumstantial. -/
theorem gitksan_circ_factual :
    backgroundClass daakhlxw = .factualCircumstantial ∧
    backgroundClass anookxw = .factualCircumstantial ∧
    backgroundClass sgi = .factualCircumstantial :=
  ⟨rfl, rfl, rfl⟩

/-- Coarse evidential source of a modal background class in Matthewson's
    system: factual-evidential modals are inferential, content-evidential
    modals reportative, and factual circumstantials encode no information
    source. -/
def backgroundCoarseSource :
    BackgroundClass → Option Semantics.Evidential.CoarseSource
  | .factualEvidential => some .inference
  | .contentEvidential => some .hearsay
  | .factualCircumstantial => none

/-- Gitksan ima('a) marks inferential evidence and gat reportative
    evidence in the shared source taxonomy. -/
theorem gitksan_sources :
    backgroundCoarseSource (backgroundClass imaa) = some .inference ∧
    backgroundCoarseSource (backgroundClass gat) = some .hearsay :=
  ⟨rfl, rfl⟩

/-- All three background classes are represented in Gitksan. -/
theorem gitksan_three_way_split :
    (allExpressions.map backgroundClass).any (· == .factualCircumstantial) &&
    (allExpressions.map backgroundClass).any (· == .factualEvidential) &&
    (allExpressions.map backgroundClass).any (· == .contentEvidential) = true := by
  decide

end Gitksan

-- ============================================================================
-- §3. Gitksan absolute epistemic/circumstantial split (§18.2.3)
-- ============================================================================

/-- The epistemic/circumstantial split is absolute: no modal crosses
    the boundary. Epistemic modals are purely epistemic; circumstantial
    modals have no epistemic readings. -/
theorem gitksan_absolute_split :
    Gitksan.Modals.epistemicModals.all (fun e =>
      e.meaning.all (fun ff => ff.flavor == .epistemic)) = true ∧
    Gitksan.Modals.circumstantialModals.all (fun e =>
      e.meaning.all (fun ff => ff.flavor != .epistemic)) = true := by
  constructor <;> decide

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

/-- Both analyses agree: the modals lack duals. -/
theorem no_duals :
    ¬ ForceAnalysis.variableForce.HasDual ∧
    ¬ (ForceAnalysis.strengthened .possibility).HasDual := by
  refine ⟨?_, ?_⟩ <;> intro h <;> exact h.elim

/-- Despite lacking duals, both admit necessity and possibility readings. -/
theorem both_forces_available :
    ForceAnalysis.variableForce.AdmitsNecessity ∧
    ForceAnalysis.variableForce.AdmitsPossibility ∧
    (ForceAnalysis.strengthened .possibility).AdmitsNecessity ∧
    (ForceAnalysis.strengthened .possibility).AdmitsPossibility := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Force analysis consistency

Each fragment's stipulated `ForceAnalysis` is verified against the
observable `ForcePattern` derived from the meaning. The stipulation
adds explanatory content (variable-force vs strengthened), but it
must be consistent with the structural facts. -/

open Semantics.Modality.Typology (inferForcePattern)
private abbrev consistent := Semantics.Modality.Typology.ForceAnalysis.isConsistentWith

/-- Gitksan ima('a): variable-force analysis is consistent with
    multiForce pattern (both possibility and necessity in meaning). -/
theorem gitksan_imaa_force_consistent :
    consistent (Gitksan.Modals.forceAnalysis Gitksan.Modals.imaa)
      (inferForcePattern Gitksan.Modals.imaa.meaning) = true := by decide

/-- Gitksan gat: variable-force analysis is consistent. -/
theorem gitksan_gat_force_consistent :
    consistent (Gitksan.Modals.forceAnalysis Gitksan.Modals.gat)
      (inferForcePattern Gitksan.Modals.gat.meaning) = true := by decide

/-- Nez Perce o'qa: strengthened possibility is consistent with
    singleForce pattern (only possibility in meaning set). -/
theorem nez_perce_oqa_force_consistent :
    consistent (NezPerce.Modals.forceAnalysis NezPerce.Modals.oqa)
      (inferForcePattern NezPerce.Modals.oqa.meaning) = true := by decide

/-- St'át'imcets =ka: variable-force analysis is consistent. -/
theorem statimcets_ka_force_consistent :
    consistent (Statimcets.Modals.forceAnalysis Statimcets.Modals.ka)
      (inferForcePattern Statimcets.Modals.ka.meaning) = true := by decide

/-- Niuean liga: variable-force analysis is consistent. -/
theorem niuean_liga_force_consistent :
    consistent (Niuean.Modals.forceAnalysis Niuean.Modals.liga)
      (inferForcePattern Niuean.Modals.liga.meaning) = true := by decide

-- ============================================================================
-- §5. Flavour–force correlation (§18.5)
-- ============================================================================

/-! Cross-linguistic tendency: epistemic modals are more likely to lack
    force duals than circumstantial modals. Both Gitksan and Niuean
    instantiate this pattern. -/

/-- Niuean: epistemic domain has one modal (both forces), circumstantial
    has two (one per force). -/
theorem niuean_force_asymmetry :
    (Niuean.Modals.allExpressions.filter (fun e =>
      e.meaning.any (fun ff => ff.flavor == .epistemic))).length = 1 ∧
    (Niuean.Modals.allExpressions.filter (fun e =>
      e.meaning.any (fun ff => ff.flavor == .circumstantial))).length = 2 := by
  constructor <;> decide

/-- All St'át'imcets and Niuean modals satisfy IFF. -/
theorem all_fragments_iff :
    Statimcets.Modals.allExpressions.all
      (fun e => satisfiesIFF e.meaning) = true ∧
    Niuean.Modals.allExpressions.all
      (fun e => satisfiesIFF e.meaning) = true := by
  constructor <;> decide

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
  obligatoryMarking : Semantics.Modality.TemporalOrientation
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
theorem statimcets_ka_sav :
    satisfiesSAV Statimcets.Modals.ka.meaning = true := by decide

/-- Nez Perce o'qa satisfies SAV (singleton). -/
theorem nez_perce_oqa_sav :
    satisfiesSAV NezPerce.Modals.oqa.meaning = true := by decide

/-- Niuean: all modals satisfy SAV. -/
theorem niuean_all_sav :
    Niuean.Modals.allExpressions.all
      (fun e => satisfiesSAV e.meaning) = true := by decide

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

open Semantics.Modality.EventRelativity (EventBinder)

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

-- ============================================================================
-- §9. Modal inventories as ModalInventory entries
-- ============================================================================

/-! These inventories can be compared against the Imel, Guo &
    [imel-guo-steinert-threlkeld-2026] typological database but are kept
    here because their data source is [matthewson-2016], not the
    Imel et al. database. -/

open Semantics.Modality.Typology (ModalInventory)

def statimcetsInventory : ModalInventory where
  language := "St'át'imcets"
  family := "Salish"
  source := "Rullmann, Matthewson & Davis (2008)"
  expressions := Statimcets.Modals.allExpressions

def nezPerceInventory : ModalInventory where
  language := "Nez Perce"
  family := "Sahaptian"
  source := "Deal (2011)"
  expressions := NezPerce.Modals.allExpressions

def niueanInventory : ModalInventory where
  language := "Niuean"
  family := "Polynesian"
  source := "Matthewson et al. (2012), Seiter (1980)"
  expressions := Niuean.Modals.allExpressions

/-- All three Matthewson 2016 inventories satisfy IFF. -/
theorem all_inventories_iff :
    statimcetsInventory.allIFF = true ∧
    nezPerceInventory.allIFF = true ∧
    niueanInventory.allIFF = true := by
  constructor; decide
  constructor <;> decide

end Matthewson2016
