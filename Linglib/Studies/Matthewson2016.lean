import Linglib.Semantics.Modality.Universals
import Linglib.Semantics.Evidential.Source
import Linglib.Data.Examples.Matthewson2016
import Linglib.Fragments.Gitksan.Modals
import Linglib.Fragments.Statimcets.Modals
import Linglib.Fragments.NezPerce.Modals
import Linglib.Fragments.Niuean.Modals
import Linglib.Studies.Condoravdi2002
import Linglib.Studies.Matthewson2013

/-!
# Matthewson (2016): Modality

This file formalizes the typological claims of the handbook chapter [matthewson-2016]. On
flavour, a conversational background projects in [kratzer-2012]'s factual or content mode and
either encodes an information source or not, a three-way classification that St'át'imcets
lexicalizes in full; the class of a modal is read off what it encodes, with the speaker's
ability to disbelieve the prejacent as the diagnostic for content mode, and Gitksan keeps its
epistemic and circumstantial modals apart. On force, Gitksan *ima('a)* and *gat* and Nez Perce
*o'qa* are modals without duals, which their inventories confirm. On modal–temporal interaction,
Gitksan marks future orientation with the prospective *dim* where English marks past
orientation with the perfect, a mirror image derived from the Gitksan fragment and from
[condoravdi-2002]. On typology, Gitksan and Niuean distinguish force among circumstantial
modals and not among epistemic ones, and [vander-klok-2013b]'s refinement of [nauze-2008]'s
universal, one axis of variation per modal domain, is strictly stronger than the universal and
holds of the four inventories.

## Implementation notes

* The chapter's examples are rows. The deniability rows (25)–(28), the Nez Perce rows
  (39)–(40) and the Gitksan orientation rows (60)–(63) are checked against the fragments.
* Table 18.4's hypothetical root system has a teleological flavour, which the library folds
  into circumstantial; bouletic stands in for it, which keeps the system ambiguous along both
  axes.
* The English column of Table 18.3 is not formalized, no fragment recording the source or
  deniability of the English modals.

## References

* [matthewson-2016]
* [kratzer-2012]
* [rullmann-matthewson-davis-2008]
* [peterson-2010]
* [deal-2011]
* [nauze-2008]
* [vander-klok-2013b]
* [condoravdi-2002]
-/

namespace Matthewson2016

open Modality Data.Examples Evidential

/-! ### Modal flavour: the three-way classification (Tables 18.2 and 18.3) -/

/-- The mode in which a conversational background projects, [kratzer-2012]'s distinction
between realistic backgrounds, whose accessible worlds hold counterparts of some actual
evidence, and informational ones, whose accessible worlds are compatible with the content of
some source of information; the chapter's factual and content modes (Table 18.2). -/
inductive ProjectionMode where
  | factual
  | content
  deriving DecidableEq, Repr

/-- The chapter's three-way classification of conversational backgrounds (Table 18.3): factual
backgrounds without an information source, the traditional circumstantial class, and factual
and content backgrounds encoding one, the two epistemic subtypes. -/
inductive BackgroundClass where
  | factualCircumstantial
  | factualEvidential
  | contentEvidential
  deriving DecidableEq, Repr, Fintype

/-- The projection mode of a background class. -/
def BackgroundClass.projectionMode : BackgroundClass → ProjectionMode
  | .factualCircumstantial => .factual
  | .factualEvidential => .factual
  | .contentEvidential => .content

/-- The traditional epistemic or circumstantial flavour a class refines. -/
def BackgroundClass.traditionalFlavor : BackgroundClass → ModalFlavor
  | .factualCircumstantial => .circumstantial
  | .factualEvidential => .epistemic
  | .contentEvidential => .epistemic

/-- The class of a modal from what it encodes: no information source is factual-circumstantial,
a source the speaker may disbelieve is content-evidential, and any other source
factual-evidential. -/
def classOf (source : Option CoarseSource) (deniable : Prop) [Decidable deniable] :
    BackgroundClass :=
  if source = none then .factualCircumstantial
  else if deniable then .contentEvidential else .factualEvidential

/-- The circumstantial–evidential division is whether an information source is encoded. -/
theorem traditionalFlavor_classOf (source : Option CoarseSource) (deniable : Prop)
    [Decidable deniable] :
    (classOf source deniable).traditionalFlavor = .circumstantial ↔ source = none := by
  unfold classOf; split_ifs <;> simp_all [BackgroundClass.traditionalFlavor]

/-- The factual–content division among evidentials is the deniability diagnostic. -/
theorem projectionMode_classOf (source : Option CoarseSource) (deniable : Prop)
    [Decidable deniable] :
    (classOf source deniable).projectionMode = .content ↔ source ≠ none ∧ deniable := by
  unfold classOf; split_ifs <;> simp_all [BackgroundClass.projectionMode]

section Statimcets
open Statimcets.Modals

/-- The class of a St'át'imcets modal. -/
def statimcetsClass (m : ModalItem) : BackgroundClass := classOf (source m) (Deniable m)

/-- Table 18.3's St'át'imcets row. -/
theorem table18_3 :
    statimcetsClass ka = .factualCircumstantial ∧
      statimcetsClass kaCircumfix = .factualCircumstantial ∧
      statimcetsClass kaInfer = .factualEvidential ∧ statimcetsClass ku7 = .factualEvidential ∧
      statimcetsClass lakw7a = .contentEvidential := by
  decide

/-- St'át'imcets encodes the full three-way split. -/
theorem statimcets_full_split :
    ∀ c : BackgroundClass, ∃ m ∈ allExpressions, statimcetsClass m = c := by
  decide

/-- The modal a deniability row names. -/
private def modalOf : String → Option ModalItem
  | "k'a" => some kaInfer
  | "lákw7a" => some lakw7a
  | _ => none

/-- (25)–(28): a modal survives *but it was the wind* exactly when it is deniable. -/
theorem deniability_rows :
    ∀ e ∈ Examples.all, e.feature? "test" = some "deniability" →
      ∀ m ∈ (e.feature? "modal").bind modalOf, (e.judgment = .acceptable ↔ Deniable m) := by
  decide

end Statimcets

/-! ### Gitksan: epistemic and circumstantial apart (Table 18.1) -/

/-- No Gitksan modal crosses the epistemic–circumstantial boundary. -/
theorem gitksan_absolute_split :
    (∀ e ∈ Gitksan.Modals.epistemicModals, ∀ ff ∈ e.meaning, ff.flavor = .epistemic) ∧
      ∀ e ∈ Gitksan.Modals.circumstantialModals, ∀ ff ∈ e.meaning, ff.flavor ≠ .epistemic := by
  decide

/-! ### Modal force: modals without duals (§18.3.2)

A modal without a dual comes in no necessity–possibility pair and is used in contexts
supporting either claim: Gitksan *ima('a)* and *gat*, variable in force, and Nez Perce *o'qa*,
a possibility modal read as necessity because no necessity modal competes with it
([deal-2011]). -/

/-- The fragments' force analyses are consistent with their meanings. -/
theorem force_consistent :
    (∀ e ∈ Gitksan.Modals.allExpressions,
        (Matthewson2013.forceAnalysis e).Consistent e.meaning) ∧
      (∀ e ∈ Statimcets.Modals.allExpressions,
        (Statimcets.Modals.forceAnalysis e).Consistent e.meaning) ∧
      (∀ e ∈ NezPerce.Modals.allExpressions,
        (NezPerce.Modals.forceAnalysis e).Consistent e.meaning) ∧
      ∀ e ∈ Niuean.Modals.allExpressions, (Niuean.Modals.forceAnalysis e).Consistent e.meaning := by
  decide

/-- A modal has a dual in an inventory when it is fixed for one force and another item of the
inventory expresses the dual force over its flavours. -/
def HasDualIn (L : List ModalItem) (m : ModalItem) : Prop :=
  (m.meaning.image Prod.fst).card = 1 ∧
    ∃ m' ∈ L, m'.meaning = m.meaning.image (Prod.map ModalForce.dual id)

instance (L : List ModalItem) (m : ModalItem) : Decidable (HasDualIn L m) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _ = _))

/-- A variable-force modal, attesting two forces, has no dual. -/
theorem not_hasDualIn_of_variableForce {L : List ModalItem} {m : ModalItem}
    (h : ForceAnalysis.Consistent .variableForce m.meaning) : ¬ HasDualIn L m :=
  λ h' => by simp only [ForceAnalysis.Consistent] at h; have := h'.1; omega

/-- Gitksan ima('a) and gat, Nez Perce o'qa and St'át'imcets =ka have no duals in their
inventories. -/
theorem no_duals :
    ¬ HasDualIn Gitksan.Modals.allExpressions Gitksan.Modals.imaa ∧
      ¬ HasDualIn Gitksan.Modals.allExpressions Gitksan.Modals.gat ∧
      ¬ HasDualIn NezPerce.Modals.allExpressions NezPerce.Modals.oqa ∧
      ¬ HasDualIn Statimcets.Modals.allExpressions Statimcets.Modals.ka := by
  decide

/-- (37): ima('a) is read as possibility and as necessity alike. -/
theorem imaa_rows :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "ima('a)" →
      ∀ r ∈ e.readings, r.2 = .acceptable := by
  decide

/-- (39)–(40): o'qa is read as necessity outside a downward-entailing context and only as
possibility inside one, the profile of a possibility modal without a necessity competitor. -/
theorem oqa_rows :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "o'qa" →
      ∀ r ∈ e.readings, r.1 = "necessity" →
        (r.2 = .acceptable ↔ e.feature? "downwardEntailing" = some "false") := by
  decide

/-! ### Modal–temporal interaction (§18.4.3) -/

/-- The orientation a row records. -/
private def orientationOf : String → Option TemporalOrientation
  | "past" => some .past
  | "present" => some .present
  | "future" => some .future
  | _ => none

/-- (60)–(63): under a fixed past perspective ima('a) takes every orientation, and is
acceptable without the prospective *dim* exactly when not future-oriented, as
[matthewson-2013]'s `RequiresDim` records. -/
theorem gitksan_orientation_rows :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "ima('a)" →
      ∀ o ∈ (e.feature? "orientation").bind orientationOf,
        (e.judgment = .acceptable ↔
          e.feature? "prospective" = some "true" ∨
            ¬ Matthewson2013.RequiresDim Gitksan.Modals.imaa o) := by
  decide

/-- English marks past orientation, by the perfect under the modal among [condoravdi-2002]'s
scopings, and Gitksan future orientation, by *dim*: the mirror image of §18.4.3. -/
theorem marking_mirror :
    (∀ s : Condoravdi2002.Scope, s.orientation = .past ↔ s = .modalPerf) ∧
      ∀ o : TemporalOrientation,
        Matthewson2013.RequiresDim Gitksan.Modals.imaa o ↔ o = .future := by
  decide

/-! ### Typology (§18.5) -/

/-- An inventory distinguishes force within a domain when two of its modals there express
different sets of forces. -/
def DistinguishesForce (L : List ModalItem) (D : ModalItem → Prop) [DecidablePred D] : Prop :=
  ∃ m ∈ L, ∃ m' ∈ L, D m ∧ D m' ∧ m.meaning.image Prod.fst ≠ m'.meaning.image Prod.fst

instance (L : List ModalItem) (D : ModalItem → Prop) [DecidablePred D] :
    Decidable (DistinguishesForce L D) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _ ∧ _ ∧ _ ≠ _))

/-- The flavour–force correlation: Gitksan and Niuean distinguish force among their
circumstantial modals and not among their epistemic ones. -/
theorem force_only_circumstantial :
    (¬ DistinguishesForce Gitksan.Modals.allExpressions ModalItem.Epistemic ∧
        DistinguishesForce Gitksan.Modals.allExpressions (¬ ·.Epistemic)) ∧
      ¬ DistinguishesForce Niuean.Modals.allExpressions ModalItem.Epistemic ∧
        DistinguishesForce Niuean.Modals.allExpressions (¬ ·.Epistemic) := by
  decide

/-- Niuean's circumstantial *maeke* and *lata* are duals; its epistemic *liga* has none. -/
theorem niuean_duals :
    HasDualIn Niuean.Modals.allExpressions Niuean.Modals.maeke ∧
      HasDualIn Niuean.Modals.allExpressions Niuean.Modals.lata ∧
      ¬ HasDualIn Niuean.Modals.allExpressions Niuean.Modals.liga := by
  decide

/-- [nauze-2008]'s universal holds of the four inventories: every modal varies on one axis. -/
theorem nauze :
    ∀ e ∈ Gitksan.Modals.allExpressions ++ Statimcets.Modals.allExpressions ++
      NezPerce.Modals.allExpressions ++ Niuean.Modals.allExpressions, SingleAxis e.meaning := by
  decide

/-- [vander-klok-2013b]'s refinement of the universal: within each domain, epistemic and
non-epistemic, an inventory varies along one axis only. -/
def VanderKlok (L : List ModalItem) : Prop :=
  ¬ ((∃ m ∈ L, m.Epistemic ∧ m.VariesForce) ∧ ∃ m ∈ L, m.Epistemic ∧ m.VariesFlavor) ∧
    ¬ ((∃ m ∈ L, ¬ m.Epistemic ∧ m.VariesForce) ∧ ∃ m ∈ L, ¬ m.Epistemic ∧ m.VariesFlavor)

instance (L : List ModalItem) : Decidable (VanderKlok L) :=
  inferInstanceAs (Decidable (¬ (_ ∧ _) ∧ ¬ (_ ∧ _)))

/-- The refinement entails the universal: a modal varying on both axes varies on both within
its own domain. -/
theorem VanderKlok.singleAxis {L : List ModalItem} (h : VanderKlok L) {m : ModalItem}
    (hm : m ∈ L) : SingleAxis m.meaning := by
  by_contra hs
  simp only [SingleAxis, not_or, not_le] at hs
  by_cases he : m.Epistemic
  · exact h.1 ⟨⟨m, hm, he, hs.1⟩, ⟨m, hm, he, hs.2⟩⟩
  · exact h.2 ⟨⟨m, hm, he, hs.1⟩, ⟨m, hm, he, hs.2⟩⟩

/-- The four inventories satisfy the refinement. -/
theorem inventories_vanderKlok :
    VanderKlok Gitksan.Modals.allExpressions ∧ VanderKlok Statimcets.Modals.allExpressions ∧
      VanderKlok NezPerce.Modals.allExpressions ∧ VanderKlok Niuean.Modals.allExpressions := by
  decide

/-- Table 18.4's hypothetical root system: a deontic modal `x` of either force, a necessity
modal `y` over two flavours, and possibility modals `w` and `z` for one flavour each. -/
def table18_4 : List ModalItem :=
  [⟨"x", {(.necessity, .deontic), (.possibility, .deontic)}, .neutral⟩,
   ⟨"y", {(.necessity, .circumstantial), (.necessity, .bouletic)}, .neutral⟩,
   ⟨"w", {(.possibility, .circumstantial)}, .neutral⟩,
   ⟨"z", {(.possibility, .bouletic)}, .neutral⟩]

/-- The system satisfies the universal and violates the refinement, `x` varying in force and
`y` in flavour within the root domain, so the refinement is strictly stronger. -/
theorem table18_4_singleAxis_not_vanderKlok :
    (∀ m ∈ table18_4, SingleAxis m.meaning) ∧ ¬ VanderKlok table18_4 := by
  decide

end Matthewson2016
