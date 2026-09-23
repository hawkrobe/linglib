module

public import Linglib.Semantics.Modality.Universals
public import Linglib.Semantics.Evidential.Defs
public import Linglib.Data.Examples.Matthewson2016
public import Linglib.Fragments.Gitksan.Modals
public import Linglib.Fragments.Statimcets.Modals
public import Linglib.Fragments.NezPerce.Modals
public import Linglib.Fragments.Niuean.Modals
public import Linglib.Studies.Condoravdi2002
public import Linglib.Studies.Kratzer2012
public import Linglib.Studies.Matthewson2013

/-!
# Matthewson (2016): Modality

This file formalizes the typological claims of the handbook chapter [matthewson-2016]. On
flavour, [kratzer-2012] projects a conversational background in a factual mode, over the worlds
holding counterparts of some actual situation or body of evidence, or in a content mode, over
the worlds compatible with what some source of information says. A factual background is
therefore realistic, and realism is exactly the veridicality of necessity, so a factual modal
cannot be followed by the denial of its prejacent while a content modal can: the rumor of
(23)–(24), and St'át'imcets *k'a* against *lákw7a* in (25)–(28). Deniability diagnoses the
content mode rather than ruling out a modal analysis of an evidential. With the
circumstantial–evidential division, whether a background encodes an information source, the
modes give Table 18.3's three classes, which St'át'imcets lexicalizes in full, and Gitksan
keeps its epistemic and circumstantial modals apart.

On force, Gitksan *ima('a)* and *gat*, variable in force, and Nez Perce *o'qa*, a possibility
modal that no necessity modal competes with ([deal-2011]), are modals without duals. On
modal–temporal interaction, Gitksan marks future orientation with the prospective *dim* where
English marks past orientation with the perfect, a mirror image derived from the Gitksan
fragment and from [condoravdi-2002]. On typology, Gitksan and Niuean distinguish force among
circumstantial modals and not among epistemic ones, and [vander-klok-2013b]'s refinement of
[nauze-2008]'s universal, one axis of variation per modal domain, is strictly stronger than the
universal and holds of the four inventories.

## Implementation notes

* A factual-mode base is realistic, the actual world holding the situation or evidence whose
  counterparts it projects, and a content-mode base is unconstrained. Deniability is stated for
  necessity, the force of *must* in (23)–(24).
* The rows are joined to the fragments through `parse?` tables, and every row naming a modal
  resolves (`rows_resolve`), so no row theorem holds by a failed lookup.
* Table 18.4's hypothetical root system has a teleological flavour, which the library folds
  into circumstantial; bouletic stands in for it, which keeps the system ambiguous along both
  axes.
* The English column of Table 18.3 is not formalized, no fragment recording the source or
  mode of the English modals.

## TODO

* §18.3.2 contrasts [peterson-2010]'s *ima('a)*, a possibility modal strengthened by an ordering
  source, with [deal-2011]'s *o'qa*, a possibility modal without a scale, whose use in necessity
  contexts reflects only the absence of a scalar implicature: the two agree in upward-entailing
  contexts and part in downward-entailing ones, where necessity no longer entails possibility.
  `oqa_rows` records the pattern; deriving it from the monotonicity of the context is open.

## References

* [matthewson-2016]
* [kratzer-2012]
* [matthewson-2013]
* [rullmann-matthewson-davis-2008]
* [peterson-2010]
* [deal-2011]
* [nauze-2008]
* [vander-klok-2013b]
* [condoravdi-2002]
-/

@[expose] public section

namespace Matthewson2016

open Modality Modality.Kratzer Data.Examples Evidential

/-! ### Modes of projection (Table 18.2) -/

/-- [kratzer-2012]'s modes of projecting a conversational background: factual, over the worlds
holding counterparts of some actual situation or body of evidence, and content, over the worlds
compatible with the propositional content of some source of information. -/
inductive ProjectionMode where
  | factual
  | content
  deriving DecidableEq, Repr, Fintype

variable {W : Type*} {f : ModalBase W} {μ : ProjectionMode}

/-- The modal bases a mode projects. The actual world holds the situation or evidence whose
counterparts a factual base projects, so a factual base is realistic; the content of a source
may be false, so a content base need not be. -/
def ProjectionMode.Admits : ProjectionMode → ModalBase W → Prop
  | .factual, f => isRealistic f
  | .content, _ => True

/-- A modal base allows *must p, but not p* when at some world `p` is necessary and false. -/
def Deniable (f : ModalBase W) : Prop := ∃ p w, simpleNecessity f p w ∧ ¬ p w

/-- A base allows the denial of a necessity claim exactly when it is not realistic. -/
theorem deniable_iff_not_isRealistic : Deniable f ↔ ¬ isRealistic f := by
  simp [Deniable, isRealistic_iff_simpleNecessity_le_id, Pi.le_def]

/-- A mode is veridical over a space of worlds when no base it projects there allows the denial
of a necessity claim. -/
def ProjectionMode.Veridical (μ : ProjectionMode) (W : Type*) : Prop :=
  ∀ f : ModalBase W, μ.Admits f → ¬ Deniable f

/-- Deniability diagnoses the content mode: over any worlds, a mode is veridical exactly when it
is factual, a content base being free to hold what holds nowhere. -/
theorem ProjectionMode.veridical_iff [Nonempty W] : μ.Veridical W ↔ μ = .factual := by
  cases μ
  · exact iff_of_true (fun _ hf h ↦ deniable_iff_not_isRealistic.1 h hf) rfl
  · refine iff_of_false (fun h ↦ h (fun _ ↦ [fun _ ↦ False]) trivial ?_) nofun
    exact deniable_iff_not_isRealistic.2 fun hr ↦ hr ‹Nonempty W›.some _ (List.mem_singleton_self _)

instance [Nonempty W] : Decidable (μ.Veridical W) :=
  decidable_of_iff _ ProjectionMode.veridical_iff.symm

/-- (23)–(24): the rumor as evidence of things projects factually and rules out *given the rumor,
Roger must have been elected chief, but he actually wasn't*; the rumor's content allows
*according to the rumor* to be denied. -/
theorem rumor :
    ProjectionMode.factual.Admits Kratzer2012.evidence ∧ ¬ Deniable Kratzer2012.evidence ∧
      Deniable Kratzer2012.content :=
  ⟨Kratzer2012.evidence_realistic,
    fun h ↦ deniable_iff_not_isRealistic.1 h Kratzer2012.evidence_realistic,
    deniable_iff_not_isRealistic.2 Kratzer2012.content_not_realistic⟩

/-! ### The three-way classification (Table 18.3) -/

/-- The chapter's three classes of conversational backgrounds: factual backgrounds without an
information source, the traditional circumstantial class, and factual and content backgrounds
encoding one, the two epistemic subtypes. -/
inductive BackgroundClass where
  | factualCircumstantial
  | factualEvidential
  | contentEvidential
  deriving DecidableEq, Repr, Fintype

/-- The mode in which a class projects. -/
def BackgroundClass.projectionMode : BackgroundClass → ProjectionMode
  | .factualCircumstantial => .factual
  | .factualEvidential => .factual
  | .contentEvidential => .content

/-- The traditional epistemic or circumstantial flavour a class refines. -/
def BackgroundClass.traditionalFlavor : BackgroundClass → ModalFlavor
  | .factualCircumstantial => .circumstantial
  | .factualEvidential => .epistemic
  | .contentEvidential => .epistemic

/-- Table 18.2: the traditional circumstantial class is factual, and the new classification
splits the traditional epistemic class by mode. -/
theorem table18_2 :
    (∀ c : BackgroundClass, c.traditionalFlavor = .circumstantial → c.projectionMode = .factual) ∧
      ∀ μ, ∃ c : BackgroundClass, c.traditionalFlavor = .epistemic ∧ c.projectionMode = μ := by
  decide

/-- The factual–content and circumstantial–evidential divisions determine the class. -/
theorem projectionMode_traditionalFlavor_injective :
    Function.Injective fun c : BackgroundClass ↦ (c.projectionMode, c.traditionalFlavor) := by
  decide

/-- The class of a modal from its mode and the information source it encodes, if any. -/
def BackgroundClass.ofMode (μ : ProjectionMode) : Option EvidenceType → BackgroundClass
  | none => .factualCircumstantial
  | some _ => if μ = .factual then .factualEvidential else .contentEvidential

variable {s : Option EvidenceType}

/-- The circumstantial–evidential division is whether an information source is encoded. -/
theorem BackgroundClass.traditionalFlavor_ofMode :
    (ofMode μ s).traditionalFlavor = .circumstantial ↔ s = none := by
  cases s <;> cases μ <;> simp [ofMode, traditionalFlavor]

/-- The factual–content division is the mode, a background without a source being factual. -/
theorem BackgroundClass.projectionMode_ofMode (h : s = none → μ = .factual) :
    (ofMode μ s).projectionMode = μ := by
  cases s <;> cases μ <;> simp_all [ofMode, projectionMode]

/-! ### Rows -/

/-- The modals the chapter's rows name, keyed by their forms. -/
def modalTable : List (String × ModalItem) :=
  [Statimcets.kaInfer, Statimcets.lakw7a, Gitksan.imaa, NezPerce.oqa, Niuean.liga, Niuean.maeke,
    Niuean.lata].map fun m ↦ (m.form, m)

/-- Every row naming a modal names one of the fragments'. -/
theorem rows_resolve :
    ∀ e ∈ Examples.all, (e.feature? "modal").isSome → (e.parse? "modal" modalTable).isSome := by
  decide

section Statimcets
open Statimcets

/-- The mode in which a St'át'imcets modal projects: *lákw7a* from the content of its sensory
evidence, the other evidentials and the circumstantial modals factually (Table 18.3). -/
def statimcetsMode (m : ModalItem) : ProjectionMode := if m = lakw7a then .content else .factual

/-- The class of a St'át'imcets modal. -/
def statimcetsClass (m : ModalItem) : BackgroundClass := .ofMode (statimcetsMode m) (source m)

/-- Table 18.3's St'át'imcets row. -/
theorem table18_3 :
    statimcetsClass ka = .factualCircumstantial ∧
      statimcetsClass kaCircumfix = .factualCircumstantial ∧
      statimcetsClass kaInfer = .factualEvidential ∧ statimcetsClass ku7 = .factualEvidential ∧
      statimcetsClass lakw7a = .contentEvidential := by
  decide

/-- St'át'imcets encodes the full three-way split. -/
theorem statimcets_full_split : ∀ c : BackgroundClass, ∃ m ∈ modals, statimcetsClass m = c := by
  decide

/-- (25)–(28): a modal survives *but it was the wind* exactly when its mode allows the denial of
its prejacent, as the content *lákw7a* does and the factual *k'a* does not. -/
theorem deniability_rows (W : Type*) [Nonempty W] :
    ∀ e ∈ Examples.all, e.feature? "test" = some "deniability" →
      ∃ m ∈ e.parse? "modal" modalTable,
        (e.judgment = .acceptable ↔ ¬ (statimcetsMode m).Veridical W) := by
  simp only [ProjectionMode.veridical_iff]
  decide

end Statimcets

/-! ### Gitksan: epistemic and circumstantial apart (Table 18.1) -/

/-- The split between epistemic and circumstantial readings is absolute in Gitksan: each modal
selects one type, [matthewson-2013]'s type selectivity. -/
theorem gitksan_absolute_split : Matthewson2013.TypeSelective Gitksan.modals :=
  Matthewson2013.gitksan_mixed.1

/-! ### Modal force: modals without duals (§18.3.2)

A modal without a dual comes in no necessity–possibility pair and is used in contexts
supporting either claim: Gitksan *ima('a)* and *gat*, variable in force, and Nez Perce *o'qa*,
a possibility modal usable in necessity contexts because no necessity modal competes with it to
induce a scalar implicature ([deal-2011]). -/

/-- A modal has a dual in an inventory when it is fixed for one force and another item of the
inventory expresses the dual force over its flavours. -/
def HasDualIn (L : List ModalItem) (m : ModalItem) : Prop :=
  m.forces.card = 1 ∧ ∃ m' ∈ L, m'.meaning = m.meaning.image (Prod.map ModalForce.dual id)

instance (L : List ModalItem) (m : ModalItem) : Decidable (HasDualIn L m) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _ = _))

/-- A modal varying in force has no dual. -/
theorem not_hasDualIn_of_variesForce {L : List ModalItem} {m : ModalItem} (h : m.VariesForce) :
    ¬ HasDualIn L m :=
  fun h' ↦ Nat.not_succ_le_self 1 (h.trans_eq h'.1)

/-- Gitksan ima('a) and gat vary in force, and Nez Perce o'qa has no necessity counterpart, so
none has a dual in its inventory. -/
theorem no_duals :
    ¬ HasDualIn Gitksan.modals Gitksan.imaa ∧ ¬ HasDualIn Gitksan.modals Gitksan.gat ∧
      ¬ HasDualIn NezPerce.modals NezPerce.oqa :=
  ⟨not_hasDualIn_of_variesForce (by decide), not_hasDualIn_of_variesForce (by decide), by decide⟩

/-- The force a reading names. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("necessity", .necessity)]

/-- (37): ima('a) is read with each force it expresses. -/
theorem imaa_rows :
    ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some Gitksan.imaa →
      ∀ r ∈ e.readings, ∃ fo ∈ forceTable.lookup r.1,
        (r.2 = .acceptable ↔ fo ∈ Gitksan.imaa.forces) := by
  decide

/-- (39)–(40): o'qa takes a possibility translation everywhere and a necessity translation
exactly outside a downward-entailing context, the profile of a possibility modal without a
necessity competitor. -/
theorem oqa_rows :
    ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some NezPerce.oqa →
      ∀ r ∈ e.readings, ∃ fo ∈ forceTable.lookup r.1,
        (r.2 = .acceptable ↔
          fo ∈ NezPerce.oqa.forces ∨ e.feature? "downwardEntailing" = some "false") := by
  decide

/-! ### Modal–temporal interaction (§18.4.3) -/

/-- (60)–(63): under a fixed past perspective ima('a) takes every orientation, and is
acceptable without the prospective *dim* exactly when not future-oriented, as
[matthewson-2013]'s `RequiresDim` records. -/
theorem gitksan_orientation_rows :
    ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some Gitksan.imaa →
      ∀ s ∈ e.feature? "orientation", ∃ o ∈ Matthewson2013.orientationOf s,
        (e.judgment = .acceptable ↔
          e.feature? "prospective" = some "true" ∨
            ¬ Matthewson2013.RequiresDim Gitksan.imaa o) := by
  decide

/-- English marks past orientation, by the perfect under the modal among [condoravdi-2002]'s
scopings, and Gitksan future orientation, by *dim*: the mirror image of §18.4.3. -/
theorem marking_mirror :
    (∀ s : Condoravdi2002.Scope, s.orientation = .past ↔ s = .modalPerf) ∧
      ∀ o : TemporalOrientation,
        Matthewson2013.RequiresDim Gitksan.imaa o ↔ o = .future := by
  decide

/-! ### Typology (§18.5) -/

/-- An inventory distinguishes force within a domain when two of its modals there express
different sets of forces. -/
def DistinguishesForce (L : List ModalItem) (D : ModalItem → Prop) : Prop :=
  ∃ m ∈ L, ∃ m' ∈ L, D m ∧ D m' ∧ m.forces ≠ m'.forces

instance (L : List ModalItem) (D : ModalItem → Prop) [DecidablePred D] :
    Decidable (DistinguishesForce L D) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _ ∧ _ ∧ _ ≠ _))

/-- The flavour–force correlation: Gitksan and Niuean distinguish force among their
circumstantial modals and not among their epistemic ones. -/
theorem force_only_circumstantial :
    (¬ DistinguishesForce Gitksan.modals ModalItem.Epistemic ∧
        DistinguishesForce Gitksan.modals ModalItem.Circumstantial) ∧
      ¬ DistinguishesForce Niuean.modals ModalItem.Epistemic ∧
        DistinguishesForce Niuean.modals ModalItem.Circumstantial := by
  decide

/-- Niuean's circumstantial *maeke* and *lata* are duals; its epistemic *liga* has none. -/
theorem niuean_duals :
    HasDualIn Niuean.modals Niuean.maeke ∧
      HasDualIn Niuean.modals Niuean.lata ∧
      ¬ HasDualIn Niuean.modals Niuean.liga := by
  decide

/-- The strength a Niuean row records. -/
def strengthTable : List (String × ModalForce) := [("weak", .possibility), ("strong", .necessity)]

/-- The flavour a Niuean row records. -/
def flavorTable : List (String × ModalFlavor) :=
  [("epistemic", .epistemic), ("circumstantial", .circumstantial)]

/-- (64)–(68): each Niuean example expresses a force and flavour its modal has, and *liga* is
attested with each of its forces. -/
theorem niuean_rows :
    (∀ e ∈ Examples.all, e.feature? "section" = some "18.5" → (e.feature? "force").isSome →
      ∃ m ∈ e.parse? "modal" modalTable, ∃ fo ∈ e.parse? "force" strengthTable,
        ∃ fl ∈ e.parse? "flavor" flavorTable, (fo, fl) ∈ m.meaning) ∧
      ∀ fo ∈ Niuean.liga.forces, ∃ e ∈ Examples.all,
        e.parse? "modal" modalTable = some Niuean.liga ∧
          e.parse? "force" strengthTable = some fo := by
  decide

/-- [nauze-2008]'s universal holds of the four inventories: every modal varies on one axis. -/
theorem nauze :
    ∀ e ∈ Gitksan.modals ++ Statimcets.modals ++
      NezPerce.modals ++ Niuean.modals, SingleAxis e.meaning := by
  decide

/-- An inventory varies along one axis within a domain when its modals there do not vary in
force and in flavour both. -/
def OneAxisWithin (L : List ModalItem) (D : ModalItem → Prop) : Prop :=
  ¬ ((∃ m ∈ L, D m ∧ m.VariesForce) ∧ ∃ m ∈ L, D m ∧ m.VariesFlavor)

instance (L : List ModalItem) (D : ModalItem → Prop) [DecidablePred D] :
    Decidable (OneAxisWithin L D) :=
  inferInstanceAs (Decidable (¬ (_ ∧ _)))

/-- A modal of a one-axis domain varies on one axis. -/
theorem OneAxisWithin.singleAxis {L : List ModalItem} {D : ModalItem → Prop}
    (h : OneAxisWithin L D) {m : ModalItem} (hm : m ∈ L) (hD : D m) : SingleAxis m.meaning :=
  ModalItem.singleAxis_meaning_iff.2 fun hv ↦ h ⟨⟨m, hm, hD, hv.1⟩, m, hm, hD, hv.2⟩

/-- [vander-klok-2013b]'s refinement of the universal: within each domain, epistemic and
non-epistemic, an inventory varies along one axis only. -/
def VanderKlok (L : List ModalItem) : Prop :=
  OneAxisWithin L ModalItem.Epistemic ∧ OneAxisWithin L (¬ ·.Epistemic)

instance (L : List ModalItem) : Decidable (VanderKlok L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The refinement entails the universal, each modal lying in one of the two domains. -/
theorem VanderKlok.singleAxis {L : List ModalItem} (h : VanderKlok L) {m : ModalItem}
    (hm : m ∈ L) : SingleAxis m.meaning := by
  by_cases he : m.Epistemic
  exacts [h.1.singleAxis hm he, h.2.singleAxis hm he]

/-- The four inventories satisfy the refinement. -/
theorem inventories_vanderKlok :
    VanderKlok Gitksan.modals ∧ VanderKlok Statimcets.modals ∧
      VanderKlok NezPerce.modals ∧ VanderKlok Niuean.modals := by
  decide

/-- Table 18.4's hypothetical root system: a deontic modal `x` of either force, a necessity
modal `y` over two flavours, and possibility modals `w` and `z` for one flavour each. -/
def hypotheticalRootSystem : List ModalItem :=
  [⟨"x", {(.necessity, .deontic), (.possibility, .deontic)}, .neutral⟩,
   ⟨"y", {(.necessity, .circumstantial), (.necessity, .bouletic)}, .neutral⟩,
   ⟨"w", {(.possibility, .circumstantial)}, .neutral⟩,
   ⟨"z", {(.possibility, .bouletic)}, .neutral⟩]

/-- The system satisfies the universal and violates the refinement, `x` varying in force and
`y` in flavour within the root domain, so the refinement is strictly stronger. -/
theorem hypotheticalRootSystem_singleAxis_not_vanderKlok :
    (∀ m ∈ hypotheticalRootSystem, SingleAxis m.meaning) ∧ ¬ VanderKlok hypotheticalRootSystem := by
  decide

end Matthewson2016
