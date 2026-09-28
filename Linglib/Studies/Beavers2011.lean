module

public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.Events.Basic
public import Linglib.Studies.KennedyLevin2008
public import Linglib.Studies.Beavers2010

/-!
# Beavers (2011): On Affectedness

This file formalizes Beavers's analysis of affectedness as specificity about scalar change. A
predicate relates its theme to a scale, and how strongly it affects the theme is how much it says
about where the theme ends up on that scale. Change is an increase from a contextually given source
to a later goal, following Hay, Kennedy and Levin, so *the soup cooled 5 degrees* effects a
quantized change, *the soup cooled* a non-quantized one, and both entail that the soup changed. The
telic reading that Kennedy and Levin derive for a degree achievement on a scale closed above is a
quantized change to the maximum, and the atelic reading a non-quantized change.

Each degree of affectedness is an existential generalization of the one above it, so the
entailments a predicate has about its theme form one of four sets. These are exactly the four
contentful thematic roles of patienthood in Beavers's earlier work, each the entailment set of some
predicate.

## Implementation notes

* A scale `s` indexes a measure function `m s`. An event's result on `s` is where its theme ends,
  provided the theme started at the contextual source `b` and ended higher, which is SOURCE and
  GOAL (48) with the increase of (43).
* The goal of the measure-phrase reading is `b + n`, fixed only relative to the contextual source,
  whereas Beavers's exemplars of quantized change such as *break* have a lexical goal.
* Hay, Kennedy and Levin judge *broaden the investigation significantly* telic, since its
  difference value has a lower bound (`HayKennedyLevin1999.isBounded_significantly`). A
  lower-bounded change is non-quantized, and the diagnostics of (63) count only quantized change
  as telic. The two papers define telicity differently, as a bounded difference value and as a
  predicate that describes no proper part of its events.

## TODO

* Derive the telicity of quantized change, the first row of (63), from the Figure/Path Relation
  (53), with scales as Krifka's paths (`Krifka1998.isTelic_sourceGoal`).
* The remaining diagnostics of (63)–(66) and the result-phrase data of §5.

## References

* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [J. Hay, C. Kennedy and B. Levin, *Scalar Structure Underlies Telicity in “Degree
  Achievements”* (1999)][hay-kennedy-levin-1999]
* [C. Kennedy and B. Levin, *Measure of Change: The Adjectival Core of Degree Achievements*
  (2008)][kennedy-levin-2008]
* [J. Beavers, *The structure of lexical meaning: Why semantics really matters*
  (2010)][beavers-2010]
-/

@[expose] public section

namespace Beavers2011

open ArgumentStructure HayKennedyLevin1999 Set

variable {α S D T : Type*} [LinearOrder T]

/-! ### Scalar change (§4.1) -/

section Result

variable [LinearOrder D]

/-- `Result m b x s g e` holds when the theme `x` starts the event `e` at the contextual source `b`
on the scale `s` and ends it at the higher goal `g`, the result relation of (48). -/
def Result (m : S → α → T → D) (b : D) (x : α) (s : S) (g : D) (e : Event T) : Prop :=
  m s x e.τ.fst = b ∧ b < g ∧ m s x e.τ.snd = g

variable {m : S → α → T → D} {b : D} {θ : α → S → Event T → Prop} {φ : α → Event T → Prop}

/-- A non-quantized change entails that the theme ends the event with more of the property than
it began with, so that *the soup cooled 5 degrees, but nothing is different about it* is
contradictory ((59)). -/
theorem exists_lt_of_nonQuantizedChange (h : NonQuantizedChange θ (Result m b) φ) {x : α}
    {e : Event T} (hx : φ x e) : ∃ s, θ x s e ∧ m s x e.τ.fst < m s x e.τ.snd :=
  let ⟨s, hs, _, h₁, h₂, h₃⟩ := h x e hx
  ⟨s, hs, h₁ ▸ h₃ ▸ h₂⟩

/-- On a predicate whose only scale is `s₀`, a quantized change to `g` ends every event at `g`. -/
theorem snd_eq_of_quantizedChange {s₀ : S} {g : D} (hθ : ∀ x s e, θ x s e → s = s₀)
    (h : QuantizedChange θ (Result m b) φ g) {x : α} {e : Event T} (hx : φ x e) :
    m s₀ x e.τ.snd = g :=
  let ⟨s, hs, _, _, h₃⟩ := h x e hx
  hθ x s e hs ▸ h₃

/-- A predicate on the single scale `s₀` with two events that end at different goals effects no
quantized change, since a quantized change fixes one goal for all its events (p. 357). -/
theorem not_quantizedChange_of_snd_ne {s₀ : S} (hθ : ∀ x s e, θ x s e → s = s₀) {x x' : α}
    {e e' : Event T} (hx : φ x e) (hx' : φ x' e') (hne : m s₀ x e.τ.snd ≠ m s₀ x' e'.τ.snd) :
    ¬ ∃ g, QuantizedChange θ (Result m b) φ g := fun ⟨_, h⟩ ↦
  hne ((snd_eq_of_quantizedChange hθ h hx).trans (snd_eq_of_quantizedChange hθ h hx').symm)

end Result

/-! ### Quantized and non-quantized change as difference values ((58)) -/

section HayKennedyLevin

variable [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] {m : S → α → T → D} {b : D}
  {s₀ : S} {φ : α → Event T → Prop}

/-- On a predicate whose scale is `s₀`, a quantized change to `b + n` for a positive `n` is the
reading of [hay-kennedy-levin-1999] with the measure phrase `n` from the source `b`, as in *the
soup cooled 5 degrees* ((58a)). -/
theorem quantizedChange_iff_describes_measurePhrase {n : D} (hn : 0 < n) :
    QuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ (b + n) ↔
      ∀ x e, φ x e → m s₀ x e.τ.fst = b ∧
        Describes (m s₀) x (measurePhrase n) e.τ.fst e.τ.snd := by
  refine forall₂_congr fun x e ↦ imp_congr_right fun _ ↦ ?_
  simp only [Result, exists_eq_left, describes_iff_sub_mem, measurePhrase, mem_singleton_iff,
    lt_add_iff_pos_right, hn, true_and]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, by rw [h₁, h₂, add_sub_cancel_left]⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, by rw [← h₂, h₁, add_sub_cancel]⟩

/-- On a predicate whose scale is `s₀`, a non-quantized change is the reading of
[hay-kennedy-levin-1999] with the difference value "some amount" from the source `b`, as in *the
soup cooled* ((58b)). -/
theorem nonQuantizedChange_iff_describes_someAmount :
    NonQuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ ↔
      ∀ x e, φ x e → m s₀ x e.τ.fst = b ∧
        Describes (m s₀) x someAmount e.τ.fst e.τ.snd := by
  refine forall₂_congr fun x e ↦ imp_congr_right fun _ ↦ ?_
  simp only [Result, exists_eq_left, describes_iff_sub_mem, someAmount, mem_Ioi, sub_pos]
  constructor
  · rintro ⟨g, h₁, h₂, h₃⟩
    exact ⟨h₁, by rw [h₁, h₃]; exact h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, h₁, h₁ ▸ h₂, rfl⟩

end HayKennedyLevin

/-! ### Degree achievements ((60a), (60b)) -/

section KennedyLevin

variable [LinearOrder D] {m : S → α → T → D} {b : D} {s₀ : S} {φ : α → Event T → Prop}

/-- From a source below the maximum, the telic reading of a degree achievement on a scale closed
above, on which the theme reaches the maximum ([kennedy-levin-2008]), is a quantized change to
`⊤`, as for *straighten*. -/
theorem quantizedChange_top_of_maxStandard [OrderTop D] (hb : b ≠ ⊤)
    (h : ∀ x e, φ x e → m s₀ x e.τ.fst = b ∧
      projIci (m s₀ x e.τ.fst) (m s₀ x e.τ.snd) = ⊤) :
    QuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ ⊤ := fun x e hx ↦
  let ⟨h₁, h₂⟩ := h x e hx
  have h₃ := (KennedyLevin2008.maxStandard_iff (m s₀) x _ _ (h₁ ▸ hb)).1 h₂
  ⟨s₀, rfl, h₁, hb.lt_top, h₃⟩

/-- The atelic reading of a degree achievement, on which the theme ends above where it began
([kennedy-levin-2008]), is a non-quantized change, as for *widen* or *cool*. -/
theorem nonQuantizedChange_of_minStandard
    (h : ∀ x e, φ x e → m s₀ x e.τ.fst = b ∧ ⊥ < projIci (m s₀ x e.τ.fst) (m s₀ x e.τ.snd)) :
    NonQuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ := fun x e hx ↦
  let ⟨h₁, h₂⟩ := h x e hx
  have h₃ := (KennedyLevin2008.minStandard_iff (m s₀) x _ _).1 h₂
  ⟨s₀, rfl, _, h₁, h₁ ▸ (Degree.comparativeSem_positive _ _ _).1 h₃, rfl⟩

end KennedyLevin

/-! ### The contentful roles of [beavers-2010] -/

section Roles

open Beavers2010 (PatientLRole)

variable {α S G β : Type*}

open Classical in
/-- The patient role of a predicate is the set of affectedness entailments it has about its theme,
among quantized change, non-quantized change and potential for change ([beavers-2010] (65)). -/
noncomputable def role (θ : α → S → β → Prop) (R : α → S → G → β → Prop) (φ : α → β → Prop) :
    PatientLRole :=
  ⟨decide (AffectednessDegree.Holds θ R φ .quantized),
    decide (AffectednessDegree.Holds θ R φ .nonquantized),
    decide (AffectednessDegree.Holds θ R φ .potential)⟩

variable {θ : α → S → β → Prop} {R : α → S → G → β → Prop} {φ : α → β → Prop}

/-- Every predicate's role is contentful, since each affectedness entailment entails the weaker
ones ([beavers-2010] (67)). -/
theorem role_valid : (role θ R φ).Valid := by
  classical
  simp only [PatientLRole.Valid, role, decide_eq_true_eq]
  exact ⟨AffectednessDegree.holds_antitone θ R φ (by decide),
    AffectednessDegree.holds_antitone θ R φ (by decide)⟩

private theorem forall_degree {P : AffectednessDegree → Prop} :
    (∀ d, P d) ↔ P .unspecified ∧ P .potential ∧ P .nonquantized ∧ P .quantized :=
  ⟨fun h ↦ ⟨h _, h _, h _, h _⟩, fun ⟨h₁, h₂, h₃, h₄⟩ d ↦ by cases d <;> assumption⟩

/-- A predicate has the role that [beavers-2010] names by the degree `d` exactly when `d` is the
strongest degree the predicate entails. -/
theorem role_eq_ofDegree_iff {d : AffectednessDegree} :
    role θ R φ = PatientLRole.ofDegree d ↔
      {d' | AffectednessDegree.Holds θ R φ d'} = Iic d := by
  classical
  rw [Set.ext_iff, forall_degree]
  cases d <;>
    simp [role, PatientLRole.ofDegree, PatientLRole.quantizedRole,
      PatientLRole.nonquantizedRole, PatientLRole.potentialRole,
      PatientLRole.unspecifiedRole, AffectednessDegree.Holds,
      AffectednessDegree.le_iff_strength_le, AffectednessDegree.strength] <;> tauto

/-- Every predicate's role is contentful, and each contentful role is the role of some predicate,
so the contentful roles are exactly the roles of predicates, as the objects of *see*, *hit*, *cut*
and *eat* illustrate ([beavers-2010] (66)–(67)). -/
theorem valid_iff_exists_role (r : PatientLRole) :
    r.Valid ↔ ∃ (θ : Unit → Unit → Bool → Prop) (R : Unit → Unit → Bool → Bool → Prop)
      (φ : Unit → Bool → Prop), role θ R φ = r := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, _, h⟩ ↦ h ▸ role_valid⟩
  rcases (PatientLRole.exactly_four_valid_roles r).1 h with rfl | rfl | rfl | rfl
  on_goal 1 => refine ⟨fun _ _ _ ↦ True, fun _ _ _ _ ↦ True, fun _ _ ↦ True,
    role_eq_ofDegree_iff (d := .quantized) |>.2 ?_⟩
  on_goal 2 => refine ⟨fun _ _ _ ↦ True, fun _ _ g e ↦ g = e, fun _ _ ↦ True,
    role_eq_ofDegree_iff (d := .nonquantized) |>.2 ?_⟩
  on_goal 3 => refine ⟨fun _ _ _ ↦ True, fun _ _ _ _ ↦ False, fun _ _ ↦ True,
    role_eq_ofDegree_iff (d := .potential) |>.2 ?_⟩
  on_goal 4 => refine ⟨fun _ _ _ ↦ False, fun _ _ _ _ ↦ False, fun _ _ ↦ True,
    role_eq_ofDegree_iff (d := .unspecified) |>.2 ?_⟩
  all_goals ext d; cases d <;> simp [AffectednessDegree.Holds, QuantizedChange,
    NonQuantizedChange, PotentialChange, AffectednessDegree.le_iff_strength_le,
    AffectednessDegree.strength]

end Roles

end Beavers2011
