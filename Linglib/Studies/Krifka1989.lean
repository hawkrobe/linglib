import Linglib.Semantics.Mereology
import Linglib.Semantics.ArgumentStructure.Thematic.Mereology
import Linglib.Semantics.Aspect.Cumulativity
import Mathlib.Order.WellFounded

/-!
# Krifka (1989): Nominal Reference, Temporal Constitution and Quantification in Event Semantics

This file formalizes the paper's algebraic account of the parallel between nominal reference
and temporal constitution. Objects, events, and times each form a join semilattice, and a
predicate over one of them has cumulative reference when it is closed under join and
quantized reference when no instance is a proper part of another; singular, strictly
cumulative, strictly quantized, and atomic reference are the variants of §2, with the paper's
theorems relating them, and predicates cut out by an extensive measure function are
quantized. In §3 mass nouns are cumulative, bare plurals cumulative by algebraic closure, and
measure constructions and count nouns quantized by their measure functions. In §4 a verbal
predicate is built from a verb, a nominal predicate, and a thematic relation, and the
reference type of the nominal predicate transfers to the verbal one through properties of
the relation: summativity carries cumulativity across (T 7), uniqueness of objects and
mapping to objects carry quantization across when the relation is not iterative (T 11), which
uniqueness of events guarantees (T 10, T 12), and mapping to events with strict quantization
yields atomicity (T 13). Graduality bundles the mapping properties (D 35), and the five
classes of (14) sort transitive verbs by summativity, graduality, and uniqueness of events.
In §5 durative adverbials are quantizing modifiers on events through the derived measure of
the temporal trace, and time-span adverbials, which are upward entailing in their number,
require atomic rather than quantized verbal predicates.

## Implementation notes

The paper's relations are stated with the library's object-first thematic relations, so its
uniqueness of objects is `UP`, uniqueness of events `GUE`, mapping to objects `MO`, mapping
to events `ME`, and summativity `CumTheta`; cumulative and quantized reference are
`Mereology.CUM` and `Mereology.QUA`. Theorem (T 3) needs a nonempty predicate, since the
empty predicate is both quantized and strictly cumulative. The proof of (T 13) establishes
that every verbal event has a part outside the predicate; its conclusion that the event
therefore contains an atom holds when the part order on events is well founded, in which case
every predicate has atomic reference, which `atm_of_wellFoundedLT` records. The sections on
negation (§6) and quantification (§7) are prose.

## References

* [krifka-1989]
* [link-1983] — the lattice-theoretic mereology
* [krifka-1998] — the later development of the transfer properties
-/

namespace Krifka1989

open Mereology ArgumentStructure Aspect.Cumulativity

/-! ### Reference types (§2) -/

section Reference

variable {α : Type*} [SemilatticeSup α]

/-- (D 11): singular reference. -/
def SNG (P : α → Prop) : Prop := ∃ x, P x ∧ ∀ y, P y → x = y

/-- (D 13): strictly cumulative reference. -/
def SCUM (P : α → Prop) : Prop := CUM P ∧ ¬ SNG P

/-- (D 15): strictly quantized reference, every instance having a proper part. -/
def SQUA (P : α → Prop) : Prop := QUA P ∧ ∀ x, P x → ∃ y, y < x

/-- (D 18): atomic reference, every instance having a part that is a `P`-atom (D 17). -/
def ATM (P : α → Prop) : Prop := ∀ x, P x → ∃ y ≤ x, atomize P y

/-- (T 1). -/
theorem qua_of_sng {P : α → Prop} (h : SNG P) : QUA P :=
  let ⟨_, _, hx⟩ := h
  qua_of_forall λ a b ha hlt hb => hlt.ne ((hx b hb).symm.trans (hx a ha))

/-- (T 2). -/
theorem cum_of_sng {P : α → Prop} (h : SNG P) : CUM P := by
  obtain ⟨x, hx, huniq⟩ := h
  intro a ha b hb
  rw [← huniq a ha, ← huniq b hb, sup_idem]
  exact hx

/-- (T 3), for a nonempty predicate. -/
theorem not_scum_of_qua {P : α → Prop} (hne : ∃ x, P x) (h : QUA P) : ¬ SCUM P := by
  rintro ⟨hcum, hsng⟩
  obtain ⟨x, hx⟩ := hne
  refine hsng ⟨x, hx, λ y hy => ?_⟩
  by_contra hxy
  have hsup := hcum hx hy
  rcases eq_or_ne (x ⊔ y) x with hxs | hxs
  · exact h hy hx (Ne.symm hxy) (hxs ▸ le_sup_right)
  · exact h hx hsup hxs.symm le_sup_left

/-- (T 4): quantized reference is atomic, each instance being its own atom. -/
theorem atm_of_qua {P : α → Prop} (h : QUA P) : ATM P := λ x hx =>
  ⟨x, le_rfl, hx, λ z hz hzx => by
    rcases eq_or_lt_of_le hzx with rfl | hlt
    · exact le_rfl
    · exact (h hz hx hlt.ne hlt.le).elim⟩

/-- (T 6): a predicate restricted by an extensive measure function to a value is quantized. -/
theorem qua_of_extMeasure {M : Type*} [AddCommMonoid M] [PartialOrder M] (μ : α → M)
    [ExtMeasure μ] (n : M) : QUA (μ · = n) :=
  extMeasure_qua n

/-- With a well-founded part order every predicate has atomic reference: the minimal
instances below any instance are its atoms. -/
theorem atm_of_wellFoundedLT [WellFoundedLT α] (P : α → Prop) : ATM P := λ x hx => by
  obtain ⟨y, ⟨hy, hyx⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {y | P y ∧ y ≤ x} ⟨x, hx, le_rfl⟩
  exact ⟨y, hyx, hy, λ z hz hzy => (eq_of_le_of_not_lt hzy (hmin z ⟨hz, hzy.trans hyx⟩)).symm.le⟩

end Reference

/-! ### Nominal predicates (§3) -/

section Nominal

variable {α : Type*} [SemilatticeSup α]

/-- A bare plural: the algebraic closure of the count noun under join, which is
cumulative. -/
theorem barePlural_cum (P : α → Prop) : CUM (AlgClosure P) := algClosure_cum

/-- The measure construction (4): a cumulative noun restricted by an extensive measure
function is quantized (D 28), which is why measure phrases do not iterate (3c). -/
theorem measure_qua {M : Type*} [AddCommMonoid M] [PartialOrder M] {P : α → Prop}
    (_ : CUM P) (μ : α → M) [ExtMeasure μ] (n : M) : QUA (QMOD P μ n) :=
  qmod_qua P n

/-- A count noun (6) is a classifier construction with the natural unit built in: the noun's
predicate restricted by the natural-unit measure to a number, hence quantized. -/
theorem countNoun_qua {M : Type*} [AddCommMonoid M] [PartialOrder M] (P : α → Prop)
    (NU : α → M) [ExtMeasure NU] (n : M) : QUA (QMOD P NU n) :=
  qmod_qua P n

end Nominal

/-! ### Transfer of reference from objects to events (§4) -/

section Transfer

variable {O E : Type*} [SemilatticeSup O] [SemilatticeSup E]

/-- The verbal predicate (12): a verb, a nominal predicate, and a thematic relation. -/
def ofTheta (α : E → Prop) (δ : O → Prop) (θ : O → E → Prop) : E → Prop :=
  λ e => α e ∧ ∃ x, δ x ∧ θ x e

/-- (D 34): iterativity, some part of the object being subjected to two parts of the
event. -/
def ITER (θ : O → E → Prop) (e : E) (x : O) : Prop :=
  θ x e ∧ ∃ e' e'' x', e' ≤ e ∧ e'' ≤ e ∧ e' ≠ e'' ∧ x' ≤ x ∧ θ x' e' ∧ θ x' e''

/-- (D 35): graduality, uniqueness of objects with both mappings. -/
def GRAD (θ : O → E → Prop) : Prop := UP θ ∧ MO θ ∧ ME θ

variable {α : E → Prop} {δ : O → Prop} {θ : O → E → Prop}

/-- (T 7): a cumulative verb, a cumulative nominal predicate, and a summative relation
give a cumulative verbal predicate. -/
theorem cum_ofTheta (hα : CUM α) (hδ : CUM δ) (hθ : CumTheta θ) : CUM (ofTheta α δ θ) :=
  λ e ⟨ha, x, hx, hθx⟩ e' ⟨ha', x', hx', hθx'⟩ =>
    ⟨hα ha ha', x ⊔ x', hδ hx hx', hθ x x' e e' hθx hθx'⟩

/-- (T 8): a singular nominal predicate, a summative relation, and a strictly cumulative
verbal predicate force an iterative event, since two distinct events with the one object
sum to an event subjecting it twice. -/
theorem exists_iter (hδ : SNG δ) (hθ : CumTheta θ) (hne : ∃ e, ofTheta α δ θ e)
    (hs : SCUM (ofTheta α δ θ)) : ∃ e x, ITER θ e x := by
  obtain ⟨e₁, hα₁, x₁, hx₁, hθ₁⟩ := hne
  obtain ⟨hcum, hsng⟩ := hs
  have : ∃ e₂, ofTheta α δ θ e₂ ∧ e₁ ≠ e₂ := by
    by_contra h
    exact hsng ⟨e₁, ⟨hα₁, x₁, hx₁, hθ₁⟩, λ e₂ he₂ => by
      by_contra hne
      exact h ⟨e₂, he₂, hne⟩⟩
  obtain ⟨e₂, ⟨_, x₂, hx₂, hθ₂⟩, hne⟩ := this
  obtain ⟨x, _, huniq⟩ := hδ
  rw [← huniq x₁ hx₁] at hθ₁
  rw [← huniq x₂ hx₂] at hθ₂
  exact ⟨e₁ ⊔ e₂, x, by simpa using hθ x x e₁ e₂ hθ₁ hθ₂, e₁, e₂, x, le_sup_left,
    le_sup_right, hne, le_rfl, hθ₁, hθ₂⟩

/-- (T 9): without iteration the verbal predicate of a singular nominal predicate is not
strictly cumulative. -/
theorem not_scum_of_not_iter (hδ : SNG δ) (hθ : CumTheta θ) (hne : ∃ e, ofTheta α δ θ e)
    (hi : ∀ e x, ¬ ITER θ e x) : ¬ SCUM (ofTheta α δ θ) := λ hs =>
  let ⟨e, x, h⟩ := exists_iter hδ hθ hne hs; hi e x h

/-- (T 10): uniqueness of events excludes iteration. -/
theorem not_iter_of_gue (h : GUE θ) (e : E) (x : O) : ¬ ITER θ e x :=
  λ ⟨_, _, _, _, _, _, hne, _, h', h''⟩ => hne (h _ _ _ h' h'')

/-- (T 11): a quantized nominal predicate transfers quantization to the verbal predicate when
the relation has uniqueness of objects, mapping to objects, and no iteration. -/
theorem qua_ofTheta (hδ : QUA δ) (hu : UP θ) (hm : MO θ) (hi : ∀ e x, ¬ ITER θ e x) :
    QUA (ofTheta α δ θ) :=
  qua_of_forall λ e₁ e₂ ⟨_, x₁, hx₁, hθ₁⟩ hlt ⟨_, x₂, hx₂, hθ₂⟩ => by
    obtain ⟨x₃, hx₃, hθ₃⟩ := hm x₁ e₁ e₂ hθ₁ hlt.le
    have h32 : x₃ = x₂ := hu x₃ x₂ e₂ hθ₃ hθ₂
    subst h32
    have hne : x₁ ≠ x₃ := λ h =>
      hi e₁ x₁ ⟨hθ₁, e₁, e₂, x₁, le_rfl, hlt.le, hlt.ne', le_rfl, hθ₁, h ▸ hθ₃⟩
    exact hδ hx₂ hx₁ hne.symm hx₃

/-- (T 12): the special case of uniqueness of events, as for effected and consumed
objects. -/
theorem qua_ofTheta_of_gue (hδ : QUA δ) (hu : UP θ) (hm : MO θ) (hg : GUE θ) :
    QUA (ofTheta α δ θ) :=
  qua_ofTheta hδ hu hm (not_iter_of_gue hg)

/-- The step of (T 13): with a strictly quantized nominal predicate, mapping to events,
and uniqueness of objects, every verbal event has a part outside the verbal predicate. -/
theorem exists_le_not_ofTheta (hδ : SQUA δ) (hm : ME θ) (hu : UP θ) (e : E)
    (he : ofTheta α δ θ e) : ∃ e' ≤ e, ¬ ofTheta α δ θ e' := by
  obtain ⟨_, x, hx, hθx⟩ := he
  obtain ⟨y, hyx⟩ := hδ.2 x hx
  obtain ⟨e', he', hθy⟩ := hm x e y hθx hyx.le
  refine ⟨e', he', λ ⟨_, z, hz, hθz⟩ => ?_⟩
  have hzy : z = y := hu z y e' hθz hθy
  subst hzy
  exact hδ.1 hz hx hyx.ne hyx.le

/-! ### The classification of thematic relations (14) -/

/-- The five classes of (14): gradual effected patient (*write a letter*), gradual consumed
patient (*eat an apple*), gradual patient (*read a letter*), affected patient (*touch a
cat*), and stimulus (*see a horse*). -/
inductive ThematicClass
  | gradualEffectedPatient
  | gradualConsumedPatient
  | gradualPatient
  | affectedPatient
  | stimulus
  deriving DecidableEq, Repr

/-- The gradual classes. -/
def ThematicClass.Gradual : ThematicClass → Prop
  | .gradualEffectedPatient | .gradualConsumedPatient | .gradualPatient => True
  | .affectedPatient | .stimulus => False

/-- The classes with uniqueness of events. -/
def ThematicClass.UniqueEvents : ThematicClass → Prop
  | .gradualEffectedPatient | .gradualConsumedPatient => True
  | .gradualPatient | .affectedPatient | .stimulus => False

/-- What (14) requires of a relation in a class: summativity throughout, graduality for the
gradual classes, uniqueness of events for effected and consumed patients. -/
def ThematicClass.Requires (c : ThematicClass) (θ : O → E → Prop) : Prop :=
  CumTheta θ ∧ (c.Gradual → GRAD θ) ∧ (c.UniqueEvents → GUE θ)

/-- Effected and consumed patients make a quantized object into a quantized verbal
predicate (T 12): *write a letter* and *eat an apple* are telic. -/
theorem qua_of_uniqueEvents {c : ThematicClass} (hc : c.UniqueEvents) (h : c.Requires θ)
    (hδ : QUA δ) : QUA (ofTheta α δ θ) := by
  have hg : GRAD θ := h.2.1 (by cases c <;> trivial)
  exact qua_ofTheta_of_gue hδ hg.1 hg.2.1 (h.2.2 hc)

/-- A gradual patient transfers cumulativity (T 7) and, with a strictly quantized object,
leaves every event a part outside the predicate (T 13), the atomicity behind *read a
letter in an hour* even where the letter may be reread. -/
theorem gradualPatient_transfer (h : ThematicClass.gradualPatient.Requires θ) :
    (CUM α → CUM δ → CUM (ofTheta α δ θ)) ∧
      (SQUA δ → ∀ e, ofTheta α δ θ e → ∃ e' ≤ e, ¬ ofTheta α δ θ e') :=
  ⟨λ hα hδ => cum_ofTheta hα hδ h.1,
    λ hδ => exists_le_not_ofTheta hδ (h.2.1 trivial).2.2 (h.2.1 trivial).1⟩

end Transfer

/-! ### Temporal adverbials (§5) -/

section Adverbials

variable {E T M : Type*} [SemilatticeSup T]

/-- A durative adverbial (15): the quantizing modifier on events through the measure of
the temporal trace (D 41); the result is quantized once that derived measure is
extensive. -/
theorem durative_qua [SemilatticeSup E] [AddCommMonoid M] [PartialOrder M] (P : E → Prop)
    (μ' : E → M) [ExtMeasure μ'] (n : M) : QUA (QMOD P μ' n) :=
  qmod_qua P n

/-- A time-span adverbial (16): the event lies within a convex time of the given measure. -/
def inSpan (P : E → Prop) (τ : E → T) (Conv : T → Prop) (μ : T → M) (n : M) : E → Prop :=
  λ e => P e ∧ ∃ t, Conv t ∧ μ t = n ∧ τ e ≤ t

/-- Time-span adverbials are upward entailing in their number (17): if every convex time of
one measure lies within a convex time of a larger measure, the adverbial with the larger
number holds of every event the smaller one holds of. -/
theorem inSpan_mono (P : E → Prop) (τ : E → T) (Conv : T → Prop) (μ : T → M) {n n' : M}
    (h : ∀ t, Conv t → μ t = n → ∃ t', Conv t' ∧ μ t' = n' ∧ t ≤ t') :
    ∀ e, inSpan P τ Conv μ n e → inSpan P τ Conv μ n' e := by
  rintro e ⟨hp, t, hc, hμ, hle⟩
  obtain ⟨t', hc', hμ', htt'⟩ := h t hc hμ
  exact ⟨hp, t', hc', hμ', hle.trans htt'⟩

end Adverbials

end Krifka1989
