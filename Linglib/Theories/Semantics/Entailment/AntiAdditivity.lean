/-
The DE < Anti-Additive < Anti-Morphic hierarchy.
Reference: @cite{chierchia-2013} section 1.4.3, @cite{ladusaw-1980}.
-/

import Mathlib.Order.Monotone.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Logic.NaturalLogic
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.Polarity

namespace Semantics.Entailment.AntiAdditivity

open Core.NaturalLogic (DEStrength UEStrength strengthSufficient)
open Core.Proposition (Prop')
open Semantics.Entailment
open Semantics.Entailment.Polarity
open List (Sublist)


section Definitions

/-- Anti-additive: forall A B, f(A | B) = f(A) & f(B). -/
def IsAntiAdditive (f : Prop' World → Prop' World) : Prop :=
  ∀ p q : Prop' World, ∀ w, f (por p q) w ↔ f p w ∧ f q w

/--
Anti-morphic (AM): Anti-additive + distributes ∧ to ∨ in both directions.
-/
def IsAntiMorphic (f : Prop' World → Prop' World) : Prop :=
  IsAntiAdditive f ∧
  (∀ p q : Prop' World, ∀ w, f (pand p q) w ↔ f p w ∨ f q w)


/-- Anti-additive implies DE. -/
theorem antiAdditive_implies_de (f : Prop' World → Prop' World) (hAA : IsAntiAdditive f) :
    IsDownwardEntailing f := by
  intro p q hpq w hfq
  have hpor_eq : por p q = q := by
    funext w'
    simp only [por, Core.Proposition.Classical.por, eq_iff_iff]
    exact ⟨fun h => h.elim (hpq w') id, Or.inr⟩
  have := (hAA p q w).mp (by rw [hpor_eq]; exact hfq)
  exact this.1

/-- Anti-morphic implies anti-additive. -/
theorem antiMorphic_implies_antiAdditive (f : Prop' World → Prop' World) (hAM : IsAntiMorphic f) :
    IsAntiAdditive f :=
  hAM.1

/-- Anti-morphic implies DE. -/
theorem antiMorphic_implies_de (f : Prop' World → Prop' World) (hAM : IsAntiMorphic f) :
    IsDownwardEntailing f :=
  antiAdditive_implies_de f (antiMorphic_implies_antiAdditive f hAM)


/-- Negation is anti-additive. -/
theorem pnot_isAntiAdditive : IsAntiAdditive pnot := by
  intro p q w
  simp only [pnot, por, Core.Proposition.Classical.pnot, Core.Proposition.Classical.por,
             not_or]

/-- Negation satisfies the conjunction-to-disjunction property. -/
theorem pnot_distributes_and :
    ∀ p q : Prop' World, ∀ w, pnot (pand p q) w ↔ pnot p w ∨ pnot q w := by
  intro p q w
  simp only [pnot, pand, Core.Proposition.Classical.pnot, Core.Proposition.Classical.pand,
             not_and_or]

/-- Negation is anti-morphic. -/
theorem pnot_isAntiMorphic : IsAntiMorphic pnot :=
  ⟨pnot_isAntiAdditive, pnot_distributes_and⟩


/-- "No A is B" = ∀x. A(x) → ¬B(x). -/
def no' (restr : Prop' World) (scope : Prop' World) : Prop' World :=
  λ _ => ∀ x ∈ allWorlds, ¬ (restr x ∧ scope x)

/-- "No student ___" with fixed restrictor. -/
def no_student : Prop' World → Prop' World := no' p01

/-- "No" is anti-additive in scope. -/
theorem no_isAntiAdditive_scope : IsAntiAdditive no_student := by
  intro p q _w
  simp only [no_student, no', por, Core.Proposition.Classical.por, not_and, not_or]
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> intro x hx hr
    · exact (h x hx hr).1
    · exact (h x hx hr).2
  · rintro ⟨h1, h2⟩ x hx hr
    exact ⟨h1 x hx hr, h2 x hx hr⟩

/-- "No" is DE in scope. -/
theorem no_isDE_scope : IsDE no_student :=
  antiAdditive_implies_de no_student no_isAntiAdditive_scope


/-- "At most n A's are B" - true if at most n worlds satisfy both.
    Uses an existential over a sublist witness so the def is decidable
    only when the predicates are decidable, but stays in `Prop`. -/
def atMost (n : Nat) (restr scope : Prop' World) : Prop :=
  ∀ ws : List World, ws.Nodup →
    (∀ w ∈ ws, restr w ∧ scope w) →
    ws.length ≤ n

/-- Monotonicity: if `p ⊆ q` (entailment) and `q` has at most `n` witnesses,
    so does `p`. -/
theorem atMost_mono (n : Nat) (restr p q : Prop' World)
    (hpq : ∀ w, p w → q w) (h : atMost n restr q) :
    atMost n restr p := by
  intro ws hnd hall
  apply h ws hnd
  intro w hw
  exact ⟨(hall w hw).1, hpq w (hall w hw).2⟩

/-- "At most 2 students ___" with fixed restrictor. -/
def atMost2_student : Prop' World → Prop' World :=
  λ scope => λ _ => atMost 2 p01 scope

/-- "At most n" is DE in scope. -/
theorem atMost_isDE_scope : IsDE atMost2_student := by
  intro p q hpq _w h
  exact atMost_mono 2 p01 p q (fun w => hpq w) h

/-- "At most 1 student ___" with fixed restrictor. -/
def atMost1_student : Prop' World → Prop' World :=
  λ scope => λ _ => atMost 1 p01 scope

/-- "At most 1" is still DE. -/
theorem atMost1_isDE_scope : IsDE atMost1_student := by
  intro p q hpq _w h
  exact atMost_mono 1 p01 p q (fun w => hpq w) h

/-- "At most n" is not anti-additive (counterexample). -/
theorem atMost_not_antiAdditive :
    ¬IsAntiAdditive atMost1_student := by
  intro h
  let qProp : Prop' World := λ w => w = .w1
  have key : atMost1_student (por p0 qProp) .w0 ↔
             atMost1_student p0 .w0 ∧ atMost1_student qProp .w0 := h _ _ _
  -- p0 has just w0 as a witness; ≤ 1 ✓
  have hp : atMost1_student p0 .w0 := by
    intro ws hnd hall
    -- Every element of ws satisfies p01 ∧ p0, hence equals w0
    have hall_w0 : ∀ w ∈ ws, w = .w0 := by
      intro w hw
      have := (hall w hw).2
      simpa [p0] using this
    -- A nodup list whose every element is w0 has length ≤ 1
    rcases ws with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = .w0 := hall_w0 a (List.mem_cons_self ..)
        have hb : b = .w0 := hall_w0 b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have : a ≠ b := List.ne_of_not_mem_cons (List.Nodup.notMem hnd)
        exact this (ha.trans hb.symm)
  -- qProp has just w1 as a witness; ≤ 1 ✓
  have hq : atMost1_student qProp .w0 := by
    intro ws hnd hall
    have hall_w1 : ∀ w ∈ ws, w = .w1 := by
      intro w hw
      have := (hall w hw).2
      simpa [qProp] using this
    rcases ws with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = .w1 := hall_w1 a (List.mem_cons_self ..)
        have hb : b = .w1 := hall_w1 b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have : a ≠ b := List.ne_of_not_mem_cons (List.Nodup.notMem hnd)
        exact this (ha.trans hb.symm)
  -- por p0 qProp has both w0 and w1 as witnesses; not ≤ 1
  have hcontr : ¬ atMost1_student (por p0 qProp) .w0 := by
    intro hle
    have : ([World.w0, World.w1]).length ≤ 1 := by
      apply hle [.w0, .w1]
      · decide
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact ⟨Or.inl rfl, by left; rfl⟩
        · rcases List.mem_singleton.mp hw' with rfl
          exact ⟨Or.inr rfl, by right; rfl⟩
    simp at this
  exact hcontr (key.mpr ⟨hp, hq⟩)



/-- Weak NPI licensing: requires DE. -/
def licensesWeakNPI (f : Prop' World → Prop' World) : Prop := IsDownwardEntailing f

/-- Strong NPI licensing: requires Anti-Additive. -/
def licensesStrongNPI (f : Prop' World → Prop' World) : Prop := IsAntiAdditive f

example : licensesWeakNPI pnot := pnot_isDownwardEntailing
example : licensesStrongNPI pnot := pnot_isAntiAdditive

example : licensesWeakNPI no_student := no_isDE_scope
example : licensesStrongNPI no_student := no_isAntiAdditive_scope

example : licensesWeakNPI atMost2_student := atMost_isDE_scope


/-!
## `DEStrength` ↔ Proof Hierarchy
@cite{icard-2012}

| `DEStrength` | Proof Predicate | Example Licensor |
|--------------|-----------------|------------------|
| `.weak` | `IsDE` | few, at most n |
| `.antiAdditive` | `IsAntiAdditive` | no, nobody, without |
| `.antiMorphic` | `IsAntiMorphic` | not, never |
-/

end Definitions


-- ============================================================================
-- Section: Upward Entailing Duals (@cite{icard-2012})
-- ============================================================================

section UEDuals

/-- Additive: f(A ∨ B) = f(A) ∨ f(B) and f(⊤) = ⊤. -/
def IsAdditive (f : Prop' World → Prop' World) : Prop :=
  (∀ p q : Prop' World, ∀ w, f (por p q) w ↔ f p w ∨ f q w) ∧
  (∀ w, f pAll w)

/-- Multiplicative: f(A ∧ B) = f(A) ∧ f(B) and f(⊥) = ⊥. -/
def IsMultiplicative (f : Prop' World → Prop' World) : Prop :=
  (∀ p q : Prop' World, ∀ w, f (pand p q) w ↔ f p w ∧ f q w) ∧
  (∀ w, ¬ f pNone w)

/-- Anti-multiplicative: f(A ∧ B) = f(A) ∨ f(B) and f(⊥) = ⊤. -/
def IsAntiMultiplicative (f : Prop' World → Prop' World) : Prop :=
  (∀ p q : Prop' World, ∀ w, f (pand p q) w ↔ f p w ∨ f q w) ∧
  (∀ w, f pNone w)

/-- Additive implies UE. -/
theorem additive_implies_ue (f : Prop' World → Prop' World) (hAdd : IsAdditive f) :
    IsUpwardEntailing f := by
  intro p q hpq w hfp
  have hpor_eq : por p q = q := by
    funext w'
    simp only [por, Core.Proposition.Classical.por, eq_iff_iff]
    exact ⟨fun h => h.elim (hpq w') id, Or.inr⟩
  have := (hAdd.1 p q w).mpr (Or.inl hfp)
  rw [hpor_eq] at this
  exact this

/-- Multiplicative implies UE. -/
theorem multiplicative_implies_ue (f : Prop' World → Prop' World) (hMult : IsMultiplicative f) :
    IsUpwardEntailing f := by
  intro p q hpq w hfp
  have hpand_eq : pand p q = p := by
    funext w'
    simp only [pand, Core.Proposition.Classical.pand, eq_iff_iff]
    exact ⟨And.left, fun h => ⟨h, hpq w' h⟩⟩
  have hfpand : f (pand p q) w := by rw [hpand_eq]; exact hfp
  exact ((hMult.1 p q w).mp hfpand).2

/-- Anti-multiplicative implies DE. -/
theorem antiMultiplicative_implies_de (f : Prop' World → Prop' World) (hAM : IsAntiMultiplicative f) :
    IsDownwardEntailing f := by
  intro p q hpq w hfq
  have hpand_eq : pand p q = p := by
    funext w'
    simp only [pand, Core.Proposition.Classical.pand, eq_iff_iff]
    exact ⟨And.left, fun h => ⟨h, hpq w' h⟩⟩
  have h := (hAM.1 p q w).mpr (Or.inr hfq)
  rw [hpand_eq] at h
  exact h

end UEDuals

end Semantics.Entailment.AntiAdditivity
