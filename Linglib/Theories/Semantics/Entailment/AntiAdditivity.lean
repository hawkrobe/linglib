/-
The DE < Anti-Additive < Anti-Morphic hierarchy.
Reference: @cite{chierchia-2013} section 1.4.3, @cite{ladusaw-1980}.
-/

import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.Heyting.Hom
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Logic.NaturalLogic
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.Polarity

namespace Semantics.Entailment.AntiAdditivity

open Core.NaturalLogic (DEStrength UEStrength strengthSufficient)
open Semantics.Entailment
open Semantics.Entailment.Polarity
open List (Sublist)


section Definitions

variable {α β : Type*}

/-- Anti-additive: `f(A ∪ B) = f(A) ∩ f(B)` (pointwise iff form).

Polymorphic in domain and codomain — this is needed e.g. for
@cite{hoeksema-1983}'s S-comparative, which is anti-additive as a
function `Set Degree → Set Individual`. -/
def IsAntiAdditive (f : Set α → Set β) : Prop :=
  ∀ p q : Set α, ∀ x, f (p ∪ q) x ↔ f p x ∧ f q x

/-- Anti-morphic (AM): Anti-additive + distributes ∩ to ∪. -/
def IsAntiMorphic (f : Set α → Set β) : Prop :=
  IsAntiAdditive f ∧
  (∀ p q : Set α, ∀ x, f (p ∩ q) x ↔ f p x ∨ f q x)


/-- Anti-additive implies antitone. The codomain need not be `Set World`. -/
theorem IsAntiAdditive.antitone {f : Set α → Set β} (hAA : IsAntiAdditive f) :
    Antitone f := by
  intro p q hpq x hfq
  have hu : p ∪ q = q := Set.union_eq_right.mpr hpq
  have := (hAA p q x).mp (by rw [hu]; exact hfq)
  exact this.1

/-- Anti-morphic implies anti-additive. -/
theorem IsAntiMorphic.antiAdditive {f : Set α → Set β} (hAM : IsAntiMorphic f) :
    IsAntiAdditive f := hAM.1

/-- Anti-morphic implies antitone. -/
theorem IsAntiMorphic.antitone {f : Set α → Set β} (hAM : IsAntiMorphic f) :
    Antitone f := hAM.antiAdditive.antitone


/-- Any function of the form `fun X y => ∀ x ∈ X, P x y` is anti-additive in `X`.

    `npComparative` and `sComparative` (@cite{hoeksema-1983}) instantiate this
    with `P x y := μ x < μ y` and `P d y := d < μ y` respectively. -/
theorem isAntiAdditive_forall_mem (P : α → β → Prop) :
    IsAntiAdditive (fun (X : Set α) (y : β) => ∀ x ∈ X, P x y) := by
  intro A B y
  refine ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩, ?_⟩
  rintro ⟨hA, hB⟩ x (hx | hx)
  · exact hA x hx
  · exact hB x hx

/-- Negation is anti-additive. -/
theorem pnot_isAntiAdditive : IsAntiAdditive pnot := by
  intro p q w
  show (p ∪ q)ᶜ w ↔ pᶜ w ∧ qᶜ w
  rw [Set.compl_union]; rfl

/-- Negation satisfies the conjunction-to-disjunction property. -/
theorem pnot_distributes_and :
    ∀ p q : Set World, ∀ w, pnot (pand p q) w ↔ pnot p w ∨ pnot q w := by
  intro p q w
  show (p ∩ q)ᶜ w ↔ pᶜ w ∨ qᶜ w
  rw [Set.compl_inter]; rfl

/-- Negation is anti-morphic. -/
theorem pnot_isAntiMorphic : IsAntiMorphic pnot :=
  ⟨pnot_isAntiAdditive, pnot_distributes_and⟩


/-- "No A is B" = ∀x. A(x) → ¬B(x). -/
def no' (restr : Set World) (scope : Set World) : Set World :=
  λ _ => ∀ x ∈ allWorlds, ¬ (restr x ∧ scope x)

/-- "No student ___" with fixed restrictor. -/
def no_student : Set World → Set World := no' p01

/-- "No" is anti-additive in scope. -/
theorem no_isAntiAdditive_scope : IsAntiAdditive no_student := by
  intro p q _w
  show (∀ x ∈ allWorlds, ¬ (p01 x ∧ (p ∪ q) x)) ↔
       (∀ x ∈ allWorlds, ¬ (p01 x ∧ p x)) ∧
       (∀ x ∈ allWorlds, ¬ (p01 x ∧ q x))
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> intro x hx ⟨hr, hpx⟩
    · exact h x hx ⟨hr, Or.inl hpx⟩
    · exact h x hx ⟨hr, Or.inr hpx⟩
  · rintro ⟨h1, h2⟩ x hx ⟨hr, hor⟩
    cases hor with
    | inl hp => exact h1 x hx ⟨hr, hp⟩
    | inr hq => exact h2 x hx ⟨hr, hq⟩

/-- "No" is DE in scope. -/
theorem no_isDE_scope : IsDE no_student :=
  no_isAntiAdditive_scope.antitone


/-- "At most n A's are B" - true if at most n worlds satisfy both.
    Uses an existential over a sublist witness so the def is decidable
    only when the predicates are decidable, but stays in `Prop`. -/
def atMost (n : Nat) (restr scope : Set World) : Prop :=
  ∀ ws : List World, ws.Nodup →
    (∀ w ∈ ws, restr w ∧ scope w) →
    ws.length ≤ n

/-- Monotonicity: if `p ⊆ q` (entailment) and `q` has at most `n` witnesses,
    so does `p`. -/
theorem atMost_mono (n : Nat) (restr p q : Set World)
    (hpq : ∀ w, p w → q w) (h : atMost n restr q) :
    atMost n restr p := by
  intro ws hnd hall
  apply h ws hnd
  intro w hw
  exact ⟨(hall w hw).1, hpq w (hall w hw).2⟩

/-- "At most 2 students ___" with fixed restrictor. -/
def atMost2_student : Set World → Set World :=
  λ scope => λ _ => atMost 2 p01 scope

/-- "At most n" is DE in scope. -/
theorem atMost_isDE_scope : IsDE atMost2_student := by
  intro p q hpq _w h
  exact atMost_mono 2 p01 p q (fun _ hp => hpq hp) h

/-- "At most 1 student ___" with fixed restrictor. -/
def atMost1_student : Set World → Set World :=
  λ scope => λ _ => atMost 1 p01 scope

/-- "At most 1" is still DE. -/
theorem atMost1_isDE_scope : IsDE atMost1_student := by
  intro p q hpq _w h
  exact atMost_mono 1 p01 p q (fun _ hp => hpq hp) h

/-- "At most n" is not anti-additive (counterexample). -/
theorem atMost_not_antiAdditive :
    ¬IsAntiAdditive atMost1_student := by
  intro h
  let qProp : Set World := λ w => w = .w1
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
def licensesWeakNPI (f : Set World → Set World) : Prop := IsDownwardEntailing f

/-- Strong NPI licensing: requires Anti-Additive. -/
def licensesStrongNPI (f : Set World → Set World) : Prop := IsAntiAdditive f

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

variable {α β : Type*}

/-- Additive: `f(A ∪ B) = f(A) ∪ f(B)` and `f(⊤) = ⊤`. -/
def IsAdditive (f : Set α → Set β) : Prop :=
  (∀ p q : Set α, ∀ x, f (p ∪ q) x ↔ f p x ∨ f q x) ∧
  (∀ x, f Set.univ x)

/-- Multiplicative: `f(A ∩ B) = f(A) ∩ f(B)` and `f(⊥) = ⊥`. -/
def IsMultiplicative (f : Set α → Set β) : Prop :=
  (∀ p q : Set α, ∀ x, f (p ∩ q) x ↔ f p x ∧ f q x) ∧
  (∀ x, ¬ f ∅ x)

/-- Anti-multiplicative: `f(A ∩ B) = f(A) ∪ f(B)` and `f(⊥) = ⊤`. -/
def IsAntiMultiplicative (f : Set α → Set β) : Prop :=
  (∀ p q : Set α, ∀ x, f (p ∩ q) x ↔ f p x ∨ f q x) ∧
  (∀ x, f ∅ x)

/-- Additive implies monotone. -/
theorem IsAdditive.monotone {f : Set α → Set β} (hAdd : IsAdditive f) :
    Monotone f := by
  intro p q hpq x hfp
  have hu : p ∪ q = q := Set.union_eq_right.mpr hpq
  have h := (hAdd.1 p q x).mpr (Or.inl hfp)
  rw [hu] at h
  exact h

/-- Multiplicative implies monotone. -/
theorem IsMultiplicative.monotone {f : Set α → Set β} (hMult : IsMultiplicative f) :
    Monotone f := by
  intro p q hpq x hfp
  have hi : p ∩ q = p := Set.inter_eq_left.mpr hpq
  have hfpand : f (p ∩ q) x := by rw [hi]; exact hfp
  exact ((hMult.1 p q x).mp hfpand).2

/-- Anti-multiplicative implies antitone. -/
theorem IsAntiMultiplicative.antitone {f : Set α → Set β} (hAM : IsAntiMultiplicative f) :
    Antitone f := by
  intro p q hpq x hfq
  have hi : p ∩ q = p := Set.inter_eq_left.mpr hpq
  have h := (hAM.1 p q x).mpr (Or.inr hfq)
  rw [hi] at h
  exact h

end UEDuals


-- ============================================================================
-- Section: Boolean Homomorphism (@cite{hoeksema-1983})
-- ============================================================================

section BooleanHomomorphism

/-- A function `f : Set α → Set β` is a Boolean homomorphism iff it underlies
a `BoundedLatticeHom (Set α) (Set β)`. Since `Set _` is a `BooleanAlgebra`,
mathlib's `BoundedLatticeHomClass.toBiheytingHomClass` instance derives
`map_compl` for free — so preservation of `∩` / `∪` / `ᶜ` / `⊤` / `⊥` are
all available via the standard `map_inf` / `map_sup` / `map_compl` /
`map_top` / `map_bot` simp lemmas on the underlying bundled hom.

This is the property @cite{hoeksema-1983} attributes to the NP-comparative
`⟦Adj-er than⟧ : Set (Set U) → Set U` (Eq 22), from which Hoeksema derives
both monotonicity (Fact 3) and uniqueness (Facts 1–2).

For consumers, the recommended API is to construct a `BoundedLatticeHom` and
use mathlib's `map_inf`/`map_sup`/`map_compl` directly; this `Prop`-valued
predicate exists as a documentation hook anchoring the @cite{hoeksema-1983}
terminology to the mathlib infrastructure. -/
def IsBooleanHomomorphism {α β : Type*} (f : Set α → Set β) : Prop :=
  ∃ g : BoundedLatticeHom (Set α) (Set β), ⇑g = f

end BooleanHomomorphism

end Semantics.Entailment.AntiAdditivity
