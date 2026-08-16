import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Linglib.Core.Order.AntiAdditive

/-!
# Finite-world test fixture for entailment

Thin shim over `Set` / `compl` / `∩` / `∪` from mathlib, specialized to a
4-element `World` enum. Consumers across the natural-logic and polarity layers use
the `World` type + a handful of test propositions to write `by decide`
test cases for monotonicity, polarity, and presupposition machinery.

The general (polymorphic) monotonicity theorems live in
`Linglib.Semantics.Quantification.Quantifier` (`every_scope_up`,
`some_scope_up`, `no_scope_down`, `every_restrictor_down`). This file
provides only the finite-world fixture.

Reference: [van-benthem-1986], [ladusaw-1980],
[barwise-cooper-1981].
-/

namespace Entailment

/-- A small finite set of worlds for decidable reasoning. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr

def allWorlds : List World := [.w0, .w1, .w2, .w3]

instance : Fintype World where
  elems := {.w0, .w1, .w2, .w3}
  complete := fun w => by cases w <;> decide

/-- Semantic entailment: thin alias for `Set` inclusion (`p ⊆ q`). -/
def entails : Set World → Set World → Prop := (· ⊆ ·)

instance (p q : Set World) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    Decidable (entails p q) :=
  Fintype.decidableForallFintype

/-- Negation: thin alias for set complement. -/
def pnot : Set World → Set World := compl

/-- Conjunction: thin alias for set intersection. -/
def pand : Set World → Set World → Set World := (· ∩ ·)

/-- Disjunction: thin alias for set union. -/
def por : Set World → Set World → Set World := (· ∪ ·)

instance (p : Set World) [DecidablePred (· ∈ p)] : DecidablePred (· ∈ pnot p) :=
  fun w => inferInstanceAs (Decidable (¬ w ∈ p))

instance (p q : Set World) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    DecidablePred (· ∈ pand p q) :=
  fun w => inferInstanceAs (Decidable (w ∈ p ∧ w ∈ q))

instance (p q : Set World) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    DecidablePred (· ∈ por p q) :=
  fun w => inferInstanceAs (Decidable (w ∈ p ∨ w ∈ q))

/-- Proposition true only in w0. -/
def p0 : Set World := {.w0}

/-- Proposition true in w0 and w1. -/
def p01 : Set World := {.w0, .w1}

/-- Proposition true in w0, w1, w2. -/
def p012 : Set World := {.w0, .w1, .w2}

/-- Proposition true everywhere. -/
def pAll : Set World := Set.univ

/-- Proposition false everywhere. -/
def pNone : Set World := ∅

instance : DecidablePred (· ∈ p0) := fun w => by unfold p0; infer_instance
instance : DecidablePred (· ∈ p01) := fun w => by unfold p01; infer_instance
instance : DecidablePred (· ∈ p012) := fun w => by unfold p012; infer_instance
instance : DecidablePred (· ∈ pAll) := fun _ => isTrue trivial
instance : DecidablePred (· ∈ pNone) := fun _ => isFalse not_false

theorem p0_entails_p01 : entails p0 p01 := by decide
theorem p01_entails_p012 : entails p01 p012 := by decide

/-! ### Toy-`World` witnesses -/

section ToyWitnesses

/-- Negation is anti-additive. -/
theorem pnot_isAntiAdditive : IsAntiAdditive pnot := fun p q => by
  show (p ∪ q)ᶜ = pᶜ ∩ qᶜ
  exact Set.compl_union p q

/-- Negation is anti-multiplicative. -/
theorem pnot_isAntiMultiplicative : IsAntiMultiplicative pnot := fun p q => by
  show (p ∩ q)ᶜ = pᶜ ∪ qᶜ
  exact Set.compl_inter p q

/-- Negation is anti-morphic. -/
theorem pnot_isAntiMorphic : IsAntiMorphic pnot :=
  ⟨pnot_isAntiAdditive, pnot_isAntiMultiplicative⟩

/-- Negation is antitone (downward entailing). -/
theorem pnot_antitone : Antitone pnot :=
  pnot_isAntiAdditive.antitone

/-- "No A is B" = ∀x. A(x) → ¬B(x). -/
def no' (restr : Set World) (scope : Set World) : Set World :=
  λ _ => ∀ x ∈ allWorlds, ¬ (restr x ∧ scope x)

/-- "No student ___" with fixed restrictor. -/
def no_student : Set World → Set World := no' p01

/-- "No" is anti-additive in scope. -/
theorem no_isAntiAdditive_scope : IsAntiAdditive no_student := by
  refine isAntiAdditive_iff_mem.mpr (fun p q _w => ?_)
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

/-- "No" is antitone in scope. -/
theorem no_antitone_scope : Antitone no_student :=
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

/-- "At most n" is antitone in scope. -/
theorem atMost_antitone_scope : Antitone atMost2_student := by
  intro p q hpq _w h
  exact atMost_mono 2 p01 p q (fun _ hp => hpq hp) h

/-- "At most 1 student ___" with fixed restrictor. -/
def atMost1_student : Set World → Set World :=
  λ scope => λ _ => atMost 1 p01 scope

/-- "At most 1" is still antitone. -/
theorem atMost1_antitone_scope : Antitone atMost1_student := by
  intro p q hpq _w h
  exact atMost_mono 1 p01 p q (fun _ hp => hpq hp) h

/-- "At most n" is not anti-additive (counterexample): the strictness
witness for DE ⊊ anti-additive. -/
theorem atMost_not_antiAdditive :
    ¬IsAntiAdditive atMost1_student := by
  intro hAA
  have h := isAntiAdditive_iff_mem.mp hAA
  let qProp : Set World := λ w => w = .w1
  have key : atMost1_student (por p0 qProp) .w0 ↔
             atMost1_student p0 .w0 ∧ atMost1_student qProp .w0 :=
    h p0 qProp World.w0
  -- p0 has just w0 as a witness; ≤ 1 ✓
  have hp : atMost1_student p0 .w0 := by
    intro ws hnd hall
    -- Every element of ws satisfies p01 ∧ p0, hence equals w0
    have hall_w0 : ∀ w ∈ ws, w = .w0 := by
      intro w hw
      have := (hall w hw).2
      exact this
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

end ToyWitnesses

end Entailment
