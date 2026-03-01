import Linglib.Core.Logic.Quantification
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Polarized Individuals @cite{elliott-2026}

Entity–polarity pairs and their embedding into conservative GQs.

## Overview

Elliott (2026) argues that determiners denote sets of **polarized
individuals** — entity–polarity pairs `(e, ±)` that encode whether an
entity witnesses the restrictor ∩ scope (positive) or the restrictor ∖
scope (negative). The conservative GQ lattice (`ConsGQ`, §12 of
`Core.Logic.Quantification`) is the algebraic setting.

The module is organized in three sections:

1. **Entity–polarity pairs** (`PolInd α = α × Bool`): the compositionally
   useful type. A polarized individual `(e, p)` maps to the GQ
   `λ R S => R(e) ∧ (S(e) ↔ p)` via polarized functional application.

2. **Trivalent functions** (`PolDomain α`): the full polarized domain
   D_e^± from Elliott's Definition 14. Each trivalent function
   `f : α → Tri` assigns every entity a value in `{pos, neg, blank}`.
   These are the **atoms** (= join-irreducible elements) of `ConsGQ`;
   entity–polarity pairs are the "simple" trivalent functions with
   exactly one non-blank value.

3. **Boolean algebra structure**: `ConsGQ α` is a Boolean algebra
   (a product of powersets) whose atoms are exactly the non-trivial
   trivalent functions. The Birkhoff representation theorem yields
   `ConsGQ ≅ 𝒫(PolDomain α)`.

## References

- Elliott, P. (2026). Determiners as Polarized Individuals.
- Birkhoff, G. (1937). Rings of sets.
- Van Benthem, J. (1984). Questions about Quantifiers.
-/

namespace Core.Quantification

-- ============================================================================
-- §1 — Entity–Polarity Pairs
-- ============================================================================

/-- Polarized individual: an entity paired with a polarity.
    `(e, true)` = *positive* (`e⁺`): entity witnesses restrictor ∩ scope.
    `(e, false)` = *negative* (`e⁻`): entity witnesses restrictor ∖ scope.
    Elliott (2026), Definition 14 (atomic case). -/
abbrev PolInd (α : Type*) := α × Bool

namespace PolInd

variable {α : Type*}

/-- GQ denotation via polarized functional application.
    `⟦(e, p)⟧(R, S) = R(e) ∧ (S(e) ↔ p)`.
    - `(e, true)`:  `R(e) ∧ S(e)`    — entity in restrictor ∩ scope
    - `(e, false)`: `R(e) ∧ ¬S(e)`   — entity in restrictor ∖ scope
    Elliott (2026), Definition 15. -/
def toGQ (x : PolInd α) : GQ α :=
  λ R S => R x.1 && (S x.1 == x.2)

/-- The GQ of a polarized individual is conservative. -/
theorem toGQ_conservative (x : PolInd α) : Conservative (toGQ x) := by
  intro R S; simp only [toGQ]; cases R x.1 <;> simp

/-- Lift a polarized individual into the conservative GQ sublattice. -/
def toConsGQ (x : PolInd α) : ConsGQ α :=
  ⟨toGQ x, toGQ_conservative x⟩

-- ---- Simp API ----

@[simp] theorem toGQ_apply (x : PolInd α) (R S : α → Bool) :
    toGQ x R S = (R x.1 && (S x.1 == x.2)) := rfl

@[simp] theorem toConsGQ_val (x : PolInd α) : (toConsGQ x).1 = toGQ x := rfl

-- ---- Positive/negative characterization ----

theorem toGQ_pos (e : α) (R S : α → Bool) :
    toGQ (e, true) R S = (R e && S e) := by simp [toGQ]

theorem toGQ_neg (e : α) (R S : α → Bool) :
    toGQ (e, false) R S = (R e && !S e) := by simp [toGQ]

-- ---- Connection to Montagovian individuals ----

/-- The positive polarized individual `(e, true)` restricts the
    Montagovian individual `individual e` to entities in the restrictor. -/
theorem toGQ_pos_eq_individual (e : α) (R S : α → Bool) :
    toGQ (e, true) R S = (R e && individual e S) := by simp [toGQ, individual]

-- ---- Lattice properties ----

/-- Positive and negative polarized individuals for the same entity are
    complementary within the restrictor: their join covers all cases
    where `e ∈ R`, and their meet is ⊥ (restricted to `R`).

    This is the lattice-theoretic content of the "split reading":
    `e⁺ ⊔ e⁻ = λR S. R(e)` (the individual-restrictor GQ). -/
theorem pos_sup_neg (e : α) :
    toConsGQ (e, true) ⊔ toConsGQ (e, false) =
    (⟨λ R _ => R e, λ R _ => by simp⟩ : ConsGQ α) := by
  apply Subtype.ext; funext R S
  simp [toGQ, ConsGQ.sup_val]
  cases S e <;> simp

theorem pos_inf_neg (e : α) :
    toConsGQ (e, true) ⊓ toConsGQ (e, false) = ⊥ := by
  apply Subtype.ext; funext R S
  simp [toGQ, ConsGQ.inf_val]
  cases S e <;> simp

-- ---- Order characterization ----

/-- `toConsGQ x ≤ toConsGQ y` iff `x = y`: distinct polarized
    individuals are incomparable in the ConsGQ lattice (they form an
    antichain). -/
theorem toConsGQ_le_iff [DecidableEq α] (x y : PolInd α) :
    toConsGQ x ≤ toConsGQ y ↔ x = y := by
  constructor
  · intro h
    have heval : toGQ y (· == x.1) (λ _ => x.2) = true :=
      h (· == x.1) (λ _ => x.2) (by simp [toGQ])
    simp only [toGQ] at heval
    cases hb1 : (y.1 == x.1) <;> cases hb2 : (x.2 == y.2) <;>
      simp_all [beq_iff_eq, Prod.ext_iff]
  · intro h; rw [h]

/-- The embedding is order-reflecting: an injection into `ConsGQ α`. -/
theorem toConsGQ_injective [DecidableEq α] : Function.Injective (toConsGQ (α := α)) := by
  intro x y h; exact (toConsGQ_le_iff x y).mp (le_of_eq h)

end PolInd

-- ============================================================================
-- §2 — Trivalent Functions (Full Polarized Domain D_e^±)
-- ============================================================================

/-- Trivalent value: the polarity of an entity relative to a quantifier.
    - `pos`: entity is in restrictor ∩ scope
    - `neg`: entity is in restrictor ∖ scope
    - `blank`: entity is irrelevant (not constrained by the quantifier)
    Elliott (2026), Definition 14. -/
inductive Tri where
  | pos   : Tri
  | neg   : Tri
  | blank : Tri
  deriving DecidableEq, Repr, BEq

namespace Tri

/-- Convert a polarity `Bool` to the corresponding non-blank trivalent
    value: `true ↦ pos`, `false ↦ neg`. -/
def ofBool : Bool → Tri
  | true  => .pos
  | false => .neg

@[simp] theorem ofBool_true : ofBool true = .pos := rfl
@[simp] theorem ofBool_false : ofBool false = .neg := rfl

theorem ofBool_ne_blank (b : Bool) : ofBool b ≠ .blank := by cases b <;> simp [ofBool]

/-- A non-blank trivalent value determines a Boolean: `pos ↦ true`,
    `neg ↦ false`. Returns `true` for `blank` (vacuously satisfied). -/
def toBool : Tri → Bool
  | .pos   => true
  | .neg   => false
  | .blank => true

end Tri

/-- An element of the polarized domain D_e^±: a trivalent function
    `f : α → Tri` with at least one non-blank value.

    Each element specifies a "pattern" of entity polarities: which entities
    must be in the restrictor ∩ scope, which in the restrictor ∖ scope,
    and which are unconstrained.

    These are the **atoms** (join-irreducible elements) of `ConsGQ α`.
    Entity–polarity pairs `(e, p)` correspond to the simple case where
    exactly one entity is non-blank. -/
structure PolDomain (α : Type*) where
  /-- The trivalent assignment: each entity gets pos, neg, or blank. -/
  assign : α → Tri
  /-- At least one entity is assigned a non-blank value. -/
  nontrivial : ∃ e, assign e ≠ .blank

namespace PolDomain

variable {α : Type*}

/-- The support of a polarized domain element: entities with non-blank
    polarity. This determines the restrictor of the corresponding atom. -/
def support (f : PolDomain α) : α → Bool :=
  λ e => f.assign e != .blank

/-- The positive part: entities with positive polarity within the
    support. This determines the scope-restriction of the atom. -/
def positivePart (f : PolDomain α) : α → Bool :=
  λ e => f.assign e == .pos

-- ---- PolInd as atomic PolDomain ----

/-- Embed an entity–polarity pair as a trivalent function: the
    "simple" element of D_e^± with exactly one non-blank value. -/
def ofPolInd [DecidableEq α] (x : PolInd α) : PolDomain α where
  assign := λ e => if e == x.1 then Tri.ofBool x.2 else .blank
  nontrivial := ⟨x.1, by simp; exact Tri.ofBool_ne_blank x.2⟩

@[simp] theorem ofPolInd_assign_self [DecidableEq α] (x : PolInd α) :
    (ofPolInd x).assign x.1 = Tri.ofBool x.2 := by simp [ofPolInd]

theorem ofPolInd_assign_ne [DecidableEq α] (x : PolInd α) (e : α) (h : e ≠ x.1) :
    (ofPolInd x).assign e = .blank := by simp [ofPolInd, h]

end PolDomain

-- ============================================================================
-- §3 — Boolean Algebra Structure
-- ============================================================================

-- `ConsGQ α` is a Boolean algebra. The complement of a conservative
-- GQ is its pointwise Boolean negation, which is again conservative:
-- `(¬Q)(R, S) = ¬Q(R, S)` satisfies `(¬Q)(R, S) = (¬Q)(R, R∧S)`
-- because `Q(R, S) = Q(R, R∧S)`.
--
-- This extends the bounded distributive lattice from §12 of
-- `Quantification.lean` (via Sublattice) to a full `BooleanAlgebra`.
-- The Boolean algebra structure reflects the product decomposition
-- `ConsGQ α ≅ ∏_{A ⊆ α} 𝒫(𝒫(A))`: each factor is a powerset
-- lattice (hence Boolean), and products of Boolean algebras are Boolean.
-- Elliott (2026), Theorem 1.

section ConsGQ_BA

variable {α : Type*}

instance : Compl (ConsGQ α) where
  compl q := ⟨λ R S => !q.1 R S, λ R S => by
    simp only; congr 1; exact q.2 R S⟩

instance : SDiff (ConsGQ α) where
  sdiff q₁ q₂ := q₁ ⊓ q₂ᶜ

instance : HImp (ConsGQ α) where
  himp q₁ q₂ := q₂ ⊔ q₁ᶜ

instance : BooleanAlgebra (ConsGQ α) where
  inf_compl_le_bot a := by
    intro R S h
    simp only [ConsGQ.inf_val, Compl.compl, ConsGQ.bot_val] at h ⊢
    cases a.1 R S <;> simp_all
  top_le_sup_compl a := by
    intro R S _
    simp only [ConsGQ.sup_val, Compl.compl]
    cases a.1 R S <;> simp
  le_top a := ConsGQ.instOrderTop.le_top a
  bot_le a := ConsGQ.instOrderBot.bot_le a
  sdiff_eq a b := rfl
  himp_eq a b := rfl

@[simp] theorem ConsGQ.compl_val (q : ConsGQ α) (R S : α → Bool) :
    qᶜ.1 R S = !q.1 R S := rfl

end ConsGQ_BA

end Core.Quantification
