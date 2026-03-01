import Linglib.Core.Logic.Quantification
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Polarized Individuals and the Birkhoff Representation @cite{elliott-2025}

Entity–polarity pairs, trivalent functions, and the Birkhoff
representation theorem for conservative GQs.

## Overview

Elliott (2025) argues that determiners denote sets of **polarized
individuals** — entity–polarity pairs `(e, ±)` that encode whether an
entity witnesses the restrictor ∩ scope (positive) or the restrictor ∖
scope (negative). The conservative GQ lattice (`ConsGQ`, §12 of
`Core.Logic.Quantification`) is the algebraic setting.

The module is organized in five sections:

1. **Trivalent values** (`Tri`): three-valued type `{pos, neg, blank}`
   encoding an entity's status relative to a quantifier.

2. **Encoding/decoding** (`triFunction`, `triSupport`, `triPositive`):
   round-trip between `(R, S)` predicate pairs and trivalent functions
   `α → Tri`. This gives the concrete representation of the polarized
   domain D_e^± from Elliott §4.3.

3. **Birkhoff representation** (`consGQOrderIso`): the order-isomorphism
   `ConsGQ α ≃o ((α → Tri) → Bool)`, using mathlib's `Equiv.toOrderIso`.
   This is the concrete Birkhoff representation: conservative GQs are
   exactly predicates on trivalent functions. Conservativity is a
   structural consequence of the encoding — `predToGQ_conservative`
   shows any predicate on trivalent functions yields a conservative GQ.

4. **Entity–polarity pairs** (`PolInd α = α × Bool`): the compositionally
   useful type. A polarized individual `(e, p)` maps to the GQ
   `λ R S => R(e) ∧ (S(e) ↔ p)` via polarized functional application.
   Under the Birkhoff representation, each `PolInd` corresponds to an
   atomic predicate checking a single entity's polarity.

5. **Boolean algebra structure**: `ConsGQ α` is a Boolean algebra.

## References

- Elliott, P. (2025). Determiners as predicates. SALT 35.
- Birkhoff, G. (1937). Rings of sets.
- Van Benthem, J. (1984). Questions about Quantifiers.
-/

namespace Core.Quantification

-- ============================================================================
-- §1 — Trivalent Values
-- ============================================================================

/-- Trivalent value: the polarity of an entity relative to a quantifier.
    - `pos`: entity is in restrictor ∩ scope
    - `neg`: entity is in restrictor ∖ scope
    - `blank`: entity is irrelevant (not constrained by the quantifier)
    Elliott (2025), §4.3. -/
inductive Tri where
  | pos   : Tri
  | neg   : Tri
  | blank : Tri
  deriving DecidableEq, Repr, BEq

namespace Tri

/-- Check whether a trivalent value is non-blank (= in the restrictor). -/
def isNonBlank : Tri → Bool
  | .pos => true
  | .neg => true
  | .blank => false

/-- Check whether a trivalent value is positive (= in restrictor ∩ scope). -/
def isPos : Tri → Bool
  | .pos => true
  | .neg => false
  | .blank => false

@[simp] theorem isNonBlank_pos : Tri.pos.isNonBlank = true := rfl
@[simp] theorem isNonBlank_neg : Tri.neg.isNonBlank = true := rfl
@[simp] theorem isNonBlank_blank : Tri.blank.isNonBlank = false := rfl

@[simp] theorem isPos_pos : Tri.pos.isPos = true := rfl
@[simp] theorem isPos_neg : Tri.neg.isPos = false := rfl
@[simp] theorem isPos_blank : Tri.blank.isPos = false := rfl

end Tri

-- ============================================================================
-- §2 — Encoding / Decoding between (R, S) Pairs and Trivalent Functions
-- ============================================================================

variable {α : Type*}

/-- Encode a (restrictor, scope) pair as a trivalent function.
    pos = R ∩ S, neg = R ∖ S, blank = outside R. -/
def triFunction (R S : α → Bool) : α → Tri :=
  λ e => match R e, S e with
  | true, true   => .pos
  | true, false  => .neg
  | false, _     => .blank

/-- Decode the restrictor from a trivalent function. -/
def triSupport (f : α → Tri) : α → Bool :=
  λ e => (f e).isNonBlank

/-- Decode the positive part (R ∩ S) from a trivalent function. -/
def triPositive (f : α → Tri) : α → Bool :=
  λ e => (f e).isPos

-- ---- Round-trip lemmas ----

@[simp] theorem triSupport_triFunction (R S : α → Bool) :
    triSupport (triFunction R S) = R := by
  ext e; simp only [triSupport, triFunction]
  cases R e <;> cases S e <;> rfl

@[simp] theorem triPositive_triFunction (R S : α → Bool) :
    triPositive (triFunction R S) = (λ e => R e && S e) := by
  ext e; simp only [triPositive, triFunction]
  cases R e <;> cases S e <;> rfl

@[simp] theorem triFunction_decode (f : α → Tri) :
    triFunction (triSupport f) (triPositive f) = f := by
  ext e; show triFunction _ _ e = _
  unfold triFunction triSupport triPositive
  match f e with
  | .pos   => rfl
  | .neg   => rfl
  | .blank => rfl

-- ============================================================================
-- §3 — The Birkhoff Isomorphism: ConsGQ α ≃o ((α → Tri) → Bool)
-- ============================================================================

/-- Map a predicate on trivalent functions to a GQ.
    Elliott (2025), §4.3.2, equation (44). -/
def predToGQ (P : (α → Tri) → Bool) : GQ α :=
  λ R S => P (triFunction R S)

/-- Map a conservative GQ to a predicate on trivalent functions.
    Elliott (2025), §4.3.1, equation (40). -/
def gqToPred (Q : GQ α) : (α → Tri) → Bool :=
  λ f => Q (triSupport f) (triPositive f)

/-- **Conservativity for free**: any predicate on trivalent functions
    yields a conservative GQ. This is the central insight of Elliott (2025):
    conservativity is a structural consequence of the predicative theory,
    not an additional constraint. -/
private theorem triFunction_and_absorb (R S : α → Bool) :
    triFunction R (fun x => R x && S x) = triFunction R S := by
  ext e; simp only [triFunction]; cases R e <;> simp

theorem predToGQ_conservative (P : (α → Tri) → Bool) :
    Conservative (predToGQ P) := by
  intro R S; simp only [predToGQ, triFunction_and_absorb]

/-- Lift predToGQ into the conservative GQ sublattice. -/
def predToConsGQ (P : (α → Tri) → Bool) : ConsGQ α :=
  ⟨predToGQ P, predToGQ_conservative P⟩

/-- Round-trip: encoding then decoding is the identity. -/
theorem gqToPred_predToGQ (P : (α → Tri) → Bool) :
    gqToPred (predToGQ P) = P := by
  funext f; simp only [gqToPred, predToGQ, triFunction_decode]

/-- Round-trip: decoding then encoding a conservative GQ is the identity.
    Uses conservativity in the key step. -/
theorem predToConsGQ_gqToPred (Q : ConsGQ α) :
    predToConsGQ (gqToPred Q.1) = Q := by
  apply Subtype.ext; funext R S
  simp only [predToConsGQ, predToGQ, gqToPred,
    triSupport_triFunction, triPositive_triFunction]
  exact (Q.2 R S).symm

@[simp] theorem predToConsGQ_val (P : (α → Tri) → Bool) (R S : α → Bool) :
    (predToConsGQ P).1 R S = P (triFunction R S) := rfl

/-- **Birkhoff Representation for ConsGQ** (Elliott 2025, §4.3).

    Conservative GQs are order-isomorphic to predicates on trivalent
    functions (= the powerset of the polarized domain D_e^±).

    This is the concrete Birkhoff representation: the abstract version
    (`OrderIso.lowerSetSupIrred` in `Mathlib.Order.Birkhoff`) identifies
    any finite distributive lattice with the lattice of lower sets of its
    sup-irreducible elements. Our isomorphism makes this explicit for
    `ConsGQ` using `Equiv.toOrderIso` from mathlib.

    The isomorphism is constructive and works for any `α`, not just
    finite types. -/
def consGQOrderIso : ConsGQ α ≃o ((α → Tri) → Bool) :=
  Equiv.toOrderIso
    { toFun := λ Q => gqToPred Q.1
      invFun := λ P => predToConsGQ P
      left_inv := predToConsGQ_gqToPred
      right_inv := gqToPred_predToGQ }
    (fun {_ _} h f => h (triSupport f) (triPositive f))
    (fun {_ _} h R S => h (triFunction R S))

/-- For any GQ (not necessarily conservative), the Birkhoff round-trip
    replaces S with R ∩ S. Conservative GQs are exactly those for which
    this substitution is the identity. Non-conservative determiners
    cannot be expressed as predicates on trivalent functions.
    Elliott (2025), §4.3, eq. (43). -/
theorem predToGQ_gqToPred_eq (Q : GQ α) (R S : α → Bool) :
    predToGQ (gqToPred Q) R S = Q R (λ x => R x && S x) := by
  simp only [predToGQ, gqToPred, triSupport_triFunction, triPositive_triFunction]

-- ============================================================================
-- §4 — Entity–Polarity Pairs
-- ============================================================================

/-- Polarized individual: an entity paired with a polarity.
    `(e, true)` = *positive* (`e⁺`): entity witnesses restrictor ∩ scope.
    `(e, false)` = *negative* (`e⁻`): entity witnesses restrictor ∖ scope. -/
abbrev PolInd (α : Type*) := α × Bool

namespace PolInd

variable {α : Type*}

/-- GQ denotation via polarized functional application.
    `⟦(e, p)⟧(R, S) = R(e) ∧ (S(e) ↔ p)`.
    - `(e, true)`:  `R(e) ∧ S(e)`    — entity in restrictor ∩ scope
    - `(e, false)`: `R(e) ∧ ¬S(e)`   — entity in restrictor ∖ scope -/
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

-- ---- Connection to Birkhoff representation ----

/-- Under the Birkhoff representation, an entity-polarity pair
    corresponds to an atomic predicate: `(e, p)` maps to the predicate
    that checks whether `e` is in the restrictor and has matching
    polarity in the trivalent function. -/
theorem toGQ_eq_predToGQ (x : PolInd α) :
    toGQ x = predToGQ (λ f => (f x.1).isNonBlank && ((f x.1).isPos == x.2)) := by
  funext R S; simp only [toGQ, predToGQ, triFunction]
  cases R x.1 <;> cases S x.1 <;> cases x.2 <;> rfl

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
theorem toConsGQ_injective [DecidableEq α] :
    Function.Injective (toConsGQ (α := α)) := by
  intro x y h; exact (toConsGQ_le_iff x y).mp (le_of_eq h)

end PolInd

-- ============================================================================
-- §5 — Boolean Algebra Structure
-- ============================================================================

-- `ConsGQ α` is a Boolean algebra. The complement of a conservative
-- GQ is its pointwise Boolean negation, which is again conservative:
-- `(¬Q)(R, S) = ¬Q(R, S)` satisfies `(¬Q)(R, S) = (¬Q)(R, R∧S)`
-- because `Q(R, S) = Q(R, R∧S)`.
--
-- This extends the bounded distributive lattice from §12 of
-- `Quantification.lean` (via Sublattice) to a full `BooleanAlgebra`.
-- Elliott (2025), §4.3.

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
  le_top a := le_top
  bot_le a := bot_le
  sdiff_eq a b := rfl
  himp_eq a b := rfl

@[simp] theorem ConsGQ.compl_val (q : ConsGQ α) (R S : α → Bool) :
    qᶜ.1 R S = !q.1 R S := rfl

end ConsGQ_BA

end Core.Quantification
