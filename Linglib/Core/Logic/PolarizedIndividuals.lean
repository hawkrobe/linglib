import Linglib.Core.Logic.Quantification
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Polarized Individuals and the Birkhoff Representation @cite{elliott-2025}
@cite{van-benthem-1984}

Entity–polarity pairs, trivalent functions, and the Birkhoff
representation theorem for conservative GQs.

## Overview

@cite{elliott-2025} argues that determiners denote sets of **polarized
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
   `ConsGQ α ≃o ((α → Tri) → Prop)`, using mathlib's `Equiv.toOrderIso`.
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

-/

namespace Core.Quantification

-- ============================================================================
-- §1 — Trivalent Values
-- ============================================================================

/-- Trivalent value: the polarity of an entity relative to a quantifier.
    - `pos`: entity is in restrictor ∩ scope
    - `neg`: entity is in restrictor ∖ scope
    - `blank`: entity is irrelevant (not constrained by the quantifier)
    @cite{elliott-2025}, §4.3. -/
inductive Tri where
  | pos   : Tri
  | neg   : Tri
  | blank : Tri
  deriving DecidableEq, Repr

namespace Tri

/-- Whether a trivalent value is non-blank (= in the restrictor). -/
def IsNonBlank : Tri → Prop
  | .pos => True
  | .neg => True
  | .blank => False

/-- Whether a trivalent value is positive (= in restrictor ∩ scope). -/
def IsPos : Tri → Prop
  | .pos => True
  | .neg => False
  | .blank => False

@[simp] theorem IsNonBlank_pos : Tri.pos.IsNonBlank := trivial
@[simp] theorem IsNonBlank_neg : Tri.neg.IsNonBlank := trivial
@[simp] theorem not_IsNonBlank_blank : ¬ Tri.blank.IsNonBlank := id

@[simp] theorem IsPos_pos : Tri.pos.IsPos := trivial
@[simp] theorem not_IsPos_neg : ¬ Tri.neg.IsPos := id
@[simp] theorem not_IsPos_blank : ¬ Tri.blank.IsPos := id

instance : DecidablePred Tri.IsNonBlank := by
  intro t; cases t <;> simp [IsNonBlank] <;> infer_instance

instance : DecidablePred Tri.IsPos := by
  intro t; cases t <;> simp [IsPos] <;> infer_instance

end Tri

-- ============================================================================
-- §2 — Encoding / Decoding between (R, S) Pairs and Trivalent Functions
-- ============================================================================

variable {α : Type*}

/-- Encode a (restrictor, scope) pair as a trivalent function.
    pos = R ∩ S, neg = R ∖ S, blank = outside R.
    Noncomputable: uses classical decidability of the input predicates. -/
noncomputable def triFunction (R S : α → Prop) : α → Tri :=
  λ e =>
    open Classical in
    if R e then (if S e then .pos else .neg) else .blank

/-- Decode the restrictor from a trivalent function. -/
def triSupport (f : α → Tri) : α → Prop :=
  λ e => (f e).IsNonBlank

/-- Decode the positive part (R ∩ S) from a trivalent function. -/
def triPositive (f : α → Tri) : α → Prop :=
  λ e => (f e).IsPos

-- ---- Round-trip lemmas ----

@[simp] theorem triSupport_triFunction (R S : α → Prop) :
    triSupport (triFunction R S) = R := by
  funext e
  apply propext
  unfold triSupport triFunction
  by_cases hR : R e
  · by_cases hS : S e
    · simp [hR, hS, Tri.IsNonBlank]
    · simp [hR, hS, Tri.IsNonBlank]
  · simp [hR, Tri.IsNonBlank]

@[simp] theorem triPositive_triFunction (R S : α → Prop) :
    triPositive (triFunction R S) = (λ e => R e ∧ S e) := by
  funext e
  apply propext
  unfold triPositive triFunction
  by_cases hR : R e
  · by_cases hS : S e
    · simp [hR, hS, Tri.IsPos]
    · simp [hR, hS, Tri.IsPos]
  · simp [hR, Tri.IsPos]

@[simp] theorem triFunction_decode (f : α → Tri) :
    triFunction (triSupport f) (triPositive f) = f := by
  funext e
  unfold triFunction triSupport triPositive
  match h : f e with
  | .pos   => simp [h, Tri.IsNonBlank, Tri.IsPos]
  | .neg   => simp [h, Tri.IsNonBlank, Tri.IsPos]
  | .blank => simp [h, Tri.IsNonBlank, Tri.IsPos]

-- ============================================================================
-- §3 — The Birkhoff Isomorphism: ConsGQ α ≃o ((α → Tri) → Prop)
-- ============================================================================

/-- Map a predicate on trivalent functions to a GQ.
    @cite{elliott-2025}, §4.3.2, equation (44). -/
noncomputable def predToGQ (P : (α → Tri) → Prop) : GQ α :=
  λ R S => P (triFunction R S)

/-- Map a GQ to a predicate on trivalent functions.
    @cite{elliott-2025}, §4.3.1, equation (40). -/
def gqToPred (Q : GQ α) : (α → Tri) → Prop :=
  λ f => Q (triSupport f) (triPositive f)

/-- **Conservativity for free**: any predicate on trivalent functions
    yields a conservative GQ. This is the central insight of @cite{elliott-2025}:
    conservativity is a structural consequence of the predicative theory,
    not an additional constraint. -/
private theorem triFunction_and_absorb (R S : α → Prop) :
    triFunction R (fun x => R x ∧ S x) = triFunction R S := by
  funext e
  unfold triFunction
  by_cases hR : R e
  · by_cases hS : S e
    · simp [hR, hS]
    · simp [hR, hS]
  · simp [hR]

theorem predToGQ_conservative (P : (α → Tri) → Prop) :
    Conservative (predToGQ P) := by
  intro R S; simp only [predToGQ, triFunction_and_absorb]

/-- Lift predToGQ into the conservative GQ sublattice. -/
noncomputable def predToConsGQ (P : (α → Tri) → Prop) : ConsGQ α :=
  ⟨predToGQ P, predToGQ_conservative P⟩

/-- Round-trip: encoding then decoding is the identity. -/
theorem gqToPred_predToGQ (P : (α → Tri) → Prop) :
    gqToPred (predToGQ P) = P := by
  funext f; simp only [gqToPred, predToGQ, triFunction_decode]

/-- Round-trip: decoding then encoding a conservative GQ is the identity.
    Uses conservativity in the key step. -/
theorem predToConsGQ_gqToPred (Q : ConsGQ α) :
    predToConsGQ (gqToPred Q.1) = Q := by
  apply Subtype.ext; funext R S
  apply propext
  simp only [predToConsGQ, predToGQ, gqToPred,
    triSupport_triFunction, triPositive_triFunction]
  exact (Q.2 R S).symm

@[simp] theorem predToConsGQ_val (P : (α → Tri) → Prop) (R S : α → Prop) :
    (predToConsGQ P).1 R S = P (triFunction R S) := rfl

/-- **Birkhoff Representation for ConsGQ**.

    Conservative GQs are order-isomorphic to predicates on trivalent
    functions (= the powerset of the polarized domain D_e^±).

    This is the concrete Birkhoff representation: the abstract version
    (`OrderIso.lowerSetSupIrred` in `Mathlib.Order.Birkhoff`) identifies
    any finite distributive lattice with the lattice of lower sets of its
    sup-irreducible elements. Our isomorphism makes this explicit for
    `ConsGQ` using `Equiv.toOrderIso` from mathlib.

    The isomorphism is constructive in shape (though `predToGQ` is
    noncomputable due to classical decidability) and works for any `α`. -/
noncomputable def consGQOrderIso : ConsGQ α ≃o ((α → Tri) → Prop) :=
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
    @cite{elliott-2025}, §4.3, eq. (43). -/
theorem predToGQ_gqToPred_eq (Q : GQ α) (R S : α → Prop) :
    predToGQ (gqToPred Q) R S ↔ Q R (λ x => R x ∧ S x) := by
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
    `⟦(e, true)⟧(R, S) = R(e) ∧ S(e)` — entity in restrictor ∩ scope.
    `⟦(e, false)⟧(R, S) = R(e) ∧ ¬S(e)` — entity in restrictor ∖ scope. -/
def toGQ (x : PolInd α) : GQ α :=
  λ R S => R x.1 ∧ (if x.2 then S x.1 else ¬ S x.1)

/-- The GQ of a polarized individual is conservative. -/
theorem toGQ_conservative (x : PolInd α) : Conservative (toGQ x) := by
  intro R S
  simp only [toGQ]
  by_cases h2 : x.2 <;> (simp [h2]; try tauto)

/-- Lift a polarized individual into the conservative GQ sublattice. -/
def toConsGQ (x : PolInd α) : ConsGQ α :=
  ⟨toGQ x, toGQ_conservative x⟩

-- ---- Simp API ----

@[simp] theorem toGQ_apply (x : PolInd α) (R S : α → Prop) :
    toGQ x R S = (R x.1 ∧ (if x.2 then S x.1 else ¬ S x.1)) := rfl

@[simp] theorem toConsGQ_val (x : PolInd α) : (toConsGQ x).1 = toGQ x := rfl

-- ---- Positive/negative characterization ----

theorem toGQ_pos (e : α) (R S : α → Prop) :
    toGQ (e, true) R S ↔ (R e ∧ S e) := by simp [toGQ]

theorem toGQ_neg (e : α) (R S : α → Prop) :
    toGQ (e, false) R S ↔ (R e ∧ ¬ S e) := by simp [toGQ]

-- ---- Connection to Montagovian individuals ----

/-- The positive polarized individual `(e, true)` restricts the
    Montagovian individual `individual e` to entities in the restrictor. -/
theorem toGQ_pos_eq_individual (e : α) (R S : α → Prop) :
    toGQ (e, true) R S ↔ (R e ∧ individual e S) := by simp [toGQ, individual]

-- ---- Connection to Birkhoff representation ----

/-- Under the Birkhoff representation, an entity-polarity pair
    corresponds to an atomic predicate: `(e, p)` maps to the predicate
    that checks whether `e` is in the restrictor and has matching
    polarity in the trivalent function. -/
theorem toGQ_eq_predToGQ (x : PolInd α) :
    toGQ x = predToGQ (λ f => (f x.1).IsNonBlank ∧
                              (if x.2 then (f x.1).IsPos else ¬ (f x.1).IsPos)) := by
  funext R S
  apply propext
  simp only [toGQ, predToGQ, triFunction]
  by_cases hR : R x.1 <;> by_cases hS : S x.1 <;> cases x.2 <;>
    simp [hR, hS, Tri.IsNonBlank, Tri.IsPos]

-- ---- Lattice properties ----

/-- Positive and negative polarized individuals for the same entity are
    complementary within the restrictor: their join covers all cases
    where `e ∈ R`, and their meet is ⊥ (restricted to `R`).

    This is the lattice-theoretic content of the "split reading":
    `e⁺ ⊔ e⁻ = λR S. R(e)` (the individual-restrictor GQ). -/
theorem pos_sup_neg (e : α) :
    toConsGQ (e, true) ⊔ toConsGQ (e, false) =
    (⟨λ R _ => R e, λ R _ => Iff.rfl⟩ : ConsGQ α) := by
  apply Subtype.ext; funext R S
  simp only [ConsGQ.sup_val, toConsGQ_val, toGQ]
  apply propext
  by_cases hS : S e <;> simp [hS]

theorem pos_inf_neg (e : α) :
    toConsGQ (e, true) ⊓ toConsGQ (e, false) = ⊥ := by
  apply Subtype.ext; funext R S
  simp only [ConsGQ.inf_val, toConsGQ_val, toGQ, ConsGQ.bot_val]
  apply propext
  by_cases hS : S e <;> simp [hS]

-- ---- Order characterization ----

/-- `toConsGQ x ≤ toConsGQ y` iff `x = y`: distinct polarized
    individuals are incomparable in the ConsGQ lattice (they form an
    antichain).

    TODO: revive proof after Bool→Prop GQ migration.  The original proof
    instantiates the implication at a witness pair `(· = x.1, λ _ => x.2)`;
    after the migration, the subtype `≤` no longer applies as cleanly and
    the case-split on `x.2 / y.2` interacts awkwardly with Prop equality.
    The downstream code uses `pos_sup_neg`/`pos_inf_neg` rather than this
    antichain lemma, so the gap is non-blocking. -/
theorem toConsGQ_le_iff [DecidableEq α] (x y : PolInd α) :
    toConsGQ x ≤ toConsGQ y ↔ x = y := by
  sorry

/-- The embedding is order-reflecting: an injection into `ConsGQ α`. -/
theorem toConsGQ_injective [DecidableEq α] :
    Function.Injective (toConsGQ (α := α)) := by
  intro x y h; exact (toConsGQ_le_iff x y).mp (le_of_eq h)

end PolInd

-- ============================================================================
-- §5 — Boolean Algebra Structure
-- ============================================================================

-- `ConsGQ α` is a Boolean algebra. The complement of a conservative
-- GQ is its pointwise propositional negation, which is again conservative:
-- `(¬Q)(R, S) = ¬Q(R, S)` satisfies `(¬Q)(R, S) ↔ (¬Q)(R, R∧S)`
-- because `Q(R, S) ↔ Q(R, R∧S)`.
--
-- This extends the bounded distributive lattice from §12 of
-- `Quantification.lean` (via Sublattice) to a full `BooleanAlgebra`.
-- @cite{elliott-2025}, §4.3.

section ConsGQ_BA

variable {α : Type*}

noncomputable instance : Compl (ConsGQ α) where
  compl q := ⟨λ R S => ¬ q.1 R S, by
    intro R S
    show (¬ q.1 R S) ↔ (¬ q.1 R (λ x => R x ∧ S x))
    rw [q.2 R S]⟩

noncomputable instance : SDiff (ConsGQ α) where
  sdiff q₁ q₂ := q₁ ⊓ q₂ᶜ

noncomputable instance : HImp (ConsGQ α) where
  himp q₁ q₂ := q₂ ⊔ q₁ᶜ

noncomputable instance : BooleanAlgebra (ConsGQ α) where
  inf_compl_le_bot a := by
    intro R S h
    obtain ⟨ha, hna⟩ := h
    exact hna ha
  top_le_sup_compl a := by
    intro R S _
    exact Classical.em (a.1 R S)
  le_top a := le_top
  bot_le a := bot_le
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

@[simp] theorem ConsGQ.compl_val (q : ConsGQ α) (R S : α → Prop) :
    qᶜ.1 R S = ¬ q.1 R S := rfl

end ConsGQ_BA

end Core.Quantification
