import Linglib.Core.Logic.Truth3
import Linglib.Core.Assignment

/-!
# The Transparency Principle
@cite{schlenker-2007} @cite{schlenker-2008a} @cite{spector-2025}

Schlenker's Transparency Principle states that a presupposition is felicitous
iff it is semantically redundant at its syntactic position. @cite{spector-2025}
applies this to anaphora: free variables presuppose they are *valued*, and
Transparency governs whether this presupposition projects.

## Core Idea

Given a sentence S containing a presuppositional element at some position,
form two sentences:
- **S1**: replace the element with `U(x) ∧ φ` (presupposition conjoined)
- **S2**: replace the element with `φ` alone

Transparency is satisfied iff S1 and S2 have the same truth value at
every world-assignment pair in the context, for every formula φ.

## Middle Kleene Connection

The Transparency proofs rely on Middle Kleene truth tables:
- Left-undefined absorbs (both ∧ and ∨)
- Left-defined uses Strong Kleene

This asymmetry is what makes `∃xT(x) ∧ P(x̲)` felicitous (Transparency
holds) while `P(x̲) ∧ ∃xT(x)` is infelicitous (Transparency fails).
-/

namespace Semantics.Presupposition.Transparency

open Core
open Core.Duality

universe u

-- ════════════════════════════════════════════════════════════════
-- Partial Assignments
-- ════════════════════════════════════════════════════════════════

/-- Partial assignment: variables may be undefined (`none`).

    In @cite{spector-2025}'s system, `g(x) = #` means variable `x`
    is not valued by assignment `g`. This is the source of
    undefinedness in the trivalent semantics. -/
abbrev PartialAssign (D : Type u) := Nat → Option D

namespace PartialAssign

variable {D : Type u}

/-- A partial assignment that values no variables. -/
def empty : PartialAssign D := λ _ => none

/-- Update a partial assignment at index `n`. -/
def update (g : PartialAssign D) (n : Nat) (d : D) : PartialAssign D :=
  λ m => if m = n then some d else g m

/-- Whether variable `n` is valued by `g`. -/
def valued (g : PartialAssign D) (n : Nat) : Bool :=
  (g n).isSome

/-- The `U(x)` predicate: `x` is valued.
    @cite{spector-2025} §2.2.2: `⟦U(x)⟧^{w,g} = 1` if `g(x) ≠ #`,
    `0` if `g(x) = #`. Bivalent (never undefined). -/
def isValued (g : PartialAssign D) (n : Nat) : Bool :=
  g.valued n

@[simp] theorem valued_update_at (g : PartialAssign D) (n : Nat) (d : D) :
    (g.update n d).valued n = true := by simp [update, valued]

@[simp] theorem valued_update_ne (g : PartialAssign D) {n m : Nat} (d : D)
    (h : m ≠ n) : (g.update n d).valued m = g.valued m := by
  simp [update, valued, h]

theorem valued_empty (n : Nat) : (empty (D := D)).valued n = false := rfl

end PartialAssign

-- ════════════════════════════════════════════════════════════════
-- Contexts and Transparency
-- ════════════════════════════════════════════════════════════════

variable {W : Type*} {D : Type u}

/-- A context is a set of world-assignment pairs.
    @cite{spector-2025} §2.2.1: "We view a context C as a set
    of world-assignment pairs (w,g)." -/
abbrev Ctx (W : Type*) (D : Type u) := W → PartialAssign D → Prop

/-- The null context: all world-assignment pairs.
    @cite{spector-2025} §2.2.1: "the null context which contains
    all possible world-assignment pairs." -/
def nullCtx : Ctx W D := λ _ _ => True

/-- Stalnakerian update: intersect context with sentence's truth set.
    @cite{spector-2025} §2.2.1: "if a sentence S is accepted as true
    in context C, then the resulting context is simply C intersected
    with the set of world-assignment pairs where S is true." -/
def stalnakerUpdate (C : Ctx W D) (S : W → PartialAssign D → Truth3) :
    Ctx W D :=
  λ w g => C w g ∧ S w g = .true

/-- Two trivalent sentences agree throughout a context. -/
def agreeIn (C : Ctx W D) (S1 S2 : W → PartialAssign D → Truth3) : Prop :=
  ∀ w g, C w g → S1 w g = S2 w g

/-- A trivalent sentence over world-assignment pairs. -/
abbrev Sent (W : Type*) (D : Type u) := W → PartialAssign D → Truth3

/-- A sentence frame: a sentence with a hole for a sub-sentence. -/
abbrev Frame (W : Type*) (D : Type u) := Sent W D → Sent W D

/-- The Transparency Principle (symmetric version).

    @cite{spector-2025} §2.2.2 / §6.3: For a sentence S containing
    a free (underlined) variable x, form S1 by replacing P(x̲) with
    `U(x) ∧ φ` and S2 by replacing P(x̲) with `φ`. Transparency is
    satisfied in context C iff S1 and S2 agree throughout C for every
    formula φ.

    We formalize this as: given a sentence-with-hole `frame` and a
    presupposition predicate `presup`, Transparency holds iff for every
    `φ`, `frame (meetMiddle presup φ)` and `frame φ` agree in C.

    The `frame` represents the sentence with a hole where the
    presuppositional element occurs. The presupposition (e.g., `U(x)`)
    is conjoined via Middle Kleene conjunction. -/
def transparent (C : Ctx W D) (frame : Frame W D)
    (presup : Sent W D) : Prop :=
  ∀ φ : Sent W D,
    agreeIn C (frame (λ w g => Truth3.meetMiddle (presup w g) (φ w g)))
              (frame φ)

/-- Transparency holds trivially when the presupposition is always true
    in the context (since `meetMiddle true v = v`). -/
theorem transparent_of_presup_true (C : Ctx W D) (frame : Frame W D)
    (presup : Sent W D)
    (hframe : ∀ (φ₁ φ₂ : Sent W D), (∀ w g, C w g → φ₁ w g = φ₂ w g) →
              ∀ w g, C w g → frame φ₁ w g = frame φ₂ w g)
    (hpresup : ∀ w g, C w g → presup w g = .true) :
    transparent C frame presup := by
  intro φ w g hC
  exact hframe _ _ (λ w' g' hC' => by simp [Truth3.meetMiddle_true_left, hpresup w' g' hC']) w g hC

/-- The Novelty Condition: an existential quantifier introducing
    variable x can only occur once in a discourse.

    @cite{spector-2025} §4 / @cite{heim-1982}: "If x is a variable,
    an occurrence of ∃x can only occur once in a whole discourse."
    This prevents ∃xP(x).∃xQ(x) from collapsing to ∃x(P(x) ∧ Q(x)). -/
def noveltyCondition (usedVars : List Nat) (newVar : Nat) : Prop :=
  newVar ∉ usedVars

end Semantics.Presupposition.Transparency
