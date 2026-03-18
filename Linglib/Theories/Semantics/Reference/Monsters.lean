import Linglib.Core.Semantics.Intension
import Linglib.Theories.Semantics.Reference.Kaplan

/-!
# Kaplan's Anti-Monster Thesis (Tower Formulation)
@cite{anand-nevins-2004} @cite{kaplan-1989} @cite{schlenker-2003}

@cite{kaplan-1989} "Demonstratives" VIII: the claim that natural language
operators are *content operators* (shifting circumstances of evaluation)
rather than *context operators* (shifting contexts of utterance).

Under the tower analysis, a monster is a non-identity context shift:
an embedding operator that pushes a shift where.apply c != c for some c.
Kaplan's thesis for English says attitude verbs push identity shifts —
they embed without changing the context of utterance.

Cross-linguistic counterexamples
are languages where attitude verbs push non-identity shifts (e.g.,
`attitudeShift` changes the agent to the attitude holder).

## Key Definitions

- `IsTowerMonster`: a shift where apply c != c for some c
- `kaplansThesisAsTower`: English embedding verbs push identity shifts
- `sayM`: Schlenker's monster operator, rewritten via tower push + fold
- Bridge: old `IsMonster` concept <-> `IsTowerMonster`

-/

namespace Semantics.Reference.Monsters

open Core.Context
open Core (Intension)
open Core.Intension (IsRigid)

-- ════════════════════════════════════════════════════════════════
-- § Tower Monster
-- ════════════════════════════════════════════════════════════════

/-- A context shift is a tower monster iff it is non-identity: there exists
    some context c where applying the shift produces a different context.

    Under the tower analysis, monsters are exactly the non-identity shifts.
    English attitude verbs push identity shifts (not monsters); Amharic
    attitude verbs push attitude shifts (monsters). -/
def IsTowerMonster {C : Type*} (σ : ContextShift C) : Prop :=
  ∃ (c : C), σ.apply c ≠ c

/-- The identity shift is not a monster. -/
theorem identityShift_not_monster {W : Type*} {E : Type*} {P : Type*} {T : Type*} :
    ¬ IsTowerMonster (identityShift (W := W) (E := E) (P := P) (T := T)) := by
  intro ⟨c, h⟩
  exact h (identityShift_apply c)

/-- An attitude shift is a monster when the holder differs from some
    context's agent. -/
theorem attitudeShift_is_monster {W : Type*} {E : Type*} {P : Type*} {T : Type*}
    (holder : E) (attWorld : W) (c : KContext W E P T)
    (hAgent : c.agent ≠ holder) :
    IsTowerMonster (attitudeShift (P := P) (T := T) holder attWorld) := by
  refine ⟨c, λ h => ?_⟩
  have : (attitudeShift (P := P) (T := T) holder attWorld).apply c = c := h
  have hagent : ((attitudeShift (P := P) (T := T) holder attWorld).apply c).agent = c.agent :=
    congrArg KContext.agent this
  simp only [attitudeShift] at hagent
  exact hAgent hagent.symm

-- ════════════════════════════════════════════════════════════════
-- § Kaplan's Thesis (Tower Formulation)
-- ════════════════════════════════════════════════════════════════

/-- Kaplan's thesis as a tower property: embedding verbs in a language push
    shifts that are not monsters (i.e., identity shifts).

    For English, this means all attitude verbs push `identityShift`:
    "John said that I am happy" evaluates "I" at the original context,
    because the embedding verb didn't shift anything.

    The `embeddingShifts` parameter lists the shifts that the language's
    embedding verbs produce. The thesis holds iff none of them is a monster. -/
def KaplansThesisHolds {C : Type*} (embeddingShifts : List (ContextShift C)) : Prop :=
  ∀ σ ∈ embeddingShifts, ¬ IsTowerMonster σ

/-- English embedding verbs push identity shifts. Kaplan's thesis holds. -/
theorem kaplansThesisAsTower {W : Type*} {E : Type*} {P : Type*} {T : Type*} :
    KaplansThesisHolds
      [identityShift (W := W) (E := E) (P := P) (T := T)] := by
  intro σ hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rw [hMem]
  exact identityShift_not_monster

-- ════════════════════════════════════════════════════════════════
-- § Schlenker's Say_m (Tower Formulation)
-- ════════════════════════════════════════════════════════════════

/-- Schlenker's monstrous `Say_m`, rewritten via tower push.

    Standard analysis: "John says that phi" quantifies over worlds compatible
    with John's assertion. Schlenker's monster analysis: "John says that phi"
    pushes an attitude shift onto the tower, making the embedded clause
    see John as the agent.

    `sayMTower assert attHolder phi t w` pushes `attitudeShift attHolder w'`
    for each compatible world w', evaluating phi against the shifted tower. -/
def sayMTower {W E P T : Type*}
    (assert : E → W → W → Prop)
    (attHolder : E)
    (φ : ContextTower (KContext W E P T) → W → Prop)
    (t : ContextTower (KContext W E P T)) (w : W) : Prop :=
  ∀ w', assert attHolder w w' →
    φ (t.push (attitudeShift attHolder w')) w'

/-- `sayMTower` accesses shifted contexts: the embedded clause is evaluated
    with the attitude holder as agent at the compatible world. -/
theorem sayMTower_shifts_agent {W E P T : Type*}
    (assert : E → W → W → Prop)
    (attHolder : E) (w w' : W)
    (hCompat : assert attHolder w w')
    (φ : ContextTower (KContext W E P T) → W → Prop)
    (t : ContextTower (KContext W E P T))
    (h : sayMTower assert attHolder φ t w) :
    φ (t.push (attitudeShift attHolder w')) w' :=
  h w' hCompat

end Semantics.Reference.Monsters
