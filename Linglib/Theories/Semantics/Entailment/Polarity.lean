/-
# Grounded Context Polarity

Semantic grounding for `ContextPolarity` (defined in `Core.NaturalLogic`)
via Mathlib's `Monotone`/`Antitone` infrastructure.

## Contents

1. Re-export of `ContextPolarity` from `Core.NaturalLogic`
2. IsUpwardEntailing/IsDownwardEntailing - Mathlib-based formal definitions
3. Decidable test functions - For verification on finite models
4. GroundedPolarity - Context + polarity + proof
5. Monotonicity theorems - Negation, conditionals, quantifiers

## Integration with Mathlib

We use Mathlib's order-theoretic infrastructure:
- `Monotone f` (from `Mathlib.Order.Monotone.Basic`): `∀ a b, a ≤ b → f a ≤ f b`
- `Antitone f`: `∀ a b, a ≤ b → f b ≤ f a`

For `Prop' World = World → Prop`, the ordering is pointwise: `p ≤ q ↔ ∀ w, p w → q w`.

Mathlib provides composition lemmas for free:
- `Monotone.comp`: UE ∘ UE = UE
- `Antitone.comp_antitone`: DE ∘ DE = UE (the "double negation" rule!)
- `Monotone.comp_antitone`: UE ∘ DE = DE
- `Antitone.comp`: DE ∘ UE = DE

The polarity composition rules are a homomorphic image of the
`EntailmentSig` monoid — see `EntailmentSig.toContextPolarity_compose`.

-/

import Mathlib.Order.Monotone.Defs
import Linglib.Core.Logic.NaturalLogic
import Linglib.Theories.Semantics.Entailment.Basic

namespace Semantics.Entailment.Polarity

export Core.NaturalLogic (ContextPolarity)

open Semantics.Entailment
open Core.Proposition (Prop')

/--
IsUpwardEntailing is an abbreviation for `Monotone`.

A context function `f : Prop' World → Prop' World` is upward entailing if
it preserves the ordering: If p ≤ q, then f(p) ≤ f(q).
-/
abbrev IsUpwardEntailing (f : Prop' World → Prop' World) := Monotone f

/--
IsDownwardEntailing is an abbreviation for `Antitone`.

A context function `f : Prop' World → Prop' World` is downward entailing if
it reverses the ordering: If p ≤ q, then f(q) ≤ f(p).
-/
abbrev IsDownwardEntailing (f : Prop' World → Prop' World) := Antitone f

abbrev IsUE := IsUpwardEntailing
abbrev IsDE := IsDownwardEntailing


/-- Identity is UE. -/
theorem id_isUpwardEntailing : IsUpwardEntailing (id : Prop' World → Prop' World) :=
  monotone_id

/-- Negation is DE. -/
theorem pnot_isDownwardEntailing : IsDownwardEntailing pnot := by
  intro p q hpq w hnq hp
  exact hnq (hpq w hp)

/-- Double negation is UE. -/
theorem pnot_pnot_isUpwardEntailing : IsUpwardEntailing (pnot ∘ pnot) :=
  pnot_isDownwardEntailing.comp pnot_isDownwardEntailing


/-- UE ∘ UE = UE -/
theorem ue_comp_ue {f g : Prop' World → Prop' World}
    (hf : IsUpwardEntailing f) (hg : IsUpwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- DE ∘ DE = UE (double negation). -/
theorem de_comp_de {f g : Prop' World → Prop' World}
    (hf : IsDownwardEntailing f) (hg : IsDownwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- UE ∘ DE = DE -/
theorem ue_comp_de {f g : Prop' World → Prop' World}
    (hf : IsUpwardEntailing f) (hg : IsDownwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_antitone hg

/-- DE ∘ UE = DE -/
theorem de_comp_ue {f g : Prop' World → Prop' World}
    (hf : IsDownwardEntailing f) (hg : IsUpwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_monotone hg


/-- Check if f is upward entailing on given test cases (decidable approximation). -/
def isUpwardEntailing (f : Prop' World → Prop' World)
    [∀ p : Prop' World, [DecidablePred p] → DecidablePred (f p)]
    (tests : List (Prop' World × Prop' World)) : Prop :=
  ∀ pq ∈ tests, ∀ _ : DecidablePred pq.1, ∀ _ : DecidablePred pq.2,
    entails pq.1 pq.2 → entails (f pq.1) (f pq.2)

/-- Check if f is downward entailing on given test cases (decidable approximation). -/
def isDownwardEntailing (f : Prop' World → Prop' World)
    [∀ p : Prop' World, [DecidablePred p] → DecidablePred (f p)]
    (tests : List (Prop' World × Prop' World)) : Prop :=
  ∀ pq ∈ tests, ∀ _ : DecidablePred pq.1, ∀ _ : DecidablePred pq.2,
    entails pq.1 pq.2 → entails (f pq.2) (f pq.1)


/-- Negation reverses entailment. -/
theorem negation_reverses_example :
    entails p0 p01 ∧ entails (pnot p01) (pnot p0) := by
  refine ⟨p0_entails_p01, ?_⟩
  exact pnot_isDownwardEntailing p0_entails_p01

/-- DE contexts reverse scalar strength. -/
theorem de_reverses_strength :
    entails p0 p01 ∧ entails (pnot p01) (pnot p0) :=
  negation_reverses_example


/-- Material conditional with fixed consequent: "If _, then c" -/
def materialCond (c : Prop' World) : Prop' World → Prop' World :=
  λ p => λ w => p w → c w

/-- Conditional antecedent is DE. -/
theorem materialCond_antecedent_DE (c : Prop' World) :
    IsDownwardEntailing (materialCond c) := by
  intro p q hpq w hpc hp
  exact hpc (hpq w hp)

/-- Conditional consequent is UE. -/
theorem materialCond_consequent_UE (a : Prop' World) :
    IsUpwardEntailing (λ c => materialCond c a) := by
  intro p q hpq w hap ha
  exact hpq w (hap ha)


/-- A grounded UE polarity carries proof that a context function is monotone. -/
structure GroundedUE where
  context : Prop' World → Prop' World
  witness : Monotone context

/-- A grounded DE polarity carries proof that a context function is antitone. -/
structure GroundedDE where
  context : Prop' World → Prop' World
  witness : Antitone context

/-- A grounded polarity is either UE or DE, with proof. -/
inductive GroundedPolarity where
  | ue : GroundedUE → GroundedPolarity
  | de : GroundedDE → GroundedPolarity

/-- Extract the ContextPolarity enum from a grounded polarity. -/
def GroundedPolarity.toContextPolarity : GroundedPolarity → ContextPolarity
  | .ue _ => .upward
  | .de _ => .downward

def mkUpward (ctx : Prop' World → Prop' World) (h : Monotone ctx) : GroundedPolarity :=
  .ue ⟨ctx, h⟩

def mkDownward (ctx : Prop' World → Prop' World) (h : Antitone ctx) : GroundedPolarity :=
  .de ⟨ctx, h⟩

/-- The identity context is grounded UE. -/
def identityPolarity : GroundedPolarity := mkUpward id id_isUpwardEntailing

/-- Negation is grounded DE. -/
def negationPolarity : GroundedPolarity := mkDownward pnot pnot_isDownwardEntailing


/--
Compose two grounded polarities, with proof that the composition has the
right property.
-/
def composePolarity (outer inner : GroundedPolarity) : GroundedPolarity :=
  match outer, inner with
  | .ue ⟨f, hf⟩, .ue ⟨g, hg⟩ => .ue ⟨f ∘ g, ue_comp_ue hf hg⟩
  | .ue ⟨f, hf⟩, .de ⟨g, hg⟩ => .de ⟨f ∘ g, ue_comp_de hf hg⟩
  | .de ⟨f, hf⟩, .ue ⟨g, hg⟩ => .de ⟨f ∘ g, de_comp_ue hf hg⟩
  | .de ⟨f, hf⟩, .de ⟨g, hg⟩ => .ue ⟨f ∘ g, de_comp_de hf hg⟩

/-- Grounded polarity composition agrees with `ContextPolarity.compose`. -/
theorem composePolarity_agrees (outer inner : GroundedPolarity) :
    (composePolarity outer inner).toContextPolarity =
    outer.toContextPolarity.compose inner.toContextPolarity := by
  cases outer with
  | ue o => cases inner with
    | ue i => rfl
    | de i => rfl
  | de o => cases inner with
    | ue i => rfl
    | de i => rfl

/-- Double DE gives UE (grounded version). -/
theorem double_de_is_ue_grounded (f g : Prop' World → Prop' World)
    (hf : Antitone f) (hg : Antitone g) :
    (composePolarity (mkDownward f hf) (mkDownward g hg)).toContextPolarity = .upward := by
  rfl


/-- Scalar implicatures require UE context. -/
def implicatureAllowed (gp : GroundedPolarity) : Prop :=
  gp.toContextPolarity = .upward

/-- Implicature is allowed in identity context. -/
theorem implicature_allowed_identity : implicatureAllowed identityPolarity := by
  simp only [implicatureAllowed, identityPolarity, mkUpward, GroundedPolarity.toContextPolarity]

/-- Implicature is blocked under single negation. -/
theorem implicature_blocked_negation : ¬implicatureAllowed negationPolarity := by
  simp only [implicatureAllowed, negationPolarity, mkDownward, GroundedPolarity.toContextPolarity,
             reduceCtorEq, not_false_eq_true]

/-- Implicature is allowed under double negation. -/
theorem implicature_allowed_double_negation :
    implicatureAllowed (composePolarity negationPolarity negationPolarity) := by
  simp only [implicatureAllowed, composePolarity, negationPolarity, mkDownward,
             GroundedPolarity.toContextPolarity]

end Semantics.Entailment.Polarity
