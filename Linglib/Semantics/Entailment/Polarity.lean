import Mathlib.Order.Monotone.Defs
import Linglib.Semantics.Entailment.NaturalLogic
import Linglib.Semantics.Entailment.Basic

/-!
# Grounded context polarity

Semantic grounding for `ContextPolarity` (defined in `NaturalLogic`) via
mathlib's `Monotone`/`Antitone` infrastructure: `IsUpwardEntailing`/
`IsDownwardEntailing` abbreviate `Monotone`/`Antitone` on `Set α → Set β`,
so the composition rules (UE ∘ UE = UE, DE ∘ DE = UE, mixed = DE) are
`Monotone.comp`/`Antitone.comp` and friends. The polarity composition rules
are a homomorphic image of the `EntailmentSig` monoid — see
`EntailmentSig.toContextPolarity_compose`. `GroundedPolarity` bundles a
context function with its monotonicity proof on the toy `World` model.
-/

namespace Entailment

export NaturalLogic (ContextPolarity)

open Entailment

/-- A context function is upward entailing if it preserves entailment:
`Monotone` on sets of worlds. -/
abbrev IsUpwardEntailing {α β : Type*} (f : Set α → Set β) := Monotone f

/-- A context function is downward entailing if it reverses entailment:
`Antitone` on sets of worlds. -/
abbrev IsDownwardEntailing {α β : Type*} (f : Set α → Set β) := Antitone f

abbrev IsUE {α β : Type*} (f : Set α → Set β) := IsUpwardEntailing f
abbrev IsDE {α β : Type*} (f : Set α → Set β) := IsDownwardEntailing f


/-- Identity is UE. -/
theorem id_isUpwardEntailing : IsUpwardEntailing (id : Set World → Set World) :=
  monotone_id

/-- Negation is DE. -/
theorem pnot_isDownwardEntailing : IsDownwardEntailing pnot := by
  intro p q hpq
  exact Set.compl_subset_compl.mpr hpq

/-- Double negation is UE. -/
theorem pnot_pnot_isUpwardEntailing : IsUpwardEntailing (pnot ∘ pnot) :=
  pnot_isDownwardEntailing.comp pnot_isDownwardEntailing


/-- UE ∘ UE = UE -/
theorem ue_comp_ue {α β γ : Type*} {f : Set β → Set γ} {g : Set α → Set β}
    (hf : IsUpwardEntailing f) (hg : IsUpwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- DE ∘ DE = UE (double negation). -/
theorem de_comp_de {α β γ : Type*} {f : Set β → Set γ} {g : Set α → Set β}
    (hf : IsDownwardEntailing f) (hg : IsDownwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- UE ∘ DE = DE -/
theorem ue_comp_de {α β γ : Type*} {f : Set β → Set γ} {g : Set α → Set β}
    (hf : IsUpwardEntailing f) (hg : IsDownwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_antitone hg

/-- DE ∘ UE = DE -/
theorem de_comp_ue {α β γ : Type*} {f : Set β → Set γ} {g : Set α → Set β}
    (hf : IsDownwardEntailing f) (hg : IsUpwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_monotone hg


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
def materialCond (c : Set World) : Set World → Set World :=
  λ p => λ w => p w → c w

/-- Conditional antecedent is DE. -/
theorem materialCond_antecedent_DE (c : Set World) :
    IsDownwardEntailing (materialCond c) := by
  intro p q hpq w hpc hp
  exact hpc (hpq hp)

/-- Conditional consequent is UE. -/
theorem materialCond_consequent_UE (a : Set World) :
    IsUpwardEntailing (λ c => materialCond c a) := by
  intro p q hpq w hap ha
  exact hpq (hap ha)


/-- A grounded UE polarity carries proof that a context function is monotone. -/
structure GroundedUE where
  context : Set World → Set World
  witness : Monotone context

/-- A grounded DE polarity carries proof that a context function is antitone. -/
structure GroundedDE where
  context : Set World → Set World
  witness : Antitone context

/-- A grounded polarity is either UE or DE, with proof. -/
inductive GroundedPolarity where
  | ue : GroundedUE → GroundedPolarity
  | de : GroundedDE → GroundedPolarity

/-- Extract the ContextPolarity enum from a grounded polarity. -/
def GroundedPolarity.toContextPolarity : GroundedPolarity → ContextPolarity
  | .ue _ => .upward
  | .de _ => .downward

def mkUpward (ctx : Set World → Set World) (h : Monotone ctx) : GroundedPolarity :=
  .ue ⟨ctx, h⟩

def mkDownward (ctx : Set World → Set World) (h : Antitone ctx) : GroundedPolarity :=
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
theorem double_de_is_ue_grounded (f g : Set World → Set World)
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

end Entailment
