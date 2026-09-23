module

public import Linglib.Logic.Natural.Soundness
public import Linglib.Logic.Natural.Strawson.Basic

/-!
# Strawson-relativized soundness

This file relativizes the soundness layer of
`Logic/Natural/Soundness.lean` to presuppositions ([von-fintel-1999]'s
Strawson move, at signature level): a projection row holds modulo
presuppositions when the projected relation holds on the region where
the arguments' presuppositions are satisfied.

## Main declarations

* `Relation.HoldsOn`: the lattice content of a relation, relativized
  to a region; at `⊤` it is `Relation.Holds`.
* `Signature.StrawsonSoundFor`: `Signature.SoundFor` with every
  projected relation read on the symmetric definedness region
  `defined x ⊓ defined y` of [gajewski-2011]'s Strawson
  anti-additivity.
* `strawsonSoundFor_top_iff`, `Signature.SoundFor.strawsonSoundFor`:
  classical soundness is the trivial-definedness case, and implies the
  Strawson form at any definedness.
* `strawsonSoundFor_anti_of_isStrawsonDE` and the operator instances:
  `only`, `regret`, `superlative`, and `since` realize the `.anti` row
  Strawson-ly while failing it classically.

## Implementation notes

The operator instances are the semantic content of the
`classicalSignature = none` rows of
`Polarity.LicensingContext.properties`. Composing definedness along a
path is presupposition projection and is deliberately not attempted
here; its home is a bridge to `Semantics/Presupposition/`.

## References

* [von-fintel-1999] — the Strawson move.
* [gajewski-2011] — the symmetric definedness gate.
-/

@[expose] public section

namespace NaturalLogic

open Presupposition

/-- The lattice content of a relation, relativized to a region `D` (the
worlds where the relevant presuppositions are satisfied). At `D = ⊤` this
is `Relation.Holds` (`holdsOn_top`). -/
def Relation.HoldsOn {β : Type*} [Lattice β] [BoundedOrder β] (D : β) :
    Relation → β → β → Prop
  | .equiv => fun u v => u ⊓ D = v ⊓ D
  | .forward => fun u v => u ⊓ D ≤ v
  | .reverse => fun u v => v ⊓ D ≤ u
  | .negation => fun u v => u ⊓ v ⊓ D = ⊥ ∧ D ≤ u ⊔ v
  | .alternation => fun u v => u ⊓ v ⊓ D = ⊥
  | .cover => fun u v => D ≤ u ⊔ v
  | .independent => fun _ _ => True

section HoldsOn

variable {β : Type*} [Lattice β] [BoundedOrder β]

/-- At trivial definedness, relativized content is plain content. -/
@[simp]
theorem Relation.holdsOn_top {R : Relation} {u v : β} :
    R.HoldsOn ⊤ u v ↔ R.Holds u v := by
  cases R <;>
    simp only [Relation.HoldsOn, Relation.Holds, inf_top_eq, top_le_iff,
      disjoint_iff, codisjoint_iff, isCompl_iff]

/-- Plain content implies relativized content on any region. -/
theorem Relation.Holds.holdsOn {R : Relation} {u v : β} (D : β)
    (h : R.Holds u v) : R.HoldsOn D u v := by
  cases R with
  | equiv => subst h; rfl
  | forward => exact le_trans inf_le_left h
  | reverse => exact le_trans inf_le_left h
  | negation =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, le_top.trans_eq (codisjoint_iff.mp h2).symm⟩
      show u ⊓ v ⊓ D = ⊥
      rw [disjoint_iff.mp h1, bot_inf_eq]
  | alternation =>
      show u ⊓ v ⊓ D = ⊥
      rw [disjoint_iff.mp h, bot_inf_eq]
  | cover => exact le_top.trans_eq (codisjoint_iff.mp h).symm
  | independent => trivial

end HoldsOn

section StrawsonSoundFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- σ's row is **Strawson-sound** for `f` relative to `defined`: every
projected relation holds on the region where both arguments'
presuppositions are satisfied — the symmetric gate of [gajewski-2011]'s
`IsStrawsonAntiAdditive`. -/
def Signature.StrawsonSoundFor (σ : Signature) (f : α → β)
    (defined : α → β) : Prop :=
  ∀ (R : Relation) (x y : α), R.Holds x y →
    (Signature.project R σ).HoldsOn (defined x ⊓ defined y) (f x) (f y)

/-- Classical soundness implies Strawson soundness at any definedness. -/
theorem Signature.SoundFor.strawsonSoundFor {σ : Signature}
    {f : α → β} (h : σ.SoundFor f) (defined : α → β) :
    σ.StrawsonSoundFor f defined :=
  fun R x y hR => (h R x y hR).holdsOn _

/-- Strawson soundness at trivial definedness is classical soundness. -/
theorem strawsonSoundFor_top_iff {σ : Signature} {f : α → β} :
    σ.StrawsonSoundFor f (fun _ => ⊤) ↔ σ.SoundFor f := by
  constructor
  · intro h R x y hR
    simpa only [inf_top_eq, Relation.holdsOn_top] using h R x y hR
  · intro h
    exact h.strawsonSoundFor _

end StrawsonSoundFor

/-! ### The Strawson-DE operators, at signature level -/

section SetInstances

variable {α W : Type*} [Lattice α] [BoundedOrder α]

/-- [von-fintel-1999]'s Strawson-DE, at signature level: a Strawson-DE operator's total meaning
realizes the `.anti` row relative to its presupposition. -/
theorem strawsonSoundFor_anti_of_isStrawsonDE {f : α → PartialProp W} (h : IsStrawsonDE f) :
    Signature.StrawsonSoundFor .anti (λ p => (f p).truthSet) (λ p => {w | (f p).presup w}) := by
  intro R x y hR
  cases R with
  | equiv => subst hR; rfl
  | forward => rintro w ⟨hfy, hdx, _⟩; exact ⟨hdx, h hR w hfy.1 hdx hfy.2⟩
  | reverse => rintro w ⟨hfx, _, hdy⟩; exact ⟨hdy, h hR w hfx.1 hdy hfx.2⟩
  | negation | alternation | cover | independent => trivial

/-- *Only* realizes the `.anti` row Strawson-ly while failing it classically
(`only_not_antitone`). -/
theorem only_strawsonSoundFor_anti {ι : Type*} (x : ι) :
    Signature.StrawsonSoundFor .anti (λ P : ι → Set W => (only x P).truthSet)
      (λ P => {w | (only x P).presup w}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (only_isStrawsonDE x)

/-- Adversatives (*sorry*, *regret*, *surprised*) realize the `.anti` row Strawson-ly while
failing it classically (`regret_not_antitone`). -/
theorem regret_strawsonSoundFor_anti (dox best : W → Set W) :
    Signature.StrawsonSoundFor .anti (λ p => (regret dox best p).truthSet)
      (λ p => {w | (regret dox best p).presup w}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (regret_isStrawsonDE dox best)

/-- Superlatives realize the `.anti` row Strawson-ly in their restriction. -/
theorem superlative_strawsonSoundFor_anti {ι D : Type*} [Preorder D] (μ : ι → D) (a : ι) :
    Signature.StrawsonSoundFor .anti (λ Q : ι → Set W => (superlative μ Q a).truthSet)
      (λ Q => {w | (superlative μ Q a).presup w}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (superlative_isStrawsonDE μ a)

/-- Temporal *since* realizes the `.anti` row Strawson-ly. -/
theorem since_strawsonSoundFor_anti (past window : W → Set W) :
    Signature.StrawsonSoundFor .anti (λ p => (since past window p).truthSet)
      (λ p => {w | (since past window p).presup w}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (since_isStrawsonDE past window)

end SetInstances

end NaturalLogic
