import Linglib.Semantics.Entailment.Soundness
import Linglib.Semantics.Entailment.StrawsonEntailment

/-!
# Strawson-relativized soundness

[von-fintel-1999]'s Strawson move, at signature level: a projection row
holds *modulo presuppositions* when the projected relation holds on the
region where the arguments' presuppositions are satisfied.
`NLRelation.HoldsOn D` relativizes the lattice content of a relation to a
region `D`; `EntailmentSig.StrawsonSoundFor σ f defined` is `SoundFor`
with every projected relation read on `defined x ⊓ defined y` — the
symmetric definedness gate of [gajewski-2011]'s Strawson
anti-additivity. Classical soundness is the trivial-definedness case
(`strawsonSoundFor_top_iff`) and implies the Strawson form at any
definedness (`EntailmentSig.SoundFor.strawsonSoundFor`).

The operator instances are the semantic content of the
`classicalSignature = none` rows of
`Semantics.Polarity.Licensing.contextProperties`: `onlyFull`,
`sorryFull`, `superlativeAssert`, and `sinceFull` realize the `.anti` row
Strawson-ly while failing it classically.

## Main declarations

- `NLRelation.HoldsOn`: relation content relativized to a region;
- `EntailmentSig.StrawsonSoundFor`: row soundness modulo presupposition;
- `strawsonSoundFor_top_iff`, `EntailmentSig.SoundFor.strawsonSoundFor`:
  the classical ↔ Strawson bridges;
- `strawsonSoundFor_anti_of_isStrawsonDE` and the four operator instances.

Composing definedness along a path is presupposition projection and is
deliberately not attempted here — its home is a bridge to
`Semantics/Presupposition/`, not an ad-hoc operator.
-/

namespace Core.NaturalLogic

open Entailment

/-- The lattice content of a relation, relativized to a region `D` (the
worlds where the relevant presuppositions are satisfied). At `D = ⊤` this
is `NLRelation.Holds` (`holdsOn_top`). -/
def NLRelation.HoldsOn {β : Type*} [Lattice β] [BoundedOrder β] (D : β) :
    NLRelation → β → β → Prop
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
theorem NLRelation.holdsOn_top {R : NLRelation} {u v : β} :
    R.HoldsOn ⊤ u v ↔ R.Holds u v := by
  cases R <;>
    simp only [NLRelation.HoldsOn, NLRelation.Holds, inf_top_eq, top_le_iff]

/-- Plain content implies relativized content on any region. -/
theorem NLRelation.Holds.holdsOn {R : NLRelation} {u v : β} (D : β)
    (h : R.Holds u v) : R.HoldsOn D u v := by
  cases R with
  | equiv => subst h; rfl
  | forward => exact le_trans inf_le_left h
  | reverse => exact le_trans inf_le_left h
  | negation =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, le_top.trans_eq h2.symm⟩
      show u ⊓ v ⊓ D = ⊥
      rw [(h1 : u ⊓ v = ⊥), bot_inf_eq]
  | alternation =>
      show u ⊓ v ⊓ D = ⊥
      rw [(h : u ⊓ v = ⊥), bot_inf_eq]
  | cover => exact le_top.trans_eq h.symm
  | independent => trivial

end HoldsOn

section StrawsonSoundFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- σ's row is **Strawson-sound** for `f` relative to `defined`: every
projected relation holds on the region where both arguments'
presuppositions are satisfied — the symmetric gate of [gajewski-2011]'s
`IsStrawsonAntiAdditive`. -/
def EntailmentSig.StrawsonSoundFor (σ : EntailmentSig) (f : α → β)
    (defined : α → β) : Prop :=
  ∀ (R : NLRelation) (x y : α), R.Holds x y →
    (EntailmentSig.project R σ).HoldsOn (defined x ⊓ defined y) (f x) (f y)

/-- Classical soundness implies Strawson soundness at any definedness. -/
theorem EntailmentSig.SoundFor.strawsonSoundFor {σ : EntailmentSig}
    {f : α → β} (h : σ.SoundFor f) (defined : α → β) :
    σ.StrawsonSoundFor f defined :=
  fun R x y hR => (h R x y hR).holdsOn _

/-- Strawson soundness at trivial definedness is classical soundness. -/
theorem strawsonSoundFor_top_iff {σ : EntailmentSig} {f : α → β} :
    σ.StrawsonSoundFor f (fun _ => ⊤) ↔ σ.SoundFor f := by
  constructor
  · intro h R x y hR
    simpa only [inf_top_eq, NLRelation.holdsOn_top] using h R x y hR
  · intro h
    exact h.strawsonSoundFor _

end StrawsonSoundFor

/-! ### The Strawson-DE operator zoo, at signature level -/

section SetInstances

variable {W W' : Type*}

/-- [von-fintel-1999]'s Strawson-DE, at signature level: a Strawson-DE
operator realizes the `.anti` row relative to its definedness. -/
theorem strawsonSoundFor_anti_of_isStrawsonDE {f : Set W → Set W'}
    {defined : Set W → W' → Prop} (h : IsStrawsonDE f defined) :
    EntailmentSig.StrawsonSoundFor .anti f (fun p => {w | defined p w}) := by
  intro R x y hR
  cases R with
  | equiv => subst hR; rfl
  | forward =>
      rintro w ⟨hfy, hdx, _⟩
      exact h x y hR w hdx hfy
  | reverse =>
      rintro w ⟨hfx, _, hdy⟩
      exact h y x hR w hdy hfx
  | negation | alternation | cover | independent => trivial

/-- `only` realizes the `.anti` row Strawson-ly (definedness = its
existence presupposition) while failing it classically
(`onlyFull_not_de`). -/
theorem onlyFull_strawsonSoundFor_anti (x : W → Prop) :
    EntailmentSig.StrawsonSoundFor .anti (onlyFull x)
      (fun scope => {_w | ∃ w', x w' ∧ scope w'}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (onlyFull_isStrawsonDE x)

/-- Adversatives (*sorry*, *regret*, *surprised*) realize the `.anti` row
Strawson-ly (definedness = doxastic factivity) while failing it
classically (`sorryFull_not_de`). -/
theorem sorryFull_strawsonSoundFor_anti (dox bestOf : W → Set W) :
    EntailmentSig.StrawsonSoundFor .anti (sorryFull dox bestOf)
      (fun p => {w | ∀ w' ∈ dox w, p w'}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (sorryFull_isStrawsonDE dox bestOf)

/-- Superlatives realize the `.anti` row Strawson-ly in their restriction
(definedness = the designated-subject presupposition). -/
theorem superlativeAssert_strawsonSoundFor_anti (a : W) :
    EntailmentSig.StrawsonSoundFor .anti (superlativeAssert a)
      (fun restriction => {w | superlativePresup a restriction w}) :=
  strawsonSoundFor_anti_of_isStrawsonDE (superlative_isStrawsonDE a)

/-- Temporal *since* realizes the `.anti` row Strawson-ly (definedness =
the past-event presupposition). -/
theorem sinceFull_strawsonSoundFor_anti (pastEvent sinceWindow : W → Set W) :
    EntailmentSig.StrawsonSoundFor .anti (sinceFull pastEvent sinceWindow)
      (fun p => {w | ∃ w' ∈ pastEvent w, p w'}) :=
  strawsonSoundFor_anti_of_isStrawsonDE
    (sinceFull_isStrawsonDE pastEvent sinceWindow)

end SetInstances

end Core.NaturalLogic
