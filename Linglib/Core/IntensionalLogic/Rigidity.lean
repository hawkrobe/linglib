import Mathlib.Logic.Function.Basic

/-!
# Intensional Properties: Rigidity, Reference, and Variable Interpretation

@cite{gallin-1975} @cite{kripke-1980} @cite{kaplan-1989}

Framework-agnostic types for intensional semantics: intensions as functions
from indices (possible worlds) to extensions, rigid designators, evaluation,
and referential interpretation modes.

These primitives are shared by `Core.IntensionalLogic.Frame`,
`Semantics.Reference/`, `Semantics.Attitudes/`, and `RSA/` — any module
that needs world-parameterized meanings.

## Relationship to Frame

`Frame.Denot (.intens a) = F.Index → F.Denot a` is an `Intension F.Index (F.Denot a)`.
The `up`/`down` operators in `Frame.lean` are definitionally equal to
`rigid`/`evalAt` here. This file provides the framework-agnostic
versions; `Frame.lean` provides the IL-typed versions.

## Key definitions

- `Intension` — world-to-extension functions (`W → τ`)
- `IsRigid` — constancy across indices
- `CoRefer`, `CoExtensional` — world-relative and world-universal agreement
- Kripke's necessity of identity theorems
- `StableCharacter` — Kaplan's stable character predicate
- `ReferentialMode` — Partee 1973's three-way classification
- `SitVarStatus` — Elbourne 2013's two-way classification
-/

namespace Core

/-- An intension of type τ over indices W: a function from worlds to extensions.
    @cite{gallin-1975}'s Ty2 type system: every type τ has an intensional
    counterpart `(s,τ)` interpreted as `W → ⟦τ⟧`. -/
abbrev Intension (W : Type*) (τ : Type*) := W → τ

namespace Intension

/-- A rigid designator: an intension that returns the same value at every world. -/
def rigid {W τ : Type*} (x : τ) : Intension W τ := λ _ => x

/-- Evaluate an intension at a world to get its extension. -/
def evalAt {W τ : Type*} (f : Intension W τ) (w : W) : τ := f w

/-- An intension is rigid iff it assigns the same extension at every world. -/
def IsRigid {W τ : Type*} (f : Intension W τ) : Prop := ∀ w₁ w₂, f w₁ = f w₂

/-- A rigid designator is rigid. -/
theorem rigid_isRigid {W τ : Type*} (x : τ) : IsRigid (rigid (W := W) x) :=
  λ _ _ => rfl

/-- evalAt of rigid returns the original value. -/
theorem evalAt_rigid {W τ : Type*} (x : τ) (w : W) : evalAt (rigid x) w = x := rfl

/-- `rigid` is a section (right inverse) of world-evaluation: embedding an
entity as a rigid intension and then evaluating recovers the entity.

Function-level formulation of `evalAt_rigid`. Together with
`rigid_evalAt_lossy`, this establishes `τ` as a retract of `Intension W τ`
via the section-retraction pair `(rigid, evalAt · w)`. -/
theorem rigid_section {W τ : Type*} (w : W) :
    (fun (x : τ) => evalAt (rigid (W := W) x) w) = id :=
  funext (fun _ => rfl)

/-- The reverse composition — evaluating and re-embedding — is lossy:
it collapses non-rigid intensions to their value at `w`.

If `f` is non-rigid, `rigid (f w) ≠ f` because `rigid (f w)` is the constant
function at `f w`, which disagrees with `f` at the worlds where `f` varies.
Together with `rigid_section`, this shows that `τ` is a proper retract of
`Intension W τ`: the round-trip `rigid ∘ evalAt · w` is the identity on the
image of `rigid` but collapses everything else. -/
theorem rigid_evalAt_lossy {W τ : Type*}
    (f : Intension W τ) (w : W) (hNonRigid : ¬ IsRigid f) :
    rigid (f w) ≠ f := by
  intro heq
  apply hNonRigid
  intro w₁ w₂
  have h₁ : f w = f w₁ := congrFun heq w₁
  have h₂ : f w = f w₂ := congrFun heq w₂
  exact h₁.symm.trans h₂

/-- rigid is injective: different values give different intensions. -/
theorem rigid_injective {W τ : Type*} [Inhabited W] :
    Function.Injective (rigid (W := W) (τ := τ)) :=
  λ _ _ h => congr_fun h default

/-- Two intensions co-refer at world w. -/
def CoRefer {W τ : Type*} (f g : Intension W τ) (w : W) : Prop := f w = g w

/-- Two intensions are co-extensional (agree at every world). -/
def CoExtensional {W τ : Type*} (f g : Intension W τ) : Prop := ∀ w, f w = g w

/-- Kripke's necessity of identity: if two rigid designators co-refer at any
world, they are co-extensional (and hence the same intension).

This is the formal kernel of the @cite{kripke-1980} argument: "Hesperus" and
"Phosphorus" are both rigid; if they co-refer at the actual world then
they pick out the same object at every world, so "Hesperus = Phosphorus"
is necessary if true. -/
theorem rigid_identity_necessary {W τ : Type*}
    (f g : Intension W τ) (hf : IsRigid f) (hg : IsRigid g)
    (w : W) (h : CoRefer f g w) : CoExtensional f g :=
  λ w' => calc
    f w' = f w := hf w' w
    _ = g w := h
    _ = g w' := hg w w'

/-- Iff version of the necessity of identity: for rigid designators,
co-reference at ANY world is equivalent to co-reference at EVERY world.
Identity between rigid designators is never contingent — all or nothing. -/
theorem rigid_allOrNothing {W τ : Type*}
    (f g : Intension W τ) (hf : IsRigid f) (hg : IsRigid g)
    (w₁ w₂ : W) : f w₁ = g w₁ ↔ f w₂ = g w₂ :=
  ⟨λ h => rigid_identity_necessary f g hf hg w₁ h w₂,
   λ h => rigid_identity_necessary f g hf hg w₂ h w₁⟩

/-- An intension that takes different values at two worlds is not rigid.
Contrapositive of `IsRigid`. -/
theorem varying_not_rigid {W τ : Type*}
    (f : Intension W τ) (w₁ w₂ : W) (h : f w₁ ≠ f w₂) :
    ¬ IsRigid f :=
  λ hRigid => h (hRigid w₁ w₂)

/-- A rigid intension is never equal to a non-rigid intension. -/
theorem rigid_neq_nonrigid {W τ : Type*} (f g : Intension W τ)
    (hf : IsRigid f) (hg : ¬ IsRigid g) : f ≠ g := by
  intro heq; subst heq; exact hg hf

-- § Stable Character (Kaplan 1989 §XIX Remarks 5-8)

/-- A character is stable iff it assigns the same content at every context.

@cite{kaplan-1989} @cite{von-fintel-heim-2011} Remark 5: non-indexical expressions have stable character —
their content does not depend on the context of utterance. This generalizes
`constantCharacter` from `Reference/Basic.lean` to the framework-agnostic level. -/
def StableCharacter {C W τ : Type*} (char : C → Intension W τ) : Prop :=
  ∀ c₁ c₂ : C, char c₁ = char c₂

end Intension

end Core


-- ════════════════════════════════════════════════════════════════
-- Referential Mode (@cite{partee-1973})
-- ════════════════════════════════════════════════════════════════

namespace Core.ReferentialMode

/-- @cite{partee-1973}'s three-way interpretive classification for referential
    expressions. Applies uniformly to pronouns (entity variables) and
    tenses (temporal variables).

    | Mode      | Pronouns                 | Tenses                         |
    |-----------|--------------------------|--------------------------------|
    | indexical | "I" → agent of context   | present → speech time          |
    | anaphoric | "he" → salient individual| past → salient narrative time  |
    | bound     | "his" in ∀x...his...     | tense in "whenever...is..."    |

    @cite{elbourne-2013} collapses this to a two-way free/bound distinction
    (`SitVarStatus`); `isFree` provides the coarsening. -/
inductive ReferentialMode where
  /-- Anchored to utterance context (Kaplan's "I", Partee's deictic tense) -/
  | indexical
  /-- Resolved by discourse salience (3rd-person "he", narrative past) -/
  | anaphoric
  /-- Bound by a c-commanding operator (∀x...his..., whenever...is...) -/
  | bound
  deriving DecidableEq, Repr

/-- Coarsen to a two-way free/bound classification.
    Indexical and anaphoric are both "free" — they differ only in how the
    free variable is pragmatically resolved (utterance context vs. discourse
    salience). -/
def ReferentialMode.isFree : ReferentialMode → Bool
  | .indexical | .anaphoric => true
  | .bound => false

end Core.ReferentialMode


-- ════════════════════════════════════════════════════════════════
-- Situation Variable Status (@cite{elbourne-2013})
-- ════════════════════════════════════════════════════════════════

namespace Core.SitVarStatus

/-- @cite{elbourne-2013}'s two-way classification of situation variables.
    Coarsens `ReferentialMode`'s three-way distinction: indexical and
    anaphoric both map to `free`. -/
inductive SitVarStatus where
  /-- Free: mapped to a contextually salient situation (→ de re) -/
  | free
  /-- Bound: bound by an intensional operator (→ de dicto) -/
  | bound
  deriving DecidableEq, Repr

open Core.ReferentialMode (ReferentialMode)

/-- Expand Elbourne's two-way classification to Partee's three-way.
    Free situation variables correspond to either indexical or anaphoric
    interpretation; bound corresponds to bound. -/
def SitVarStatus.toReferentialModes : SitVarStatus → List ReferentialMode
  | .free  => [.indexical, .anaphoric]
  | .bound => [.bound]

/-- Collapse Partee's three-way classification to Elbourne's two-way.
    Uses `ReferentialMode.isFree` for the coarsening. -/
def ReferentialMode.toSitVarStatus : ReferentialMode → SitVarStatus :=
  λ m => if m.isFree then .free else .bound

/-- Round-trip: collapsing then expanding recovers the original status
    (as a member of the expanded list). -/
theorem sitVarStatus_roundtrip (s : SitVarStatus) :
    ∀ m ∈ s.toReferentialModes, ReferentialMode.toSitVarStatus m = s := by
  intro m hm
  cases s <;> simp [SitVarStatus.toReferentialModes] at hm <;>
    rcases hm with rfl | rfl <;> rfl

end Core.SitVarStatus
