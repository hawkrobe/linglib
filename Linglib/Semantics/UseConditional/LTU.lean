import Linglib.Theories.Pragmatics.Expressives.Basic

/-!
# L_TU: A Logic for Truth-Conditional and Use-Conditional Meaning
@cite{gutzmann-2015}

The central formal contribution of @cite{gutzmann-2015}'s "Use-Conditional
Meaning": a three-dimensional compositional semantics that extends
@cite{potts-2005}'s two-dimensional L_CI.

## Key Insight

Every expression carries three meaning dimensions:
- **t-dim**: truth-conditional content (evaluated at worlds)
- **s-dim**: active use-conditional content (being composed, world-indexed)
- **u-dim**: completed use-conditional propositions (evaluated at contexts)

The s-dimension is a *staging area*: use-conditional content composes there
before being "stored" in the u-dimension via use-conditional elimination (UE).
After UE, the t-dimension copies back into s-dim, making it available for
further truth-conditional composition.

## Composition

Two rules drive the system:
1. **Multidimensional application (MA)**: applies t-dims pointwise, s-dims
   pointwise, and merges u-dims via conjunction.
2. **Use-conditional elimination (UE)**: when the s-dim reaches type u,
   shift it to u-dim (conjoining with existing u-content) and reset s-dim
   to a copy of t-dim.

## UCI Typology

Use-conditional items (UCIs) are classified by three binary features:
- [±functional]: does the UCI take a truth-conditional argument?
- [±2-dimensional]: does the UCI contribute to both dimensions?
- [±resource-sensitive]: is the UCI's argument "consumed" (shunted)?

These yield five valid UCI classes (isolated expletive, isolated mixed,
functional expletive, functional shunting, functional mixed).
-/

namespace Semantics.UseConditional

open Pragmatics.Expressives (TwoDimProp)


-- ════════════════════════════════════════════════════════════════
-- § 1. L_TU Type System
-- ════════════════════════════════════════════════════════════════

/-- The L_TU type system (@cite{gutzmann-2015}, (4.45)).

Basic types: `e` (entities), `t` (truth values), `u` (use-conditional
propositions, opaque). A type is *use-conditional* iff it equals `u`
or is a function type whose codomain is use-conditional. -/
inductive UCType where
  | e : UCType
  | t : UCType
  | u : UCType
  | func : UCType → UCType → UCType
  deriving DecidableEq, Repr

/-- A type is use-conditional iff it is `u` or a function into a
use-conditional type. This determines which dimension an expression's
content targets during composition. -/
def UCType.IsUCType : UCType → Prop
  | .u => True
  | .func _ τ => τ.IsUCType
  | _ => False

instance UCType.decIsUCType : DecidablePred UCType.IsUCType
  | .e => isFalse (fun h => h)
  | .t => isFalse (fun h => h)
  | .u => isTrue trivial
  | .func _ τ => UCType.decIsUCType τ

theorem u_is_uc : UCType.u.IsUCType := trivial
theorem t_is_not_uc : ¬ UCType.t.IsUCType := fun h => h
theorem func_into_u_is_uc : (UCType.func .e .u).IsUCType := trivial


-- ════════════════════════════════════════════════════════════════
-- § 2. UCI Typology
-- ════════════════════════════════════════════════════════════════

/-- UCI classification by three binary features (@cite{gutzmann-2015}, Ch 2).

- `functional`: takes a truth-conditional argument (vs isolated)
- `twoDimensional`: contributes to both t-dim and s-dim (vs expletive)
- `resourceSensitive`: argument is consumed/shunted (vs passed through) -/
structure UCIClass where
  functional : Bool
  twoDimensional : Bool
  resourceSensitive : Bool
  deriving DecidableEq, Repr

/-- Isolated expletive: no argument, only use-conditional content.
Example: *damn* in "the damn dog." -/
def isolatedExpletive : UCIClass :=
  { functional := false, twoDimensional := false, resourceSensitive := false }

/-- Isolated mixed: no argument, contributes to both dimensions.
Example: ethnic slurs with descriptive + expressive content. -/
def isolatedMixed : UCIClass :=
  { functional := false, twoDimensional := true, resourceSensitive := false }

/-- Functional expletive: takes an argument, only use-conditional output.
Example: German modal particles *ja*, *denn*; sentence mood operators. -/
def functionalExpletive : UCIClass :=
  { functional := true, twoDimensional := false, resourceSensitive := false }

/-- Functional shunting: takes an argument that is consumed (not returned).
Example: @cite{potts-2005}'s comma feature for appositives. -/
def functionalShunting : UCIClass :=
  { functional := true, twoDimensional := false, resourceSensitive := true }

/-- Functional mixed: takes an argument, contributes to both dimensions.
Example: some honorific systems. -/
def functionalMixed : UCIClass :=
  { functional := true, twoDimensional := true, resourceSensitive := false }


-- ════════════════════════════════════════════════════════════════
-- § 3. Use-Conditional Expressions
-- ════════════════════════════════════════════════════════════════

/-- How a use-conditional expression interacts with composition
(@cite{gutzmann-2015}, §6.5).

A UCI is a *use-conditional item*: it contributes u-content by taking
truth-conditional arguments. A UC-modifier takes another UCI as its
argument and modifies its use-conditional behavior.

This distinction drives two different mechanisms for mood restriction:
- UCIs are restricted by *use-conditional conflict* (their independent
  u-content is incompatible with certain mood operators)
- UC-modifiers are restricted *selectionally* (the mood operator they
  modify is absent from certain clause types) -/
inductive UCExprKind where
  /-- Use-conditional item: maps truth-conditional content to u-content.
  Type: `⟨⟨s,t⟩, u⟩` (functional) or `u` (isolated). -/
  | uci
  /-- Use-conditional modifier: maps UCIs to UCIs.
  Type: `⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩`. Modifies an existing mood operator
  (e.g., German *wohl* modifies EPIS). -/
  | ucModifier
  deriving DecidableEq, Repr

/-- How an expression's mood restriction arises
(@cite{gutzmann-2015}, §6.5).

The two mechanisms are empirically distinguishable: selectional
restrictions produce type-mismatch infelicity, while use-conditional
conflict produces pragmatic deviance. -/
inductive RestrictionKind where
  /-- The expression modifies a mood operator that is absent from
  certain clause types — a type mismatch. Example: German *wohl*
  modifies EPIS, which is absent from imperatives. -/
  | selectional
  /-- The expression's independent u-content is incompatible with
  certain sentence moods. Example: German *ja*'s common-ground
  reminder conflicts with the epistemic uncertainty of interrogatives. -/
  | ucConflict
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════════════════
-- § 4. Three-Dimensional Meanings
-- ════════════════════════════════════════════════════════════════

/-- A three-dimensional meaning in L_TU (@cite{gutzmann-2015}, (4.46)).

`C` is the context type (for use-conditional propositions, sets of contexts),
`W` is the world type (for truth-conditional propositions, sets of worlds).

The crucial type distinction: `uDim` is `C → Bool` while `tDim`/`sDim`
are `W → Bool`. Use-conditional propositions constrain the *context of
utterance*, not the described world — matching Kaplan's character/content
distinction. -/
structure ThreeDimMeaning (C : Type*) (W : Type*) where
  /-- Truth-conditional content: the at-issue proposition -/
  tDim : W → Prop
  /-- Active use-conditional content being composed -/
  sDim : W → Prop
  /-- Completed use-conditional propositions (stored, inaccessible to
      further truth-conditional composition) -/
  uDim : C → Prop

/-- Multidimensional application (@cite{gutzmann-2015}, (4.46)).

The full MA rule applies functions *intradimensionally*: dimension 1
applies `σ(β₁)`, dimension 2 applies `ρ(β₂)`, and u-dimensions merge
via `⊙` (conjunction). At the **propositional level** — where both inputs
are already of type `⟨s,t⟩` — function application reduces to pointwise
conjunction, which is what this definition implements. The sub-propositional
case (where dims 1-2 are genuine function applications) is not formalized. -/
def multidimApp {C W : Type*}
    (f a : ThreeDimMeaning C W) : ThreeDimMeaning C W where
  tDim := λ w => f.tDim w ∧ a.tDim w
  sDim := λ w => f.sDim w ∧ a.sDim w
  uDim := λ c => f.uDim c ∧ a.uDim c

/-- Use-conditional elimination (@cite{gutzmann-2015}, (4.54)).

When the s-dimension reaches type `u` (its content is a completed
use-conditional proposition), UE:
1. Shifts s-dim content to u-dim (conjoining with existing u-content)
2. Resets s-dim to a copy of t-dim

The `eval` parameter bridges the world-indexed s-dim to the
context-indexed u-dim, typically by projecting the world from the context. -/
def ucElim {C W : Type*}
    (m : ThreeDimMeaning C W) (eval : (W → Prop) → C → Prop) :
    ThreeDimMeaning C W where
  tDim := m.tDim
  sDim := m.tDim
  uDim := λ c => m.uDim c ∧ eval m.sDim c

/-- Lift a truth-conditional proposition to a three-dimensional meaning.

Both t-dim and s-dim carry the propositional content.
u-dim is trivially satisfied (no use-conditional content yet).
Corresponds to a pure truth-conditional lexical item before LER
extension. -/
def ofTruthConditional {C W : Type*} (p : W → Prop) : ThreeDimMeaning C W where
  tDim := p
  sDim := p
  uDim := λ _ => True

/-- Lift a use-conditional function to a three-dimensional meaning.

t-dim is trivially true (UCIs do not contribute truth conditions).
s-dim carries the active UCI content.
u-dim is trivially true until `ucElim` fires. -/
def ofUCI {C W : Type*} (ucContent : W → Prop) : ThreeDimMeaning C W where
  tDim := λ _ => True
  sDim := ucContent
  uDim := λ _ => True


-- ════════════════════════════════════════════════════════════════
-- § 5. Bridge to TwoDimProp
-- ════════════════════════════════════════════════════════════════

/-- Project a three-dimensional meaning to a `TwoDimProp` (final
interpretation).

After all composition and UE steps, the final meaning of a sentence
has t-dim = truth-conditional content and u-dim = accumulated
use-conditional propositions. The s-dim equals t-dim (reset by UE)
and is discarded.

The `evalU` function projects the context-indexed u-dim (`C → Bool`)
to a world-indexed CI content (`W → Bool`) for the `TwoDimProp.ci`
field. This corresponds to @cite{gutzmann-2015}'s lowering operator
`⇓_c` which converts u-propositions to world sets by fixing context
parameters except the world. -/
def toTwoDim {C W : Type*}
    (m : ThreeDimMeaning C W) (evalU : (C → Prop) → W → Prop) :
    TwoDimProp W where
  atIssue := m.tDim
  ci := evalU m.uDim


-- ════════════════════════════════════════════════════════════════
-- § 6. Key Theorems
-- ════════════════════════════════════════════════════════════════

/-- UE does not affect truth conditions.

This is the formal guarantee of *non-interaction*: storing use-conditional
content in the u-dimension never changes what a sentence says about the
world. -/
theorem ucElim_preserves_tDim {C W : Type*}
    (m : ThreeDimMeaning C W) (eval : (W → Prop) → C → Prop) :
    (ucElim m eval).tDim = m.tDim := rfl

/-- After UE, the s-dimension is reset to the t-dimension. -/
theorem ucElim_resets_sDim {C W : Type*}
    (m : ThreeDimMeaning C W) (eval : (W → Prop) → C → Prop) :
    (ucElim m eval).sDim = m.tDim := rfl

/-- MA merges u-dimensions via conjunction. Completed use-conditional
propositions from both constituents are preserved. -/
theorem multidimApp_merges_uDim {C W : Type*}
    (f a : ThreeDimMeaning C W) (c : C) :
    (multidimApp f a).uDim c ↔ (f.uDim c ∧ a.uDim c) := Iff.rfl

/-- A pure truth-conditional expression has trivial use conditions. -/
theorem ofTruthConditional_trivial_uDim {C W : Type*}
    (p : W → Prop) (c : C) :
    (ofTruthConditional (C := C) p).uDim c := trivial

/-- A UCI has trivial truth conditions. -/
theorem ofUCI_trivial_tDim {C W : Type*}
    (ucContent : W → Prop) (w : W) :
    (ofUCI (C := C) ucContent).tDim w := trivial


-- ════════════════════════════════════════════════════════════════
-- § 7. Non-Interaction (General)
-- ════════════════════════════════════════════════════════════════

/-- A derivation in the propositional fragment of L_TU.

Derivation trees encode the composition history: which expressions
were combined via MA, and where UE was applied. This lets us state
and prove properties of *all possible* derivations, not just specific
ones. -/
inductive LTUDeriv (C : Type*) (W : Type*) where
  /-- A lexical item (leaf of the derivation tree) -/
  | leaf : ThreeDimMeaning C W → LTUDeriv C W
  /-- Multidimensional application of two sub-derivations -/
  | app : LTUDeriv C W → LTUDeriv C W → LTUDeriv C W
  /-- Use-conditional elimination applied to a sub-derivation -/
  | elim : LTUDeriv C W → ((W → Prop) → C → Prop) → LTUDeriv C W

/-- Evaluate a derivation to its three-dimensional meaning. -/
def LTUDeriv.eval {C W : Type*} : LTUDeriv C W → ThreeDimMeaning C W
  | .leaf m => m
  | .app d₁ d₂ => multidimApp d₁.eval d₂.eval
  | .elim d f => ucElim d.eval f

/-- Strip all use-conditional content from a derivation's leaves,
replacing s-dim with t-dim and u-dim with trivial content. This
produces a "truth-conditional shadow" of the derivation. -/
def LTUDeriv.stripUC {C W : Type*} : LTUDeriv C W → LTUDeriv C W
  | .leaf m => .leaf ⟨m.tDim, m.tDim, λ _ => True⟩
  | .app d₁ d₂ => .app d₁.stripUC d₂.stripUC
  | .elim d f => .elim d.stripUC f

/-- **Non-interaction theorem** (@cite{gutzmann-2015}).

For ANY derivation built from multidimensional application and
use-conditional elimination, the truth-conditional content of the
result depends ONLY on the truth-conditional content of the inputs.

Stripping all use-conditional content from the leaves does not change
the final t-dimension. Use-conditional meaning can never leak into
truth conditions — not through MA, not through UE, not through any
combination of the two. This is the fundamental architectural guarantee
of L_TU. -/
theorem non_interaction {C W : Type*} (d : LTUDeriv C W) (w : W) :
    d.eval.tDim w ↔ d.stripUC.eval.tDim w := by
  induction d with
  | leaf _ => exact Iff.rfl
  | app d₁ d₂ ih₁ ih₂ =>
    simp only [LTUDeriv.eval, LTUDeriv.stripUC, multidimApp]
    exact and_congr ih₁ ih₂
  | elim d _ ih =>
    simp only [LTUDeriv.eval, LTUDeriv.stripUC, ucElim]
    exact ih

/-- Non-interaction at the function level (extensional form). -/
theorem non_interaction_ext {C W : Type*} (d : LTUDeriv C W) :
    d.eval.tDim = d.stripUC.eval.tDim :=
  funext (λ w => propext (non_interaction d w))


-- ════════════════════════════════════════════════════════════════
-- § 8. UCI Non-Contribution
-- ════════════════════════════════════════════════════════════════

/-- Composing with a UCI does not change truth conditions.

When a functional expletive UCI (with trivial t-dim) is composed with
truth-conditional content via MA, the t-dim of the result equals the
t-dim of the truth-conditional input. This is the formal content of
"UCIs do not contribute truth conditions." -/
theorem multidimApp_uci_tDim {C W : Type*}
    (tc : ThreeDimMeaning C W) (uci : ThreeDimMeaning C W)
    (h : ∀ w, uci.tDim w) (w : W) :
    (multidimApp tc uci).tDim w ↔ tc.tDim w := by
  simp only [multidimApp, and_iff_left (h w)]

/-- Composing with truth-conditional content does not change truth conditions
of an expression whose t-dim is already trivial. -/
theorem multidimApp_tc_preserves_uci_tDim {C W : Type*}
    (uci tc : ThreeDimMeaning C W)
    (h : ∀ w, uci.tDim w) (w : W) :
    (multidimApp uci tc).tDim w ↔ tc.tDim w := by
  simp only [multidimApp, and_iff_right (h w)]


-- ════════════════════════════════════════════════════════════════
-- § 9. Bridge Compositionality
-- ════════════════════════════════════════════════════════════════

/-- The 3D→2D bridge commutes with MA when the lowering operator
distributes over conjunction.

If `evalU` preserves conjunctive structure (i.e., lowering a conjunction
of u-propositions equals the conjunction of lowered u-propositions),
then projecting a composed 3D meaning to 2D is the same as composing
the individual 2D projections.

This is the formal guarantee that L_TU's 3D composition "collapses"
correctly into @cite{potts-2005}'s 2D framework. -/
theorem toTwoDim_multidimApp {C W : Type*}
    (f a : ThreeDimMeaning C W) (evalU : (C → Prop) → W → Prop)
    (hConj : ∀ (p q : C → Prop) (w : W),
      evalU (λ c => p c ∧ q c) w ↔ (evalU p w ∧ evalU q w)) :
    toTwoDim (multidimApp f a) evalU =
    TwoDimProp.and (toTwoDim f evalU) (toTwoDim a evalU) := by
  ext w
  · simp only [toTwoDim, multidimApp, TwoDimProp.and]
  · simp only [toTwoDim, multidimApp, TwoDimProp.and, hConj]

end Semantics.UseConditional
