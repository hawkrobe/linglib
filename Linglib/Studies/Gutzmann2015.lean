import Linglib.Pragmatics.Expressives.Basic
import Linglib.Fragments.German.ClauseTypes
import Linglib.Fragments.German.Particles
import Linglib.Features.ClauseForm

/-!
# Gutzmann (2015): Sentence Mood as Use-Conditional Meaning
[gutzmann-2015]

*Use-Conditional Meaning: Studies in Multidimensional Semantics* (OUP).
Self-contained study: the L_TU logic (the book's central formal
contribution, a three-dimensional extension of [potts-2005]'s L_CI),
the sentence-mood operators DEONT/EPIS/HKNOW as use-conditional items,
their composition in the German clause-type inventory, and the modal
particle predictions. (L_TU and the mood operators live here rather
than in the theory layer because this book is their only consumer;
they graduate per the ≥ 2-studies rule if a second study consumes
them.)

## Key claims

1. Sentence mood operators (deontic, epistemic) are UCIs, not presuppositions
2. The epistemic interpretation of [±wh] does NOT pass standard
   presupposition tests (negation, disjunction)
3. V2-interrogatives carry a HKNOW condition absent from VL-interrogatives
   (the Cuban cigar argument)
4. Modal particles are functional expletive UCIs whose mood restrictions
   derive from interaction with sentence mood operators
5. *wohl* is a UC-modifier (not a UCI), with selectional restriction

## Clause type predictions

| Clause type       | t-content | u-content                    |
|-------------------|-----------|------------------------------|
| dass-VL           | p         | DEONT(p)                     |
| V2-declarative    | p         | DEONT(EPIS(p))               |
| VL-interrogative  | p         | DEONT(EPIS(p))               |
| V2-interrogative  | p         | DEONT(EPIS(p)) ⊙ HKNOW(p)   |
| Imperative        | p         | DEONT(p)                     |

## The L_TU architecture

Every expression carries three meaning dimensions — **t-dim**
(truth-conditional, world-indexed), **s-dim** (active use-conditional
content being composed), **u-dim** (completed use-conditional
propositions, context-indexed). Multidimensional application (MA)
composes dimensions pointwise; use-conditional elimination (UE) stores
a completed s-dim in the u-dim and resets. The non-interaction theorem
(`non_interaction`) guarantees use-conditional meaning never leaks
into truth conditions.
-/

namespace Gutzmann2015

open Features
open German.ClauseTypes
open German.Particles
open Pragmatics.Expressives (TwoDimProp)

/-! ## The L_TU logic -/

open Pragmatics.Expressives (TwoDimProp)

/-! ### L_TU Type System -/

/-- The L_TU type system ([gutzmann-2015], (4.45)).

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

/-! ### UCI Typology -/

/-- UCI classification by three binary features ([gutzmann-2015], Ch 2).

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
Example: [potts-2005]'s comma feature for appositives. -/
def functionalShunting : UCIClass :=
  { functional := true, twoDimensional := false, resourceSensitive := true }

/-- Functional mixed: takes an argument, contributes to both dimensions.
Example: some honorific systems. -/
def functionalMixed : UCIClass :=
  { functional := true, twoDimensional := true, resourceSensitive := false }

/-! ### Use-Conditional Expressions -/

/-- How a use-conditional expression interacts with composition
([gutzmann-2015], §6.5).

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
([gutzmann-2015], §6.5).

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

/-! ### Three-Dimensional Meanings -/

/-- A three-dimensional meaning in L_TU ([gutzmann-2015], (4.46)).

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

/-- Multidimensional application ([gutzmann-2015], (4.46)).

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

/-- Use-conditional elimination ([gutzmann-2015], (4.54)).

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

/-! ### Bridge to TwoDimProp -/

/-- Project a three-dimensional meaning to a `TwoDimProp` (final
interpretation).

After all composition and UE steps, the final meaning of a sentence
has t-dim = truth-conditional content and u-dim = accumulated
use-conditional propositions. The s-dim equals t-dim (reset by UE)
and is discarded.

The `evalU` function projects the context-indexed u-dim (`C → Bool`)
to a world-indexed CI content (`W → Bool`) for the `TwoDimProp.ci`
field. This corresponds to [gutzmann-2015]'s lowering operator
`⇓_c` which converts u-propositions to world sets by fixing context
parameters except the world. -/
def toTwoDim {C W : Type*}
    (m : ThreeDimMeaning C W) (evalU : (C → Prop) → W → Prop) :
    TwoDimProp W where
  atIssue := m.tDim
  ci := evalU m.uDim

/-! ### Key Theorems -/

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

/-! ### Non-Interaction (General) -/

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

/-- **Non-interaction theorem** ([gutzmann-2015]).

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

/-! ### UCI Non-Contribution -/

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

/-! ### Bridge Compositionality -/

/-- The 3D→2D bridge commutes with MA when the lowering operator
distributes over conjunction.

If `evalU` preserves conjunctive structure (i.e., lowering a conjunction
of u-propositions equals the conjunction of lowered u-propositions),
then projecting a composed 3D meaning to 2D is the same as composing
the individual 2D projections.

This is the formal guarantee that L_TU's 3D composition "collapses"
correctly into [potts-2005]'s 2D framework. -/
theorem toTwoDim_multidimApp {C W : Type*}
    (f a : ThreeDimMeaning C W) (evalU : (C → Prop) → W → Prop)
    (hConj : ∀ (p q : C → Prop) (w : W),
      evalU (λ c => p c ∧ q c) w ↔ (evalU p w ∧ evalU q w)) :
    toTwoDim (multidimApp f a) evalU =
    TwoDimProp.and (toTwoDim f evalU) (toTwoDim a evalU) := by
  ext w
  · simp only [toTwoDim, multidimApp, TwoDimProp.and_atIssue]
  · simp only [toTwoDim, multidimApp, TwoDimProp.and_ci, hConj]

/-! ## Sentence-mood operators as UCIs -/

/-! ### Mood Context -/

/-- A context of utterance for sentence mood evaluation.

Captures the context parameters that sentence mood operators quantify
over: `c_S` (speaker), `c_A` (addressee), `c_W` (world of the context).

**Simplification**: [gutzmann-2015] defines DEONT via existential
quantification over a set D of contextually suitable deontic predicates
(wants, wishes, orders, ...). The full definition is:
`⟦DEONT⟧ = λp.{c : ∃ d ∈ D, d suitable for p in c ∧ d(c_S, p, c_W)}`.
We simplify this to a fixed `speakerWants` function, which suffices for
the core derivation theorems but does not capture the context-dependent
selection among different deontic attitudes. -/
structure MoodContext (W : Type*) where
  /-- The world of the utterance context -/
  world : W
  /-- Whether the speaker wants p to hold (given p's truth value at world) -/
  speakerWants : Bool → Bool
  /-- Whether the addressee knows whether p (given p's truth value at world) -/
  addresseeKnows : Bool → Bool

/-! ### Sentence Mood Operators -/

/-- Deontic sentence mood operator ([gutzmann-2015], (5.85)).

⟦DEONT⟧ = λp. {c : there is a d ∈ D such that d is suitable for p
in c and d holds for p in c_W}

Simplified: the speaker wants `p` to hold in the utterance world.

Introduced by the root rule (5.43): every matrix clause gets a deontic
interpretation, expressing a volition on the part of the speaker. -/
def deont {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  c.speakerWants (p c.world)

/-- Epistemic sentence mood operator ([gutzmann-2015], (5.90)).

⟦EPIS⟧ = λp. {w : EPIS(p)(w) in w} = λp. {w : there is an e ∈ E
suitable for p in w and e holds for p in w}

Simplified: at the world level, epistemic embedding preserves truth.
The epistemic contribution is in the *use-conditional* dimension,
mediated by the E modifier. -/
def epis {W : Type*} (p : W → Bool) : W → Bool := p

/-- The E operator: epistemic modifier on UCIs ([gutzmann-2015], (5.91)).

E = λDλp. D(EPIS(p))

This is a use-conditional modifier of type
`⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩`. It takes a UCI (like DEONT) that maps
propositions to use-conditional propositions, and pre-composes it
with EPIS. The result is that DEONT applies to the epistemically
embedded proposition rather than the raw propositional content. -/
def episModifier {W : Type*}
    (d : (W → Bool) → MoodContext W → Bool) :
    (W → Bool) → MoodContext W → Bool :=
  λ p c => d (epis p) c

/-- Hearer knowledge operator ([gutzmann-2015], (5.99)).

⟦HKNOW⟧ = λp. {c : c_A knows whether p in c_W}

A functional expletive UCI that adds a "free-floating" use condition:
the addressee knows the answer to the question. Present only in
V2-interrogatives (triggered by [−wh] in C⁰), absent from
VL-interrogatives — accounting for the Cuban cigar scenario. -/
def hknow {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  c.addresseeKnows (p c.world)

/-! ### Mood Operator Inventory -/

/-- Which sentence mood operators are present in a clause type
([gutzmann-2015], Table 5.1).

Language-agnostic predicate over a (possibly language-specific) clause
type, recording which of DEONT, EPIS, and HKNOW the clause composes.
Used by per-language clause-type fragments to declare their mood
inventories (e.g., `German.ClauseTypes.GermanClauseType.moodStructure`). -/
structure MoodStructure where
  hasDeontic : Bool
  hasEpistemic : Bool
  hasHearerKnowledge : Bool
  deriving DecidableEq, Repr

/-! ### Operator-level theorems -/

/-- Epistemic embedding preserves truth at the world level. The
epistemic contribution is purely use-conditional, not truth-conditional. -/
theorem epis_preserves_truth {W : Type*} (p : W → Bool) (w : W) :
    epis p w = p w := rfl

/-! ## The German clause-type mood compositions -/

/-! ### German clause-type mood compositions -/

/-- dass-VL clause mood: DEONT only ([gutzmann-2015], (5.82)).

No [±wh] visible at LF (dass is semantically empty, so [−wh] is
invisible per the visibility condition (5.41)). Therefore no epistemic
interpretation is triggered. The root rule introduces DEONT.

"Dass du nicht zu spät kommst!" = The speaker wants [you not arrive late]. -/
def dassVLMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  deont p c

/-- V2-declarative mood: DEONT(EPIS(p)) ([gutzmann-2015], (5.93)–(5.96)).

The finite verb moves to C⁰ (V-to-C triggered by [−wh] attached to an
overt element at PF). The [−wh] is visible at LF, triggering epistemic
interpretation. The root rule adds DEONT, and E modifies it to embed
the epistemic predicate.

"Jim wohnt in Berlin." = The speaker wants the hearer to believe
[Jim lives in Berlin]. -/
def v2DeclMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c

/-- V2-interrogative mood: DEONT(EPIS(p)) ⊙ HKNOW(p)
([gutzmann-2015], (5.100)).

V2-interrogatives have two [±wh] specifications: [+wh] in CP^spec
and [−wh] in C⁰ (Brandt et al. 1992). The first triggers epistemic
interpretation, the second (in C⁰) triggers an additional epistemic
interpretation resolved to hearer knowledge. HKNOW is a separate
functional expletive UCI whose u-content is conjoined (⊙) with the
deontic/epistemic mood.

"Kommt Peter?" = The speaker wants to know [whether Peter comes]
AND the addressee knows [whether Peter comes]. -/
def v2InterrogMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c && hknow p c

/-- VL-interrogative mood: DEONT(EPIS(p)) only — no HKNOW
([gutzmann-2015], p. 213).

VL-interrogatives (e.g., "Wann Peter nach Hause kommt?") lack the
[−wh] in C⁰ that triggers HKNOW. Therefore they are felicitous even
when the hearer does not know the answer (the Cuban cigar scenario). -/
def vlInterrogMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c

/-! ### Mood-operator theorems for the German clause-type compositions -/

/-- dass-VL clauses have no epistemic component. -/
theorem dassVL_is_pure_deontic {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    dassVLMood p c = deont p c := rfl

/-- V2-interrogatives differ from VL-interrogatives only in the
HKNOW component (hearer knowledge use condition). -/
theorem v2_vs_vl_interrog {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    v2InterrogMood p c = (vlInterrogMood p c && hknow p c) := rfl

/-! ### German Clause Types as a refinement of Features.ClauseForm -/

/-- The mood structure of each German clause type, derived from
the theory of [±wh] visibility and the root rule. -/
def _root_.German.ClauseTypes.GermanClauseType.moodStructure : ∀ {f : ClauseForm},
    GermanClauseType f → MoodStructure
  | _, .dassVL          => ⟨true, false, false⟩
  | _, .v2Declarative   => ⟨true, true, false⟩
  | _, .v2Interrogative => ⟨true, true, true⟩
  | _, .vlInterrogative => ⟨true, true, false⟩
  | _, .imperative      => ⟨true, false, false⟩

/-- Every matrix clause has a deontic operator (the root rule). -/
theorem every_clause_has_deont {f : ClauseForm} (ct : GermanClauseType f) :
    ct.moodStructure.hasDeontic = true := by
  cases ct <;> rfl

/-- Imperatives lack EPIS — the structural basis for selectional
restrictions on UC-modifiers like *wohl*. -/
theorem imperative_lacks_epis :
    GermanClauseType.imperative.moodStructure.hasEpistemic = false := rfl

/-- dass-VL and imperatives share mood structure: deontic only. -/
theorem dassVL_matches_imperative :
    GermanClauseType.dassVL.moodStructure =
    GermanClauseType.imperative.moodStructure := rfl

/-- V2-interrogatives differ from VL-interrogatives only in HKNOW. -/
theorem v2_vl_differ_only_in_hknow :
    GermanClauseType.v2Interrogative.moodStructure.hasDeontic =
      GermanClauseType.vlInterrogative.moodStructure.hasDeontic ∧
    GermanClauseType.v2Interrogative.moodStructure.hasEpistemic =
      GermanClauseType.vlInterrogative.moodStructure.hasEpistemic ∧
    GermanClauseType.v2Interrogative.moodStructure.hasHearerKnowledge = true ∧
    GermanClauseType.vlInterrogative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- HKNOW iff matrix question — restated structurally as a fact about the
index. The HKNOW use condition tracks *form*-level matrix interrogativity
([gutzmann-2015], p. 213, Cuban cigar argument). -/
theorem hknow_iff_matrix_question {f : ClauseForm} (ct : GermanClauseType f) :
    ct.moodStructure.hasHearerKnowledge = true ↔ f = .matrixQuestion := by
  cases ct <;> simp [GermanClauseType.moodStructure]

/-- Matrix-question German clauses always carry HKNOW. -/
theorem matrix_question_has_hknow (ct : GermanClauseType .matrixQuestion) :
    ct.moodStructure.hasHearerKnowledge = true := by
  cases ct; rfl

/-- The `.declarative` fiber is many-to-one — three German clause types
inhabit it (dassVL, v2Declarative, imperative), and they are
distinguishable only at the `moodStructure` level. The contrast below
type-checks because both terms have type `GermanClauseType .declarative`. -/
theorem declarative_fiber_underdetermines_mood :
    (GermanClauseType.dassVL : GermanClauseType .declarative).moodStructure ≠
    (GermanClauseType.v2Declarative : GermanClauseType .declarative).moodStructure := by
  decide

/-! ## Mood-structure predictions -/

/-- The Cuban cigar argument: V2- and VL-interrogatives differ ONLY in
the hearer knowledge condition. This explains why VL-interrogatives
are felicitous even when the hearer clearly does not know the answer
(the Cuban cigar scenario), while V2-interrogatives are not. -/
theorem cuban_cigar :
    GermanClauseType.v2Interrogative.moodStructure.hasHearerKnowledge = true ∧
    GermanClauseType.vlInterrogative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl⟩

/-- Imperatives share dass-VL mood structure (deontic only):
both lack [±wh] at LF, so neither triggers epistemic interpretation. -/
theorem imperative_matches_dassVL :
    GermanClauseType.imperative.moodStructure =
    GermanClauseType.dassVL.moodStructure := rfl

/-- dass-VL clauses have no epistemic component. -/
theorem dassVL_no_epis :
    GermanClauseType.dassVL.moodStructure.hasEpistemic = false := rfl

/-- V2-declaratives have epistemic but not hearer knowledge. -/
theorem v2Decl_epis_no_hknow :
    GermanClauseType.v2Declarative.moodStructure.hasEpistemic = true ∧
    GermanClauseType.v2Declarative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl⟩

/-! ## Modal particle–mood interaction -/

/-- Gutzmann's L_TU classification (§6.5): *ja/denn/halt/doch* are
functional-expletive UCIs of type `⟨⟨s,t⟩, u⟩`, restricted via
use-conditional conflict. (Formerly fragment fields; the typing is this
book's analysis.) -/
def uciParticles : List Particle := [ja, denn, halt, doch]

/-- *wohl* is Gutzmann's sole UC-modifier among the common MPs: type
`⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩`, modifying EPIS, restricted selectionally. -/
def ucModifiers : List Particle := [wohl]

/-- Restriction kind per Gutzmann: UCIs restrict via use-conditional
conflict, UC-modifiers selectionally (imperatives lack EPIS — a type
mismatch, not a pragmatic conflict). -/
def restrictionKind (p : Particle) : RestrictionKind :=
  if p ∈ ucModifiers then .selectional else .ucConflict

/-- *wohl*'s licensing across German clause types is exactly the
presence of EPIS in the clause type's mood structure — the formal
content of the selectional restriction analysis. -/
theorem wohl_iff_epis {f : ClauseForm} (ct : GermanClauseType f) :
    licensedInClause wohl ct = ct.moodStructure.hasEpistemic := by
  cases ct <;> rfl

/-- *ja* is restricted to declaratives, matching the clause type with
deontic + epistemic mood but without the hearer knowledge condition. -/
theorem ja_declarative_restriction :
    ja.LicensedIn .declarative ∧ ¬ ja.LicensedIn .polarInterrogative := by decide

/-- *denn* is the interrogative counterpart of *ja*. -/
theorem denn_interrogative_restriction :
    ¬ denn.LicensedIn .declarative ∧ denn.LicensedIn .polarInterrogative := by decide

/-- *ja* and *denn* partition clause types: they are never both
licensed in the same clause type. -/
theorem ja_denn_partition {f : ClauseForm} (ct : GermanClauseType f) :
    ¬(licensedInClause ja ct = true ∧ licensedInClause denn ct = true) :=
  ja_denn_complementary ct

end Gutzmann2015
