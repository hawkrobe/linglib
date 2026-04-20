import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Core.Semantics.Presupposition

/-!
# Presuppositional Conditionals: K/P vs K/P*

@cite{sharvit-2025} @cite{heim-1992} @cite{rooth-partee-1982}
@cite{karttunen-peters-1979}

Formalizes the contrast between Karttunen/Peters (K/P) and Sharvit's K/P*
conditionals from "Rooth-Partee Conditionals" (Linguistics & Philosophy, 2025).

## The problem

Rooth-Partee conditionals like "If Mia is penniless or proud of her money,
Sue is (too)" have two readings:

- **if-over-∃**: single conditional with disjunctive antecedent
- **∀-over-if**: conjunction of two conditionals (one per disjunct)

Under K/P, the disjunction `or^{K/P}(penniless, proud-of-money)` is
UNDEFINED at worlds where "proud of her money"'s presupposition ("has
money") fails. This causes penniless-worlds to drop from the ∃-reading's
quantification domain, while the ∀-reading's first conditional still covers
them. Result: the two readings are NOT Strawson-equivalent.

## The fix

K/P* replaces K/P's local presupposition filtering ("if p₁(w) = False or
p₂(w) is defined") with CLOS-based filtering ("p₂ is defined at all
CLOS-closest p₁-worlds"). This is the same closest-worlds operator used
in `Counterfactual.closestWorlds`.

## Key definitions

- `closB`: Computable closest-worlds selector (= `closestWorlds`)
- `ifPresup`: K/P* conditional with CLOS-based filtering
- `ifKP`: K/P conditional with local filtering (for comparison)
- `trivialCloser`: Degenerate similarity (all worlds equally close)

-/

namespace Semantics.Conditionals.Presuppositional

open Semantics.Conditionals
open Core.Presupposition

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- § CLOS: Closest-worlds selector
-- ════════════════════════════════════════════════════════════════

/-- Computable CLOS (@cite{sharvit-2025}, (120)).

Selects worlds in `antecedent ∩ restriction` that are not dominated
under the similarity ordering. Same formula as `Counterfactual.closestWorlds`. -/
def closB [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (antecedent : List W) (w : W) : List W :=
  let pWorlds := antecedent.filter (restriction.contains ·)
  pWorlds.filter fun w' => pWorlds.all fun w'' => closer w w' w'' || !closer w w'' w'

/-- Degenerate similarity: all worlds are equally close.

With trivial similarity, `closB` returns ALL p-worlds in the restriction.
K/P* with trivial similarity has the same assertion as K/P, but the
presupposition is global (all p-worlds) vs local (evaluation world). -/
def trivialCloser : W → W → W → Bool := fun _ _ _ => true

-- ════════════════════════════════════════════════════════════════
-- § K/P* conditional (@cite{sharvit-2025}, (119))
-- ════════════════════════════════════════════════════════════════

/-- K/P* presuppositional conditional (@cite{sharvit-2025}, (119)).

- **Outer presupposition**: p must be defined at w
- **Inner presupposition (CLOS)**: q must be defined at all CLOS-closest
  p-worlds (contrast with K/P's LOCAL check)
- **Assertion**: q holds at all CLOS-closest p-worlds

When the antecedent p has no presupposition, use `PrProp.ofProp'`.
Requires `[DecidablePred p.assertion]` for `List.filter`. -/
def ifPresup [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (p : PrProp W) (q : PrProp W)
    [DecidablePred p.assertion] : PrProp W where
  presup := fun w =>
    p.presup w ∧
    let closest := closB closer restriction
      (restriction.filter (fun w => decide (p.assertion w))) w
    ∀ w' ∈ closest, q.presup w'
  assertion := fun w =>
    let closest := closB closer restriction
      (restriction.filter (fun w => decide (p.assertion w))) w
    ∀ w' ∈ closest, q.assertion w'

-- ════════════════════════════════════════════════════════════════
-- § K/P conditional (@cite{sharvit-2025}, (100)) — for comparison
-- ════════════════════════════════════════════════════════════════

/-- K/P presuppositional conditional (@cite{sharvit-2025}, (100)).

- **Outer presupposition**: p must be defined at w (same as K/P*)
- **Inner presupposition (LOCAL)**: if p is true at w, q must be defined
  at w — checks ONLY the evaluation world
- **Assertion**: q holds at all p-worlds in the restriction (same
  quantificational domain as K/P* with trivial similarity)

The difference from K/P* is entirely in the inner presupposition:
K/P checks locally at w, K/P* checks globally via CLOS.
Requires `[DecidablePred p.assertion]` for `List.filter`. -/
def ifKP [DecidableEq W] (restriction : List W)
    (p : PrProp W) (q : PrProp W)
    [DecidablePred p.assertion] : PrProp W where
  presup := fun w =>
    p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun _w =>
    let pWorlds := restriction.filter (fun w => decide (p.assertion w))
    ∀ w' ∈ pWorlds, q.assertion w'

-- ════════════════════════════════════════════════════════════════
-- § Contextual Plausibility and type-flexible disjunction
-- ════════════════════════════════════════════════════════════════

/-- Contextual Plausibility (CP): no uninformative sub-expressions.

A proposition is CP-acceptable in context `c` iff it is neither
trivially true nor trivially false in `c`. -/
def cpAcceptable (c : Set W) (p : Set W) : Prop :=
  (c ∩ p).Nonempty ∧ (c ∩ pᶜ).Nonempty

/-- Type-flexible disjunction over properties (Sharvit's `or^{K/P**}`, (142a)).

Given two properties Q₁, Q₂ : E → Bool, produces a generalized quantifier
over properties: `fun Z => Z = Q₁ ∨ Z = Q₂`. This enables the ∀-over-if
reading by making the universal quantifier range over {Q₁, Q₂}. -/
def orProperties {E : Type*} [DecidableEq (E → Bool)]
    (q₁ q₂ : E → Bool) : (E → Bool) → Bool :=
  fun z => (z == q₁) || (z == q₂)

-- ════════════════════════════════════════════════════════════════
-- § K/P* conjunction and disjunction (@cite{sharvit-2025}, (127)-(128))
-- ════════════════════════════════════════════════════════════════

/-- Worlds where p is defined and its assertion is false.

Used in `orPresup`: the CLOS-based disjunction checks presuppositions at
closest worlds where the OTHER disjunct is defined-and-false. -/
def definedFalse (p : PrProp W) : Set W :=
  fun w => p.presup w ∧ ¬p.assertion w

/-- K/P* presuppositional conjunction (@cite{sharvit-2025}, (127)).

- **Presupposition**: P₁ defined at w, P₂ defined at w, and P₂ defined
  at all CLOS-closest P₁-assertion-worlds.
- **Assertion**: P₁(w) ∧ P₂(w)

This is asymmetric: the CLOS-based check only goes from P₁-worlds to P₂.
The asymmetry mirrors K/P's `andFilter`, but uses CLOS-based rather than
local presupposition checking.
Requires `[DecidablePred p.assertion]` for `List.filter`. -/
def andPresup [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (p q : PrProp W)
    [DecidablePred p.assertion] : PrProp W where
  presup := fun w =>
    p.presup w ∧ q.presup w ∧
    let closest := closB closer restriction
      (restriction.filter (fun w => decide (p.assertion w))) w
    ∀ w' ∈ closest, q.presup w'
  assertion := fun w =>
    p.assertion w ∧ q.assertion w

/-- K/P* presuppositional disjunction (@cite{sharvit-2025}, (128)).

- **Presupposition**: (and^{K/P\*}(P₁)(P₂) defined OR and^{K/P\*}(P₂)(P₁)
  defined), AND and^{K/P\*}(¬P₁)(P₂) defined, AND and^{K/P\*}(¬P₂)(P₁)
  defined. Here ¬Pᵢ means the presuppositionless proposition "Pᵢ is
  defined and false" (`definedFalse`).
- **Assertion**: P₁(w) ∨ P₂(w)

`or^{K/P\*}` is more symmetric than `and^{K/P\*}`: condition 1 is a
disjunction over both asymmetric directions, and conditions 2-3 are
symmetric by construction.

Note: For the Rooth-Partee puzzle where disjuncts have conflicting
presuppositions (penniless entails ¬hasMoney, proud presupposes hasMoney),
the propositional `or^{K/P\*}` may still be undefined at worlds where one
presupposition fails. The paper's full solution uses K/P\*\* (type-flexible
connectives, (142)) which operates at the property level.
Requires `[DecidablePred p.assertion] [DecidablePred q.assertion]` and
decidability of `definedFalse` for `List.filter`. -/
def orPresup [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (p q : PrProp W)
    [DecidablePred p.assertion] [DecidablePred q.assertion]
    [DecidablePred (definedFalse p)] [DecidablePred (definedFalse q)]
    : PrProp W where
  presup := fun w =>
    let closP := closB closer restriction
      (restriction.filter (fun w => decide (p.assertion w))) w
    let closQ := closB closer restriction
      (restriction.filter (fun w => decide (q.assertion w))) w
    let closDfP := closB closer restriction
      (restriction.filter (fun w => decide (definedFalse p w))) w
    let closDfQ := closB closer restriction
      (restriction.filter (fun w => decide (definedFalse q w))) w
    -- Condition 1: at least one direction of and^{K/P*} is defined
    (  (p.presup w ∧ q.presup w ∧ ∀ w' ∈ closP, q.presup w')
     ∨ (q.presup w ∧ p.presup w ∧ ∀ w' ∈ closQ, p.presup w')) ∧
    -- Condition 2: and^{K/P*}(¬assert(P₁))(P₂) is defined
    (q.presup w ∧ ∀ w' ∈ closDfP, q.presup w') ∧
    -- Condition 3: and^{K/P*}(¬assert(P₂))(P₁) is defined
    (p.presup w ∧ ∀ w' ∈ closDfQ, p.presup w')
  assertion := fun w =>
    p.assertion w ∨ q.assertion w

-- ════════════════════════════════════════════════════════════════
-- § Set-based CLOS (non-computable)
-- ════════════════════════════════════════════════════════════════

/-- Set-based CLOS (@cite{sharvit-2025}, (120)).

Definitionally identical to `Counterfactual.closestWorlds` with reordered
parameters: `clos closer R A w = closestWorlds sim R w A` when
`sim.closer = closer`. Both select the non-dominated elements of
`antecedent ∩ restriction` under the similarity ordering centered at w. -/
def clos (closer : W → W → W → Prop)
    (restriction : Set W) (antecedent : Set W) (w : W) : Set W :=
  let pWorlds := antecedent ∩ restriction
  { w' ∈ pWorlds | ∀ w'' ∈ pWorlds, closer w w' w'' ∨ ¬closer w w'' w' }

-- ════════════════════════════════════════════════════════════════
-- § Theorems
-- ════════════════════════════════════════════════════════════════

/-- `orFilter` is inherently symmetric for presupposition projection.

This is Sharvit's observation that K/P's `or` does not distinguish
left from right. -/
theorem orFilter_symmetric (p q : PrProp W) (w : W) :
    (PrProp.orFilter p q).presup w ↔ (PrProp.orFilter q p).presup w := by
  simp only [PrProp.orFilter]
  tauto

/-- K/P*'s inner presupposition (CLOS) entails K/P's inner presupposition
(local) when the evaluation world is in CLOS.

If CLOS-closest p-worlds all satisfy q.presup (K/P* condition), and w is
among them (hw), then q.presup w — which is what K/P checks locally.

The hypothesis `hw` holds automatically with trivial similarity when
w ∈ restriction and p.assertion w, since `trivialCloser` never
dominates any world. Without it, the theorem is false: a non-trivial
ordering can exclude w from CLOS even when p(w). -/
theorem kpstar_presup_implies_kp_presup [DecidableEq W]
    (closer : W → W → W → Bool) (restriction : List W)
    (p : PrProp W) (q : PrProp W) (w : W)
    [DecidablePred p.assertion]
    (hp : p.assertion w)
    (hw : w ∈ closB closer restriction
      (restriction.filter (fun w => decide (p.assertion w))) w) :
    (ifPresup closer restriction p q).presup w →
    (ifKP restriction p q).presup w := by
  intro ⟨hpresup, hall⟩
  exact ⟨hpresup, fun _ => hall w hw⟩

/-- The converse fails: K/P's local presupposition does NOT entail K/P*'s
global CLOS presupposition. This is the Rooth-Partee gap.

Witness: w₀ where p is false and q.presup holds (K/P vacuously satisfied),
but some p-world w₁ has q.presup = false (K/P* fails globally). -/
theorem kp_presup_does_not_imply_kpstar :
    ∃ (W : Type) (_ : DecidableEq W) (restriction : List W)
      (p : PrProp W) (q : PrProp W)
      (_ : DecidablePred p.assertion)
      (w : W),
      (ifKP restriction p q).presup w ∧
      ¬(ifPresup trivialCloser restriction p q).presup w := by
  refine ⟨Bool, inferInstance, [false, true],
    ⟨fun _ => True, fun b => b = true⟩,
    ⟨fun _ => False, fun _ => True⟩,
    inferInstance,
    false, ?_, ?_⟩
  · exact ⟨trivial, fun h => Bool.noConfusion h⟩
  · intro ⟨_, hall⟩
    have := hall true (by simp [closB, trivialCloser, List.filter])
    exact this

end Semantics.Conditionals.Presuppositional
