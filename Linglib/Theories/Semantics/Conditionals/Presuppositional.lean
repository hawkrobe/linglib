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

- `closB`: Computable closest-worlds selector (= `closestWorldsB`)
- `ifPresup`: K/P* conditional with CLOS-based filtering
- `ifKP`: K/P conditional with local filtering (for comparison)
- `trivialCloser`: Degenerate similarity (all worlds equally close)

-/

namespace Semantics.Conditionals.Presuppositional

open Semantics.Conditionals
open Core.Presupposition
open Core.Proposition

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- § CLOS: Closest-worlds selector
-- ════════════════════════════════════════════════════════════════

/-- Computable CLOS (@cite{sharvit-2025}, (120)).

Selects worlds in `antecedent ∩ restriction` that are not dominated
under the similarity ordering. Same formula as `Counterfactual.closestWorldsB`. -/
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

When the antecedent p has no presupposition, use `PrProp.ofBProp`. -/
def ifPresup [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (p : PrProp W) (q : PrProp W) : PrProp W :=
  { presup := fun w =>
      -- Outer: antecedent defined at w
      p.presup w &&
      -- Inner (CLOS): consequent defined at all closest p-worlds
      let closest := closB closer restriction (restriction.filter p.assertion) w
      closest.all q.presup
  , assertion := fun w =>
      let closest := closB closer restriction (restriction.filter p.assertion) w
      closest.isEmpty || closest.all q.assertion }

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
K/P checks locally at w, K/P* checks globally via CLOS. -/
def ifKP [DecidableEq W] (restriction : List W)
    (p : PrProp W) (q : PrProp W) : PrProp W :=
  { presup := fun w =>
      -- Outer: antecedent defined at w
      p.presup w &&
      -- Inner (LOCAL): if antecedent true at w, consequent defined at w
      (!p.assertion w || q.presup w)
  , assertion := fun _w =>
      let pWorlds := restriction.filter p.assertion
      pWorlds.isEmpty || pWorlds.all q.assertion }

-- ════════════════════════════════════════════════════════════════
-- § Contextual Plausibility and type-flexible disjunction
-- ════════════════════════════════════════════════════════════════

/-- Contextual Plausibility (CP): no uninformative sub-expressions.

A proposition is CP-acceptable in context `c` iff it is neither
trivially true nor trivially false in `c`. -/
def cpAcceptable (c : BProp W) (p : BProp W) : Prop :=
  (∃ w, c w = true ∧ p w = true) ∧ (∃ w, c w = true ∧ p w = false)

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
def definedFalse (p : PrProp W) : BProp W :=
  fun w => p.presup w && !p.assertion w

/-- K/P* presuppositional conjunction (@cite{sharvit-2025}, (127)).

- **Presupposition**: P₁ defined at w, P₂ defined at w, and P₂ defined
  at all CLOS-closest P₁-assertion-worlds.
- **Assertion**: P₁(w) ∧ P₂(w)

This is asymmetric: the CLOS-based check only goes from P₁-worlds to P₂.
The asymmetry mirrors K/P's `andFilter`, but uses CLOS-based rather than
local presupposition checking. -/
def andPresup [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (p q : PrProp W) : PrProp W :=
  { presup := fun w =>
      p.presup w &&
      q.presup w &&
      let closest := closB closer restriction (restriction.filter p.assertion) w
      closest.all q.presup
  , assertion := fun w =>
      p.assertion w && q.assertion w }

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
connectives, (142)) which operates at the property level. -/
def orPresup [DecidableEq W] (closer : W → W → W → Bool)
    (restriction : List W) (p q : PrProp W) : PrProp W :=
  { presup := fun w =>
      -- Condition 1: at least one direction of and^{K/P*} is defined
      ((andPresup closer restriction p q).presup w ||
       (andPresup closer restriction q p).presup w) &&
      -- Condition 2: and^{K/P*}(¬assert(P₁))(P₂) is defined
      (andPresup closer restriction (PrProp.ofBProp (definedFalse p)) q).presup w &&
      -- Condition 3: and^{K/P*}(¬assert(P₂))(P₁) is defined
      (andPresup closer restriction (PrProp.ofBProp (definedFalse q)) p).presup w
  , assertion := fun w =>
      p.assertion w || q.assertion w }

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
    (PrProp.orFilter p q).presup w = (PrProp.orFilter q p).presup w := by
  simp only [PrProp.orFilter]
  cases p.assertion w <;> cases q.assertion w <;>
  cases p.presup w <;> cases q.presup w <;> simp_all

/-- K/P*'s inner presupposition (CLOS) entails K/P's inner presupposition
(local) when the evaluation world is in CLOS.

If CLOS-closest p-worlds all satisfy q.presup (K/P* condition), and w is
among them (hw), then q.presup w = true — which is what K/P checks locally.

The hypothesis `hw` holds automatically with trivial similarity when
w ∈ restriction and p.assertion w = true, since `trivialCloser` never
dominates any world. Without it, the theorem is false: a non-trivial
ordering can exclude w from CLOS even when p(w) = true. -/
theorem kpstar_presup_implies_kp_presup [DecidableEq W]
    (closer : W → W → W → Bool) (restriction : List W)
    (p : PrProp W) (q : PrProp W) (w : W)
    (hp : p.assertion w = true)
    (hw : w ∈ closB closer restriction (restriction.filter p.assertion) w) :
    (ifPresup closer restriction p q).presup w = true →
    (ifKP restriction p q).presup w = true := by
  simp only [ifPresup, ifKP]
  intro h_star
  have h_ppresup : p.presup w = true := by
    revert h_star; cases p.presup w <;> simp
  have h_all : (closB closer restriction (restriction.filter p.assertion) w).all q.presup = true := by
    revert h_star; rw [h_ppresup]; simp
  have h_qpresup : q.presup w = true :=
    List.all_eq_true.mp h_all w hw
  simp [h_ppresup, hp, h_qpresup]

/-- The converse fails: K/P's local presupposition does NOT entail K/P*'s
global CLOS presupposition. This is the Rooth-Partee gap.

Witness: w₀ where p is false and q.presup holds (K/P vacuously satisfied),
but some p-world w₁ has q.presup = false (K/P* fails globally). -/
theorem kp_presup_does_not_imply_kpstar :
    ∃ (W : Type) (_ : DecidableEq W) (restriction : List W)
      (p : PrProp W) (q : PrProp W) (w : W),
      (ifKP restriction p q).presup w = true ∧
      (ifPresup trivialCloser restriction p q).presup w = false := by
  refine ⟨Bool, inferInstance, [false, true],
    ⟨fun _ => true, fun b => b⟩,
    ⟨fun _ => false, fun _ => true⟩, false, ?_, ?_⟩
  · -- K/P presup at false: p.presup true, !p.assertion false = !false = true,
    -- so true && true = true
    native_decide
  · -- K/P* presup at false: p.presup true, but closB returns [true] where
    -- q.presup true = false, so all check fails
    native_decide

end Semantics.Conditionals.Presuppositional
