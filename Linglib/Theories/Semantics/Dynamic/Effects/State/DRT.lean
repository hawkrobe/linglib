/-
# Discourse Representation Theory (Kamp 1981; Kamp & Reyle 1993)
@cite{kamp-1981} @cite{kamp-reyle-1993}

Discourse Representation Theory (DRT), the pioneering framework
for dynamic semantics using Discourse Representation Structures (DRSs).

## Key Ideas

In DRT:
- Sentences build DRSs (boxes) with discourse referents and conditions
- DRSs can be embedded in each other (subordination)
- Accessibility: referents in higher boxes accessible to lower boxes
- Model-theoretic interpretation via embedding functions

## DRS Structure

A DRS K = ⟨U, Con⟩ where:
- U is a set of discourse referents
- Con is a set of conditions

## Accessibility

Referent x is accessible from position p iff:
- x is introduced in a box dominating p, and
- x is not in the scope of negation/universal

## Layered DRT (LDRT)

@cite{van-der-sandt-maier-2003} extend DRT with content layers: each DRS
condition carries a label (`pr`, `fr`, `imp`) indicating whether it
contributes presuppositional, at-issue, or implicature content. This
enables a unified treatment of denial: the same negation operator targets
different layers depending on the correction context.

See `Core.Semantics.ContentLayer` for the layer type and
`Phenomena.Negation.Denial` for empirical denial data.

-/

import Linglib.Theories.Semantics.Dynamic.Core.Basic
import Linglib.Core.Semantics.ContentLayer

namespace Semantics.Dynamic.DRT

-- TODO: Full DRT implementation (subordination, proper accessibility, etc.)

/--
A Discourse Representation Structure (DRS).

Note: This is a simplified representation. Full DRT would have
recursive structure with embedded DRSs.
-/
structure DRS (E : Type*) where
  /-- Universe: set of discourse referents introduced -/
  drefs : Set Nat
  /-- Conditions: predicates over the referents -/
  conditions : List ((Nat → E) → Prop)

/--
DRS condition: atomic predicate over discourse referents.
-/
inductive DRSCondition (E : Type*) where
  | atom : ((Nat → E) → Prop) → DRSCondition E
  | neg : DRS E → DRSCondition E
  | impl : DRS E → DRS E → DRSCondition E
  | disj : DRS E → DRS E → DRSCondition E

/--
Full DRS with complex conditions.
-/
structure DRSFull (E : Type*) where
  drefs : Set Nat
  conditions : List (DRSCondition E)

/--
DRS merge: combine two DRSs.

K₁; K₂ combines drefss and conditions.
-/
def DRS.merge {E : Type*} (k1 k2 : DRS E) : DRS E :=
  { drefs := k1.drefs ∪ k2.drefs
  , conditions := k1.conditions ++ k2.conditions }

/--
Accessibility in DRT: a referent is accessible from a condition
if it's in the drefs of a dominating DRS.

This simplified version just checks if x is in the drefs.
-/
def DRS.accessible {E : Type*} (k : DRS E) (x : Nat) : Prop :=
  x ∈ k.drefs

-- Embedding and Truth

/--
An embedding function maps discourse referents to entities.
-/
def Embedding (E : Type*) := Nat → E

/--
Embedding extends another if they agree on shared domain.
-/
def Embedding.extends {E : Type*} (f g : Embedding E) (dom : Set Nat) : Prop :=
  ∀ x ∈ dom, f x = g x

/--
DRS satisfaction: embedding f satisfies DRS K in model M.

Simplified version checking conditions hold.
-/
def DRS.satisfies {E : Type*} (k : DRS E) (f : Embedding E) : Prop :=
  ∀ cond ∈ k.conditions, cond f

-- ════════════════════════════════════════════════════
-- § Layered DRT (@cite{van-der-sandt-maier-2003})
-- ════════════════════════════════════════════════════

open Core.Semantics.ContentLayer

/--
A layered DRS condition: a standard DRS condition tagged with the
content layer it contributes to.

@cite{van-der-sandt-maier-2003}: in LDRT, every condition carries a
label indicating its discourse role. The layer determines how the
condition behaves under denial:
- `pr` conditions survive propositional denial
- `fr` conditions survive presuppositional denial
- `imp` conditions survive implicature denial
-/
structure LayeredCondition (E : Type*) where
  /-- The content layer this condition contributes to -/
  layer : ContentLayer
  /-- The underlying DRS condition -/
  condition : DRSCondition E

/--
A Layered DRS (LDRS): a DRS whose conditions carry content-layer tags.

This is the core data structure of @cite{van-der-sandt-maier-2003}'s
LDRT. A standard DRS is the special case where all conditions are
tagged `fr` (at-issue).
-/
structure LDRS (E : Type*) where
  /-- Universe: discourse referents -/
  drefs : Set Nat
  /-- Layered conditions -/
  conditions : List (LayeredCondition E)

/-- Extract all conditions at a given layer. -/
def LDRS.atLayer {E : Type*} (k : LDRS E) (l : ContentLayer) :
    List (DRSCondition E) :=
  (k.conditions.filter (·.layer == l)).map (·.condition)

/-- Project an LDRS to a standard DRS by stripping layer tags. -/
def LDRS.toDRSFull {E : Type*} (k : LDRS E) : DRSFull E :=
  { drefs := k.drefs
  , conditions := k.conditions.map (·.condition) }

/-- Lift a standard DRS to an LDRS by tagging all conditions as at-issue.

    A plain DRS is an LDRS where everything is `fr`. -/
def DRSFull.toLDRS {E : Type*} (k : DRSFull E) : LDRS E :=
  { drefs := k.drefs
  , conditions := k.conditions.map (⟨.atIssue, ·⟩) }

/-- Round-trip: DRSFull → LDRS → DRSFull preserves conditions. -/
theorem LDRS.roundtrip_conditions {E : Type*} (k : DRSFull E) :
    (k.toLDRS.toDRSFull).conditions = k.conditions := by
  simp only [toDRSFull, DRSFull.toLDRS, List.map_map]
  exact List.map_id _

/-- LDRS merge: combine two layered DRSs, preserving layer tags. -/
def LDRS.merge {E : Type*} (k1 k2 : LDRS E) : LDRS E :=
  { drefs := k1.drefs ∪ k2.drefs
  , conditions := k1.conditions ++ k2.conditions }

/-- The offensive conditions of an LDRS with respect to a correction:
    those whose layer is in the offensive set.

    In denial, these are the conditions that get retracted. The
    non-offensive conditions are resolved normally (forward anaphora
    into the post-correction context). -/
def LDRS.offensiveConditions {E : Type*} (k : LDRS E)
    (offLayers : List ContentLayer) : List (LayeredCondition E) :=
  k.conditions.filter (offLayers.contains ·.layer)

/-- The surviving conditions after denial: those NOT at offensive layers. -/
def LDRS.survivingConditions {E : Type*} (k : LDRS E)
    (offLayers : List ContentLayer) : List (LayeredCondition E) :=
  k.conditions.filter (!offLayers.contains ·.layer)

/-- Offensive + surviving = all conditions (partition). -/
theorem LDRS.offensive_surviving_partition {E : Type*} (k : LDRS E)
    (offLayers : List ContentLayer) :
    (k.offensiveConditions offLayers).length +
    (k.survivingConditions offLayers).length = k.conditions.length := by
  simp only [offensiveConditions, survivingConditions]
  induction k.conditions with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter]
    cases offLayers.contains hd.layer <;> simp_all <;> omega

-- ════════════════════════════════════════════════════
-- § Assertion vs Denial: Monotonicity
-- ════════════════════════════════════════════════════

/-! The paper's deepest architectural claim: assertion is monotonic
    (merge only adds conditions), while denial is non-monotonic (surviving
    conditions are a subset of the original). Standard DRT update is
    monotonic; denial is the ONLY operation that removes information from
    the discourse context. -/

/-- Assertion (merge) is monotonic: the result has at least as many
    conditions as the original LDRS. -/
theorem merge_monotonic {E : Type*} (k1 k2 : LDRS E) :
    k1.conditions.length ≤ (k1.merge k2).conditions.length := by
  simp only [LDRS.merge, List.length_append]
  omega

/-- Denial (surviving conditions) is non-monotonic: the result has at most
    as many conditions as the original LDRS. -/
theorem denial_nonmonotonic {E : Type*} (k : LDRS E)
    (offLayers : List ContentLayer) :
    (k.survivingConditions offLayers).length ≤ k.conditions.length := by
  exact List.length_filter_le _ _

end Semantics.Dynamic.DRT
