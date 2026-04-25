import Linglib.Theories.Semantics.Dynamic.Boxes.Accessibility
import Linglib.Core.Semantics.ContentLayer
import Mathlib.Data.Set.Basic

/-!
# Discourse Representation Theory
@cite{kamp-1981} @cite{kamp-reyle-1993}

Discourse Representation Theory (DRT), the pioneering framework for dynamic
semantics using Discourse Representation Structures (DRSs).

## Unified DRS Representation

This module builds on the canonical `DRSExpr` type from
`Core.DRSExpr`, which captures the full recursive syntax of
@cite{kamp-reyle-1993} Def 1.4.1:

- `DRSExpr.box` = K&R's `⟨U, Con⟩` (universe + conditions)
- `DRSExpr.neg` = negated condition (`¬K`)
- `DRSExpr.impl` = implicative condition (`K₁ ⇒ K₂`)
- `DRSExpr.disj` = disjunctive condition (`K₁ ∨ K₂`)
- `DRSExpr.seq` = discourse sequencing (`K₁ ; K₂`)

Syntactic operations (`adr`, `occurs`, `acc`, `isFree`, `isProper`) are
defined in `Core.DRSExpr`. Semantic interpretation (`interp`,
`mergingLemma`, `reduce`) is defined in `Core.Accessibility`.

## K&R Model Theory (Def 1.2.1)

A `KRModel` formalizes @cite{kamp-reyle-1993}'s Definition 1.2.1: a triple
⟨U_M, Name_M, Pred_M⟩ providing the universe, name bearers, and predicate
extensions for evaluating DRSs.

## Subordination (Def 2.1.2)

The `subordinate` relation captures when one DRS is structurally embedded
inside another — the key structural relation governing anaphoric accessibility
in @cite{kamp-reyle-1993} Ch 2.

## Layered DRT (LDRT)

@cite{van-der-sandt-maier-2003} extend DRT with content layers: each DRS
condition carries a label (`pr`, `fr`, `imp`) indicating whether it
contributes presuppositional, at-issue, or implicature content. This
enables a unified treatment of denial.
-/

namespace Semantics.Dynamic.DRT

open Semantics.Dynamic.Core.Accessibility
open Semantics.Dynamic.Core
open Semantics.Dynamic.Core (Assignment)
open Semantics.Dynamic.Core.WeakestPrecondition
open Core.Semantics.ContentLayer

-- ════════════════════════════════════════════════════
-- § 1. K&R Model Theory (@cite{kamp-reyle-1993}, Def 1.2.1)
-- ════════════════════════════════════════════════════

/-- A model for a DRS vocabulary, following @cite{kamp-reyle-1993} Def 1.2.1.

A model M for vocabulary V is a triple ⟨U_M, Name_M, Pred_M⟩:
- `U_M`: a non-empty set of individuals (the universe)
- `Name_M`: maps individual constants to their bearers in `U_M`
- `Pred_M`: maps predicate constants to their extensions

In our formalization, names and predicates are both identified by `Nat`
indices (matching `DRSExpr`'s `atom` constructor). -/
structure KRModel (E : Type*) where
  /-- Name interpretation: maps name indices to their bearers. -/
  names : Nat → E
  /-- Predicate interpretation: maps relation indices to truth on entity lists.
      This is exactly a `RelInterp E` from `Core.Accessibility`. -/
  preds : RelInterp E

/-- Extract a `RelInterp` from a K&R model for use with `interp`. -/
def KRModel.toRelInterp {E : Type*} (M : KRModel E) : RelInterp E := M.preds

/-- A DRS K is true in model M iff there is an embedding (assignment) that
verifies all conditions (@cite{kamp-reyle-1993} Def 1.4.5). -/
def trueIn {E : Type*} (M : KRModel E) (K : DRSExpr) : Prop :=
  ∃ g : Assignment E, wp (interp M.preds K) (λ _ => True) g

-- ════════════════════════════════════════════════════
-- § 2. Subordination (@cite{kamp-reyle-1993}, Def 2.1.2)
-- ════════════════════════════════════════════════════

/-- `K₁` is *immediately subordinate* to `K₂` if `K₂`'s conditions contain
`K₁` as a component of a complex condition (negation, implication, or
disjunction). Matches @cite{kamp-reyle-1993} Def 2.1.2(i). -/
inductive ImmSubordinate : DRSExpr → DRSExpr → Prop where
  /-- K is immediately subordinate to [... | ¬K, ...] -/
  | neg (K : DRSExpr) (drefs : List Nat) (pre post : List DRSExpr) :
      ImmSubordinate K (.box drefs (pre ++ [.neg K] ++ post))
  /-- K₁ is immediately subordinate to [... | K₁ ⇒ K₂, ...] -/
  | implLeft (K₁ K₂ : DRSExpr) (drefs : List Nat) (pre post : List DRSExpr) :
      ImmSubordinate K₁ (.box drefs (pre ++ [.impl K₁ K₂] ++ post))
  /-- K₂ is immediately subordinate to [... | K₁ ⇒ K₂, ...] -/
  | implRight (K₁ K₂ : DRSExpr) (drefs : List Nat) (pre post : List DRSExpr) :
      ImmSubordinate K₂ (.box drefs (pre ++ [.impl K₁ K₂] ++ post))
  /-- K₁ is immediately subordinate to [... | K₁ ∨ K₂, ...] -/
  | disjLeft (K₁ K₂ : DRSExpr) (drefs : List Nat) (pre post : List DRSExpr) :
      ImmSubordinate K₁ (.box drefs (pre ++ [.disj K₁ K₂] ++ post))
  /-- K₂ is immediately subordinate to [... | K₁ ∨ K₂, ...] -/
  | disjRight (K₁ K₂ : DRSExpr) (drefs : List Nat) (pre post : List DRSExpr) :
      ImmSubordinate K₂ (.box drefs (pre ++ [.disj K₁ K₂] ++ post))

/-- `K₁` is *subordinate* to `K₂` (written K₁ < K₂) if there is a chain
of immediate subordination from K₁ to K₂. This is the transitive closure
of `ImmSubordinate`. Matches @cite{kamp-reyle-1993} Def 2.1.2(ii). -/
inductive Subordinate : DRSExpr → DRSExpr → Prop where
  /-- One step of immediate subordination. -/
  | imm {K₁ K₂ : DRSExpr} : ImmSubordinate K₁ K₂ → Subordinate K₁ K₂
  /-- Transitivity: if K₁ < K₃ and K₃ < K₂, then K₁ < K₂. -/
  | trans {K₁ K₂ K₃ : DRSExpr} : Subordinate K₁ K₃ → Subordinate K₃ K₂ → Subordinate K₁ K₂

/-- `K₁` is *weakly subordinate* to `K₂` (written K₁ ≤ K₂) iff K₁ = K₂
or K₁ < K₂. Matches @cite{kamp-reyle-1993} Def 2.1.2(iii). -/
def WeakSubordinate (K₁ K₂ : DRSExpr) : Prop :=
  K₁ = K₂ ∨ Subordinate K₁ K₂

-- ════════════════════════════════════════════════════
-- § 3. Layered DRT (@cite{van-der-sandt-maier-2003})
-- ════════════════════════════════════════════════════

/-- A DRS condition tagged with its content layer.

@cite{van-der-sandt-maier-2003}: in LDRT, every condition carries a
label indicating its discourse role. Uses `DRSExpr` as the condition type,
unifying with the canonical DRS representation from `Core.Accessibility`. -/
structure TaggedCondition where
  /-- The content layer this condition contributes to. -/
  layer : ContentLayer
  /-- The underlying DRS condition. -/
  condition : DRSExpr
  deriving Repr

/-- A Layered DRS (LDRS): a DRS whose conditions carry content-layer tags.

This is the core data structure of @cite{van-der-sandt-maier-2003}'s
LDRT. A standard DRS is the special case where all conditions are
tagged `atIssue`. -/
structure LDRS where
  /-- Universe: discourse referent indices. -/
  drefs : List Nat
  /-- Layered conditions. -/
  conditions : List TaggedCondition
  deriving Repr

/-- Convert an LDRS to a plain `DRSExpr` by stripping layer tags. -/
def LDRS.toDRSExpr (k : LDRS) : DRSExpr :=
  .box k.drefs (k.conditions.map (·.condition))

/-- Lift a `DRSExpr.box` to an LDRS by tagging all conditions as at-issue.

A plain DRS is an LDRS where everything is `atIssue`. -/
def DRSExpr.toLDRS : DRSExpr → LDRS
  | .box drefs conds => { drefs, conditions := conds.map (⟨.atIssue, ·⟩) }
  | K => { drefs := [], conditions := [⟨.atIssue, K⟩] }

/-- Extract all conditions at a given layer. -/
def LDRS.atLayer (k : LDRS) (l : ContentLayer) : List DRSExpr :=
  (k.conditions.filter (·.layer == l)).map (·.condition)

/-- LDRS merge: combine two layered DRSs, preserving layer tags. -/
def LDRS.merge (k1 k2 : LDRS) : LDRS :=
  { drefs := k1.drefs ++ k2.drefs
  , conditions := k1.conditions ++ k2.conditions }

/-- The offensive conditions of an LDRS with respect to a correction:
those whose layer is in the offensive set.

In denial, these are the conditions that get retracted. -/
def LDRS.offensiveConditions (k : LDRS)
    (offLayers : List ContentLayer) : List TaggedCondition :=
  k.conditions.filter (offLayers.contains ·.layer)

/-- The surviving conditions after denial: those NOT at offensive layers. -/
def LDRS.survivingConditions (k : LDRS)
    (offLayers : List ContentLayer) : List TaggedCondition :=
  k.conditions.filter (!offLayers.contains ·.layer)

-- ════════════════════════════════════════════════════
-- § 4. Assertion vs Denial: Monotonicity
-- ════════════════════════════════════════════════════

/-! The paper's deepest architectural claim: assertion is monotonic
(merge only adds conditions), while denial is non-monotonic (surviving
conditions are a subset of the original). Standard DRT update is
monotonic; denial is the ONLY operation that removes information from
the discourse context. -/

/-- Offensive + surviving = all conditions (partition). -/
theorem LDRS.offensive_surviving_partition (k : LDRS)
    (offLayers : List ContentLayer) :
    (k.offensiveConditions offLayers).length +
    (k.survivingConditions offLayers).length = k.conditions.length := by
  simp only [offensiveConditions, survivingConditions]
  induction k.conditions with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter]
    cases offLayers.contains hd.layer <;> simp_all <;> omega

/-- Assertion (merge) is monotonic: the result has at least as many
conditions as the original LDRS. -/
theorem merge_monotonic (k1 k2 : LDRS) :
    k1.conditions.length ≤ (k1.merge k2).conditions.length := by
  simp only [LDRS.merge, List.length_append]
  omega

/-- Denial (surviving conditions) is non-monotonic: the result has at most
as many conditions as the original LDRS. -/
theorem denial_nonmonotonic (k : LDRS)
    (offLayers : List ContentLayer) :
    (k.survivingConditions offLayers).length ≤ k.conditions.length := by
  exact List.length_filter_le _ _

-- ════════════════════════════════════════════════════
-- § 5. Semantic Interpretation Bridge
-- ════════════════════════════════════════════════════

/-- Interpret an LDRS by stripping tags and using `interp` from
`Core.Accessibility`. This gives the at-issue truth conditions;
presuppositional and implicature content must be handled separately
by the content-layer machinery. -/
def LDRS.interp {E : Type*} (rels : RelInterp E) (k : LDRS) :
    DRS (Assignment E) :=
  Semantics.Dynamic.Core.Accessibility.interp rels k.toDRSExpr

/-- Round-trip: `box → toLDRS → toDRSExpr` preserves conditions. -/
theorem toLDRS_toDRSExpr_conditions (drefs : List Nat) (conds : List DRSExpr) :
    (DRSExpr.toLDRS (.box drefs conds)).toDRSExpr =
    .box drefs conds := by
  simp only [DRSExpr.toLDRS, LDRS.toDRSExpr, List.map_map]
  congr 1
  exact List.map_id _

-- ════════════════════════════════════════════════════
-- § 6. Directed Reverse Anaphora (RA*)
-- ════════════════════════════════════════════════════

/-! @cite{van-der-sandt-maier-2003} §4.3: given a set of offensive
layers (computed by `Off` from `Core.Semantics.ContentLayer`), RA*
partitions the LDRS conditions: surviving conditions remain in the
main DRS, offensive conditions are moved under negation. -/

/-- Directed reverse anaphora (RA*): move offensive-layer conditions
under negation, preserving non-offensive conditions.

@cite{van-der-sandt-maier-2003} §4.3, def (67). -/
def LDRS.directedRA (k : LDRS) (offLayers : List ContentLayer) : LDRS :=
  let surviving := k.survivingConditions offLayers
  let offensive := k.offensiveConditions offLayers
  { drefs := k.drefs
  , conditions :=
    surviving ++ match offensive with
    | [] => []
    | cs => [⟨.atIssue, .neg (.box [] (cs.map (·.condition)))⟩] }

/-- Denial pipeline: merge correction, then apply RA*.

@cite{van-der-sandt-maier-2003} §4.3: in an assertion-denial-correction
sequence ⟨σᵢ, σᵢ₊₁, σᵢ₊₂⟩, the correction is merged with the
discourse state, then RA* retracts the offensive layers. -/
def LDRS.denialUpdate (state : LDRS) (correction : LDRS)
    (offLayers : List ContentLayer) : LDRS :=
  (state.merge correction).directedRA offLayers

/-- RA* always preserves discourse referents — denial retracts conditions,
not referent introductions. This matches the paper's treatment: drefs
introduced by σ₁ remain available for anaphoric reference even after
denial (@cite{van-der-sandt-maier-2003} §3.6, ex. 51: "A man jumped
off the bridge. He didn't jump, he was pushed."). -/
theorem LDRS.directedRA_preserves_drefs (k : LDRS) (offLayers : List ContentLayer) :
    (k.directedRA offLayers).drefs = k.drefs := rfl

end Semantics.Dynamic.DRT
