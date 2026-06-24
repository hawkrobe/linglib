/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segment
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Autosegmental feature sharing

Autosegmental phonology adds **feature sharing** to segmental
representations: when adjacent segments share a geometric node's features, they
are linked to a single autosegmental element on that node's tier. This is the
**feature-geometry** representation (segments plus feature-sharing
specifications over geometric nodes). Feature geometry is an *extension of*
autosegmental phonology ([clements-1985], [clements-hume-1995]): spreading is
the association of one node to multiple anchors ([clements-1985]). So this
`SharingRep` is a flattened, adjacency-indexed special case of the bipartite
tier-association object `AR` (`Graph.lean` / `AR.lean`) — a single segment
backbone with a feature-agreement-consistency law, not two materialized tiers.
A faithful re-grounding of feature spreading as `AR` association is future work;
for now the two are kept as separate carriers. It builds on
the feature geometry (`Segment.lean`) and segment type
(`Segment.lean`) to provide feature agreement predicates,
feature-sharing representations with consistency checking, and spread/delink
operations.

## Main definitions

* `agreeAt`, `placeAssimilation`, `totalAssimilation` — feature agreement
  predicates over a geometric node.
* `Sharing`, `SharingRep` — feature-sharing representations: a segmental
  backbone plus a list of feature-sharing specifications.
* `SharingRep.inBounds`, `SharingRep.consistent` — well-formedness checks.
* `SharingRep.spread`, `SharingRep.delink`, `SharingRep.spreadFeatures` —
  atomic operations on feature-sharing representations.
* `copyFeaturesUnder` — replace features under a geometric node.

The Sagey-1986 interval-overlap derivation of the No-Crossing Constraint
(`TierPosition`/`Association`/`no_crossing`/…) lives with its paper in
`Studies/Sagey1986.lean`, its sole consumer.

## Implementation notes

The temporal NCC derivation chooses overlap (reflexive, symmetric, not
transitive) over simultaneity as the association relation. Simultaneity
would predict that contour segments and geminates are impossible, since
two distinct elements cannot be identical to the same time point.

## References

* [goldsmith-1976] — autosegmental phonology, original NCC.
* [clements-1985] — feature geometry as an extension of autosegmental
  phonology; spreading = association of one node to multiple anchors.
* [clements-hume-1995] — handbook synthesis of autosegmental phonology
  and feature geometry.
* [sagey-1986] — temporal derivation of NCC and the negative
  argument against simultaneity.
-/

namespace Autosegmental

open Phonology (Segment Feature FeatureVal)
open Phonology.FeatureGeometry (GeomNode)

/-! ### Feature agreement -/

/-- Do `s1` and `s2` agree on all features dominated by node `n`? -/
def agreeAt (s1 s2 : Segment) (n : GeomNode) : Bool :=
  n.features.all fun f => s1.spec f == s2.spec f

/-- Place assimilation: agreement on all place features. -/
def placeAssimilation (s1 s2 : Segment) : Bool := agreeAt s1 s2 .place

/-- Total assimilation: agreement on all supralaryngeal features. -/
def totalAssimilation (s1 s2 : Segment) : Bool := agreeAt s1 s2 .supralaryngeal

/-! ### Feature sharing -/

/-- Segments at positions `left` and `left + 1` share all features
    dominated by `node`. -/
structure Sharing where
  left : Nat
  node : GeomNode
  deriving DecidableEq, Repr

/-! ### Autosegmental representation -/

/-- An autosegmental representation: a sequence of segments with an explicit
    record of which adjacent pairs share features under which geometric nodes. -/
structure SharingRep where
  segments : List Segment
  sharing  : List Sharing

/-- Are all sharing specifications within bounds? -/
def SharingRep.inBounds (r : SharingRep) : Bool :=
  r.sharing.all fun s => decide (s.left + 1 < r.segments.length)

/-- Is each sharing specification consistent with the segments' feature values? -/
def SharingRep.consistent (r : SharingRep) : Bool :=
  r.sharing.all fun sh =>
    match r.segments[sh.left]?, r.segments[sh.left + 1]? with
    | some seg1, some seg2 => agreeAt seg1 seg2 sh.node
    | _, _ => false

/-! ### Operations -/

/-- Spread node `n` rightward from position `pos`. -/
def SharingRep.spread (r : SharingRep) (pos : Nat) (n : GeomNode) :
    SharingRep :=
  { r with sharing := ⟨pos, n⟩ :: r.sharing }

/-- Remove sharing at position `pos` for node `n`. -/
def SharingRep.delink (r : SharingRep) (pos : Nat) (n : GeomNode) :
    SharingRep :=
  { r with sharing := r.sharing.filter fun s =>
      !(s.left == pos && s.node == n) }

/-! ### Feature spreading -/

/-- Replace all features under geometric node `n` in `tgt` with `src`'s values.
    This models **node spreading** specifically ([clements-1985]'s class-node
    assimilation): the entire node — including features `src` leaves
    unspecified — is copied. (The node-spreading analysis; single-feature
    spreading and underspecification-sensitive variants behave differently.) -/
def copyFeaturesUnder (tgt src : Segment) (n : GeomNode) : Segment where
  spec f := if decide (f.DominatedBy n) then src.spec f else tgt.spec f

/-- Spread node `n` from position `pos + 1` onto position `pos`, replacing
    the target's features under `n` with the trigger's values and recording
    the sharing link. -/
def SharingRep.spreadFeatures (r : SharingRep) (pos : Nat) (n : GeomNode) :
    SharingRep :=
  match r.segments[pos]?, r.segments[pos + 1]? with
  | some tgt, some src =>
    let newTgt := copyFeaturesUnder tgt src n
    { segments := r.segments.set pos newTgt
      sharing := ⟨pos, n⟩ :: r.sharing }
  | _, _ => r

/-- On a filtered list, if the filter predicate makes the if-branch select the
    same value being compared, every element passes BEq self-comparison. -/
private theorem all_filter_if_beq_self {α β : Type*} [BEq β] [LawfulBEq β]
    (l : List α) (p : α → Bool) (g h : α → β) :
    (l.filter p).all (fun x => (if p x then g x else h x) == g x) = true := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    split
    · simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨by simp_all, ih⟩
    · exact ih

/-- After copying features under node `n`, the result agrees with the source
    at that node. -/
theorem copyFeaturesUnder_agreeAt (tgt src : Segment) (n : GeomNode) :
    agreeAt (copyFeaturesUnder tgt src n) src n = true := by
  simp only [agreeAt, copyFeaturesUnder, GeomNode.features]
  exact all_filter_if_beq_self Feature.allFeatures
    (fun f => decide (f.DominatedBy n)) src.spec tgt.spec

/-! ### Verification theorems -/

private theorem list_all_beq_self {α : Type*} [BEq α] [LawfulBEq α]
    (l : List Feature) (f : Feature → α) :
    l.all (fun x => f x == f x) = true := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.all_cons]

/-- Agreement is reflexive. -/
theorem agreeAt_refl (s : Segment) (n : GeomNode) :
    agreeAt s s n = true :=
  list_all_beq_self n.features s.spec

/-- Place assimilation checks 14 features (the place node's natural class). -/
theorem place_assimilation_checks_14 :
    GeomNode.place.features.length = 14 := by decide

/-- Total assimilation checks 16 features (the supralaryngeal node's natural class,
    including [nasal] via the soft palate node). -/
theorem total_assimilation_checks_16 :
    GeomNode.supralaryngeal.features.length = 16 := by decide

private theorem filter_all_pass (l : List Sharing) (p : Sharing → Bool)
    (h : l.all p = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.filter_cons, h1, ↓reduceIte]
    exact congrArg (hd :: ·) (ih h2)

/-- Spreading and then delinking returns the original representation when the
    position/node pair was not already present in the sharing list. -/
theorem spread_delink_not_present (r : SharingRep) (pos : Nat) (n : GeomNode)
    (h : (r.sharing.all fun s => !(s.left == pos && s.node == n)) = true) :
    (r.spread pos n).delink pos n = r := by
  cases r with | mk segs shs =>
  simp only [SharingRep.spread, SharingRep.delink, SharingRep.mk.injEq]
  -- Head ⟨pos, n⟩ fails the filter: !(pos == pos && n == n) = false
  have hnn : (n == n) = true := by cases n <;> rfl
  have hcond : (!(pos == pos && n == n)) = false := by rw [beq_self_eq_true, hnn]; rfl
  rw [List.filter_cons, if_neg (by rw [hcond]; decide)]
  exact ⟨trivial, filter_all_pass shs _ h⟩


end Autosegmental
