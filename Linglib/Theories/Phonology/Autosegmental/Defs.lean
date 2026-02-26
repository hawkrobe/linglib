import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.FeatureGeometry

/-!
# Autosegmental Representations

Autosegmental phonology (Goldsmith 1976) adds **feature sharing** to segmental
representations: when adjacent segments share a geometric node's features, they
are linked to a single autosegmental element on that node's tier. This module
builds on the feature geometry (`FeatureGeometry.lean`) and segment type
(`Features.lean`) to provide association lines, feature agreement predicates,
autosegmental representations with consistency checking, spread/delink operations,
and OCP violation counting.
-/

namespace Theories.Phonology.Autosegmental

open Theories.Phonology (Segment Feature FeatureVal)
open Theories.Phonology.FeatureGeometry (GeomNode)

-- ============================================================================
-- § 1: Association Lines
-- ============================================================================

/-- An association line connects a source position to a target position
    on an autosegmental tier. -/
structure AssocLine where
  src : Nat
  tgt : Nat
  deriving DecidableEq, BEq, Repr

/-- Association lines do not cross: if src₁ < src₂ then tgt₁ ≤ tgt₂. -/
def noCrossing (lines : List AssocLine) : Bool :=
  lines.all fun l1 => lines.all fun l2 =>
    decide (l1.src < l2.src → l1.tgt ≤ l2.tgt) &&
    decide (l1.tgt < l2.tgt → l1.src ≤ l2.src)

-- ============================================================================
-- § 2: Feature Agreement
-- ============================================================================

/-- Do `s1` and `s2` agree on all features dominated by node `n`? -/
def agreeAt (s1 s2 : Segment) (n : GeomNode) : Bool :=
  n.features.all fun f => s1.spec f == s2.spec f

/-- Place assimilation: agreement on all place features. -/
def placeAssimilation (s1 s2 : Segment) : Bool := agreeAt s1 s2 .place

/-- Total assimilation: agreement on all supralaryngeal features. -/
def totalAssimilation (s1 s2 : Segment) : Bool := agreeAt s1 s2 .supralaryngeal

-- ============================================================================
-- § 3: Feature Sharing
-- ============================================================================

/-- Segments at positions `left` and `left + 1` share all features
    dominated by `node`. -/
structure Sharing where
  left : Nat
  node : GeomNode
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: Autosegmental Representation
-- ============================================================================

/-- An autosegmental representation: a sequence of segments with an explicit
    record of which adjacent pairs share features under which geometric nodes. -/
structure AutosegRep where
  segments : List Segment
  sharing  : List Sharing

/-- Are all sharing specifications within bounds? -/
def AutosegRep.inBounds (r : AutosegRep) : Bool :=
  r.sharing.all fun s => decide (s.left + 1 < r.segments.length)

/-- Is each sharing specification consistent with the segments' feature values? -/
def AutosegRep.consistent (r : AutosegRep) : Bool :=
  r.sharing.all fun sh =>
    match r.segments[sh.left]?, r.segments[sh.left + 1]? with
    | some seg1, some seg2 => agreeAt seg1 seg2 sh.node
    | _, _ => false

-- ============================================================================
-- § 5: Operations
-- ============================================================================

/-- Spread node `n` rightward from position `pos`. -/
def AutosegRep.spread (r : AutosegRep) (pos : Nat) (n : GeomNode) :
    AutosegRep :=
  { r with sharing := ⟨pos, n⟩ :: r.sharing }

/-- Remove sharing at position `pos` for node `n`. -/
def AutosegRep.delink (r : AutosegRep) (pos : Nat) (n : GeomNode) :
    AutosegRep :=
  { r with sharing := r.sharing.filter fun s =>
      !(s.left == pos && s.node == n) }

/-- Remove all sharing involving node `n`. -/
def AutosegRep.delinkAll (r : AutosegRep) (n : GeomNode) : AutosegRep :=
  { r with sharing := r.sharing.filter fun s => s.node != n }

-- ============================================================================
-- § 6: OCP
-- ============================================================================

/-- Count OCP violations for node `n`: adjacent segments that agree on all
    features dominated by `n`. Returns `Nat` matching `OT/Core.lean`'s
    `NamedConstraint.eval`. -/
def ocpViolations (segs : List Segment) (n : GeomNode) : Nat :=
  (segs.zip (segs.drop 1)).filter (fun (s1, s2) => agreeAt s1 s2 n) |>.length

-- ============================================================================
-- § 7: Verification Theorems
-- ============================================================================

private theorem list_all_beq_self {α : Type} [BEq α] [LawfulBEq α]
    (l : List Feature) (f : Feature → α) :
    l.all (fun x => f x == f x) = true := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.all_cons]

/-- Agreement is reflexive. -/
theorem agreeAt_refl (s : Segment) (n : GeomNode) :
    agreeAt s s n = true :=
  list_all_beq_self n.features s.spec

/-- Place assimilation checks 12 features (the place node's natural class). -/
theorem place_assimilation_checks_12 :
    GeomNode.place.features.length = 12 := by native_decide

/-- Total assimilation checks 13 features (the supralaryngeal node's natural class). -/
theorem total_assimilation_checks_13 :
    GeomNode.supralaryngeal.features.length = 13 := by native_decide

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
theorem spread_delink_not_present (r : AutosegRep) (pos : Nat) (n : GeomNode)
    (h : (r.sharing.all fun s => !(s.left == pos && s.node == n)) = true) :
    (r.spread pos n).delink pos n = r := by
  cases r with | mk segs shs =>
  simp only [AutosegRep.spread, AutosegRep.delink, AutosegRep.mk.injEq]
  -- Head ⟨pos, n⟩ fails the filter: !(pos == pos && n == n) = false
  have hnn : (n == n) = true := by cases n <;> rfl
  have hcond : (!(pos == pos && n == n)) = false := by rw [beq_self_eq_true, hnn]; rfl
  rw [List.filter_cons, if_neg (by rw [hcond]; decide)]
  exact ⟨trivial, filter_all_pass shs _ h⟩

end Theories.Phonology.Autosegmental
