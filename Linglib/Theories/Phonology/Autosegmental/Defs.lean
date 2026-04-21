import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.Featural.Geometry
import Linglib.Core.Time.Interval.Basic

/-!
# Autosegmental Representations
@cite{goldsmith-1976} @cite{sagey-1986}

Autosegmental phonology adds **feature sharing** to segmental
representations: when adjacent segments share a geometric node's features, they
are linked to a single autosegmental element on that node's tier. This module
builds on the feature geometry (`FeatureGeometry.lean`) and segment type
(`Features.lean`) to provide feature agreement predicates,
autosegmental representations with consistency checking, spread/delink
operations, and a temporal derivation of the no-crossing constraint
(@cite{sagey-1986} §5.3) including the negative argument against
simultaneity (§5.2.2).
-/

namespace Phonology.Autosegmental

open Phonology (Segment Feature FeatureVal)
open Phonology.FeatureGeometry (GeomNode)

-- ============================================================================
-- § 1: Feature Agreement
-- ============================================================================

/-- Do `s1` and `s2` agree on all features dominated by node `n`? -/
def agreeAt (s1 s2 : Segment) (n : GeomNode) : Bool :=
  n.features.all fun f => s1.spec f == s2.spec f

/-- Place assimilation: agreement on all place features. -/
def placeAssimilation (s1 s2 : Segment) : Bool := agreeAt s1 s2 .place

/-- Total assimilation: agreement on all supralaryngeal features. -/
def totalAssimilation (s1 s2 : Segment) : Bool := agreeAt s1 s2 .supralaryngeal

-- ============================================================================
-- § 2: Feature Sharing
-- ============================================================================

/-- Segments at positions `left` and `left + 1` share all features
    dominated by `node`. -/
structure Sharing where
  left : Nat
  node : GeomNode
  deriving DecidableEq, Repr

-- ============================================================================
-- § 3: Autosegmental Representation
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
-- § 4: Operations
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

-- ============================================================================
-- § 4a: Feature Spreading
-- ============================================================================

/-- Replace all features under geometric node `n` in `tgt` with `src`'s values.
    This models autosegmental node replacement: when a place node spreads,
    the entire node (including unspecified features) is copied, not just
    the specified ones. -/
def copyFeaturesUnder (tgt src : Segment) (n : GeomNode) : Segment where
  spec f := if decide (f.DominatedBy n) then src.spec f else tgt.spec f

/-- Spread node `n` from position `pos + 1` onto position `pos`, replacing
    the target's features under `n` with the trigger's values and recording
    the sharing link. -/
def AutosegRep.spreadFeatures (r : AutosegRep) (pos : Nat) (n : GeomNode) :
    AutosegRep :=
  match r.segments[pos]?, r.segments[pos + 1]? with
  | some tgt, some src =>
    let newTgt := copyFeaturesUnder tgt src n
    { segments := r.segments.set pos newTgt
      sharing := ⟨pos, n⟩ :: r.sharing }
  | _, _ => r

/-- On a filtered list, if the filter predicate makes the if-branch select the
    same value being compared, every element passes BEq self-comparison. -/
private theorem all_filter_if_beq_self {α β : Type} [BEq β] [LawfulBEq β]
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

-- ============================================================================
-- § 5: Verification Theorems
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

/-- Place assimilation checks 14 features (the place node's natural class). -/
theorem place_assimilation_checks_14 :
    GeomNode.place.features.length = 14 := by native_decide

/-- Total assimilation checks 16 features (the supralaryngeal node's natural class,
    including [nasal] via the soft palate node). -/
theorem total_assimilation_checks_16 :
    GeomNode.supralaryngeal.features.length = 16 := by native_decide

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

-- ============================================================================
-- § 6: Temporal Tiers and the No-Crossing Constraint
-- ============================================================================

/-! ### Temporal derivation of the No-Crossing Constraint

@cite{sagey-1986} §5.3 derives the ban on crossing association lines from
temporal precedence rather than stipulating it as a well-formedness condition.

The key move is choosing the right temporal relation for association lines.
Simultaneity (identity of time points) is too strong — it predicts that
contour segments and geminates are impossible, since two distinct elements
cannot both be identical to the same time point (§5.2.2). Overlap is the
correct relation: it is reflexive and symmetric but crucially NOT transitive
(`Interval.overlaps_not_transitive`), which is what allows the NCC proof to
go through via a contradiction chain (§5.2.3, fn. 6).

The derivation (§5.3, p.294): if timing₁ ≺ timing₂ on the timing tier but
melody₂ ≺ melody₁ on the melody tier, the overlap requirements on valid
associations produce a chain melody₂.finish < melody₁.start ≤ timing₁.finish
< timing₂.start ≤ melody₂.finish — a contradiction. Crossing is therefore
logically impossible for valid associations.

This section formalizes the derivation using `Core.Time.Interval` for
temporal intervals and its `precedes`/`overlaps` relations.
-/

section NoCrossing

variable {T : Type*} [LinearOrder T]

open Core.Time (Interval)

/-- A position on an autosegmental tier, occupying a temporal interval. -/
structure TierPosition (T : Type*) [LinearOrder T] where
  interval : Interval T

/-- An association between a timing-tier position and a melody-tier position.
    An association line represents temporal overlap: the melody element is
    realized during the timing position's interval. -/
structure Association (T : Type*) [LinearOrder T] where
  timing : TierPosition T
  melody : TierPosition T

/-- Association validity: the timing and melody intervals must overlap.
    This is the phonetic grounding — an association line means the melodic
    content is realized during the timing slot. -/
def validAssociation (a : Association T) : Prop :=
  a.timing.interval.overlaps a.melody.interval

/-- **Simultaneity contradicts contours** (@cite{sagey-1986} §5.2.2):
    if association required temporal identity (simultaneity), contour
    segments — two distinct melody elements F ≠ G associated to the same
    timing position x — would be impossible, since F = x and G = x
    imply F = G by transitivity. This is Sagey's negative argument for
    why association must be overlap, not identity. -/
theorem simultaneity_no_contours {T : Type*} (t m₁ m₂ : T)
    (h₁ : t = m₁) (h₂ : t = m₂) : m₁ = m₂ :=
  h₁.symm.trans h₂

/-- Two associations cross iff their timing positions are ordered one way
    but their melody positions are ordered the other way.
    Crossing(a₁, a₂) ≡ timing₁ ≺ timing₂ ∧ melody₂ ≺ melody₁. -/
def crosses (a₁ a₂ : Association T) : Prop :=
  a₁.timing.interval.precedes a₂.timing.interval ∧
  a₂.melody.interval.precedes a₁.melody.interval

/-- **No-Crossing Constraint** (@cite{sagey-1986} §5.3, @cite{goldsmith-1976}):
    Two valid associations cannot cross.

    If timing₁ ≺ timing₂, then timing₁.finish < timing₂.start.
    Validity requires timing₁ overlaps melody₁ and timing₂ overlaps melody₂.
    If melodies also cross (melody₂ ≺ melody₁), then melody₂.finish < melody₁.start.

    From timing₁ overlaps melody₁: melody₁.start ≤ timing₁.finish.
    From timing₂ overlaps melody₂: timing₂.start ≤ melody₂.finish.

    Chaining: melody₂.finish < melody₁.start ≤ timing₁.finish < timing₂.start ≤ melody₂.finish.
    This gives melody₂.finish < melody₂.finish — a contradiction. -/
theorem no_crossing (a₁ a₂ : Association T)
    (h₁ : validAssociation a₁) (h₂ : validAssociation a₂) :
    ¬ crosses a₁ a₂ := by
  intro ⟨htime, hmelody⟩
  -- Unpack definitions
  simp only [Interval.precedes] at htime hmelody
  simp only [validAssociation, Interval.overlaps] at h₁ h₂
  obtain ⟨h₁_tm, h₁_mt⟩ := h₁
  obtain ⟨h₂_tm, h₂_mt⟩ := h₂
  -- Chain: melody₂.finish < melody₁.start ≤ timing₁.finish < timing₂.start ≤ melody₂.finish
  have : a₂.melody.interval.finish < a₂.melody.interval.finish :=
    calc a₂.melody.interval.finish
        < a₁.melody.interval.start := hmelody
      _ ≤ a₁.timing.interval.finish := h₁_mt
      _ < a₂.timing.interval.start := htime
      _ ≤ a₂.melody.interval.finish := h₂_tm
  exact lt_irrefl _ this

/-- Crossing is also impossible in the symmetric direction: if timing₂ ≺ timing₁
    and melody₁ ≺ melody₂, the same contradiction arises. -/
theorem no_crossing_symm (a₁ a₂ : Association T)
    (h₁ : validAssociation a₁) (h₂ : validAssociation a₂) :
    ¬ crosses a₂ a₁ :=
  no_crossing a₂ a₁ h₂ h₁

-- ────────────────────────────────────────────────────
-- § 6a: Concrete Demonstrations
-- ────────────────────────────────────────────────────

/-- Helper: build an interval from start and finish with a proof of validity. -/
private def mkInterval (s f : T) (h : s ≤ f) : Interval T := ⟨s, f, h⟩

/-- A geminate consonant: two adjacent timing positions associated to a single
    melodic element. The melodic element's interval spans both timing slots.

    Example: /t/ linked to two C-slots in [atta].

    ```
    C-tier:    C₁    C₂
                \  /
    melody:     t
    ``` -/
def geminate (t1s t1f t2s t2f ms mf : T)
    (h1 : t1s ≤ t1f) (h2 : t2s ≤ t2f) (hm : ms ≤ mf)
    : Association T × Association T :=
  ( ⟨⟨mkInterval t1s t1f h1⟩, ⟨mkInterval ms mf hm⟩⟩,
    ⟨⟨mkInterval t2s t2f h2⟩, ⟨mkInterval ms mf hm⟩⟩ )

/-- A contour tone: one timing position associated to two tonal elements
    sequenced within it. The two tonal elements occupy sub-intervals.

    Example: falling tone HL on a single syllable.

    ```
    timing:     σ
               / \
    tone:     H   L
    ``` -/
def contourTone (ts tf m1s m1f m2s m2f : T)
    (ht : ts ≤ tf) (hm1 : m1s ≤ m1f) (hm2 : m2s ≤ m2f)
    : Association T × Association T :=
  ( ⟨⟨mkInterval ts tf ht⟩, ⟨mkInterval m1s m1f hm1⟩⟩,
    ⟨⟨mkInterval ts tf ht⟩, ⟨mkInterval m2s m2f hm2⟩⟩ )

end NoCrossing

end Phonology.Autosegmental
