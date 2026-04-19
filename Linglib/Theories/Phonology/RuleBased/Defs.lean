import Linglib.Theories.Phonology.Featural.Features

/-!
# SPE Phonological Rules

Rule-based phonology following the SPE formalism,
as presented in @cite{hayes-2009} *Introductory Phonology*, Chapter 6.

The core notation is `A → B / C __ D`: a segment matching natural class A
undergoes structural change B when preceded by context C and followed by
context D.

**Design**: We reuse `Segment` (a partial feature specification) as both
concrete segment and natural class descriptor. An underspecified segment
(many features `none`) IS a natural class — no separate pattern type needed.

This module provides:
- Segment construction and natural class matching utilities
- `PhonRule`: the SPE rule type (`A → B / C __ D`)
- Rule application to segment strings (left-to-right scan)
- Ordered derivation (rule cascade)
- Example rules from Hayes Ch 6

@cite{hayes-2009}
-/

-- ============================================================================
-- § 1: Segment Utilities (in Phonology to extend Segment)
-- ============================================================================

namespace Phonology

/-- Create a segment from a list of (feature, value) pairs.
    Unmentioned features are unspecified (`none`), giving natural class
    semantics: `ofSpecs [(continuant, false)]` matches all [-cont] segments. -/
def Segment.ofSpecs (specs : List (Feature × Bool)) : Segment where
  spec f := match specs.find? (λ p => p.1 == f) with
    | some (_, v) => some v
    | none => none

/-- Does segment `s` match pattern `p`? True when every feature specified
    in `p` has the same value in `s`. An unspecified feature in `p`
    matches anything (natural class semantics).

    Hayes §6.2: "The target of a rule identifies a *natural class* of
    sounds — all segments sharing a particular set of feature values." -/
def Segment.matchesPattern (s : Segment) (p : Segment) : Bool :=
  Feature.allFeatures.all λ f =>
    match p.spec f with
    | none => true
    | some v => s.spec f == some v

/-- Apply feature changes from `change` to `s`: specified features in
    `change` override those in `s`, unspecified features are preserved.

    This implements the structural change `A → B` when B is a partial
    specification — only the mentioned features change. -/
def Segment.applyChanges (s : Segment) (change : Segment) : Segment where
  spec f := match change.spec f with
    | some v => some v
    | none => s.spec f

end Phonology

-- ============================================================================
-- § 2–8: Rule-Based Phonology
-- ============================================================================

namespace Phonology.RuleBased

open Phonology

-- ============================================================================
-- § 2: Context Elements
-- ============================================================================

/-- An element of a phonological rule's structural description.
    Context positions can be segment patterns (natural classes) or
    word boundaries (Hayes §6.2: `]word` or `#`). -/
inductive ContextElem where
  /-- A segment matching this natural class. -/
  | seg : Segment → ContextElem
  /-- A word boundary (Hayes: `]word` or `#`). -/
  | wordBoundary : ContextElem

-- ============================================================================
-- § 3: Rule Effect
-- ============================================================================

/-- The structural change of a phonological rule. -/
inductive RuleEffect where
  /-- Change features: merge `change` into the target segment.
      Hayes §6.2: `A → B` where B is a feature bundle. -/
  | changeFeatures : Segment → RuleEffect
  /-- Delete the target segment.
      Hayes §6.4: `A → ∅`. -/
  | delete : RuleEffect

-- ============================================================================
-- § 4: PhonRule — The SPE Rule
-- ============================================================================

/-- A phonological rule in SPE notation: `A → B / C __ D`.

    - `target`: natural class A (segments this rule applies to)
    - `effect`: structural change B (feature change or deletion)
    - `leftContext`: C (what must precede the target)
    - `rightContext`: D (what must follow the target)

    Hayes Ch 6: "A rule consists of four parts: the *target*, which
    identifies the class of sounds to be changed; the *structural
    change*, specifying what happens; and the *environment*, specifying
    where the change occurs." -/
structure PhonRule where
  name : String := ""
  target : Segment
  effect : RuleEffect
  leftContext : List ContextElem := []
  rightContext : List ContextElem := []

-- ============================================================================
-- § 5: Context Matching
-- ============================================================================

/-- Does the right context match starting at position `pos` in `segs`
    (where `pos` is the index immediately after the target)?
    Scans rightward through the context list. -/
def matchRightContext (segs : Array Segment) (pos : Nat)
    (ctx : List ContextElem) (len : Nat) : Bool :=
  match ctx with
  | [] => true
  | .wordBoundary :: rest => pos == len && matchRightContext segs pos rest len
  | .seg p :: rest =>
    if h : pos < segs.size then
      segs[pos].matchesPattern p && matchRightContext segs (pos + 1) rest len
    else false

/-- Does the left context match ending at position `pos` in `segs`
    (where `pos` is the index immediately before the target)?
    Context is ordered left-to-right, so the rightmost element is closest
    to the target. We reverse to scan inward-to-outward (leftward). -/
def matchLeftContext (segs : Array Segment) (pos : Nat)
    (ctx : List ContextElem) (len : Nat) : Bool :=
  go segs pos ctx.reverse len
where
  go (segs : Array Segment) (pos : Nat)
      (revCtx : List ContextElem) (len : Nat) : Bool :=
    match revCtx with
    | [] => true
    | .wordBoundary :: rest => pos == 0 && go segs pos rest len
    | .seg p :: rest =>
      if pos == 0 then false
      else if h : pos - 1 < segs.size then
        segs[pos - 1].matchesPattern p && go segs (pos - 1) rest len
      else false

-- ============================================================================
-- § 6: Rule Application
-- ============================================================================

/-- Apply effect to a segment: feature change merges, deletion removes. -/
def applyEffect (s : Segment) (e : RuleEffect) : Option Segment :=
  match e with
  | .changeFeatures change => some (s.applyChanges change)
  | .delete => none

/-- Apply a phonological rule to a segment string.
    Scans left-to-right, applying the rule at every position where
    the target and context match. Returns the transformed string. -/
def PhonRule.apply (r : PhonRule) (input : List Segment) : List Segment :=
  let arr := input.toArray
  let result := go arr r 0 #[]
  result.toList
where
  go (arr : Array Segment) (r : PhonRule) (pos : Nat)
      (acc : Array Segment) : Array Segment :=
    if h : pos < arr.size then
      let s := arr[pos]
      if s.matchesPattern r.target
          && matchLeftContext arr pos r.leftContext arr.size
          && matchRightContext arr (pos + 1) r.rightContext arr.size then
        match applyEffect s r.effect with
        | some s' => go arr r (pos + 1) (acc.push s')
        | none => go arr r (pos + 1) acc  -- deletion
      else
        go arr r (pos + 1) (acc.push s)
    else acc
  termination_by arr.size - pos

/-- Apply an ordered sequence of rules (derivation).
    Rules apply in order, each seeing the output of the previous.
    This is the core of ordered rule application in SPE phonology. -/
def derive (rules : List PhonRule) (input : List Segment) : List Segment :=
  rules.foldl (λ segs r => r.apply segs) input

-- ============================================================================
-- § 7: Example Rules from Hayes Ch 6
-- ============================================================================

/-- Preglottalization (Hayes p.125):
    `[-cont, -voice] → [+c.g.] / __]word`

    Voiceless stops become glottalized word-finally. -/
def preglottalization : PhonRule where
  name := "Preglottalization"
  target := Segment.ofSpecs [(Feature.continuant, false), (Feature.voice, false)]
  effect := .changeFeatures (Segment.ofSpecs [(Feature.constrGlottis, true)])
  rightContext := [.wordBoundary]

/-- Korean Stop Nasalization (Hayes p.132):
    `[-del.rel.] → [+nasal, +voice, +son] / __ [+nasal]`

    Non-affricate stops become nasalized before nasals. -/
def koreanNasalization : PhonRule where
  name := "Korean Stop Nasalization"
  target := Segment.ofSpecs [(Feature.delayedRelease, false)]
  effect := .changeFeatures (Segment.ofSpecs
    [(Feature.nasal, true), (Feature.voice, true), (Feature.sonorant, true)])
  rightContext := [.seg (Segment.ofSpecs [(Feature.nasal, true)])]

/-- Postnasal /t/ Deletion (Hayes p.133):
    `[-cont, +cor, +ant, -voice] → ∅ / [+nasal] __ [+syll]`

    Voiceless coronal stops delete between a nasal and a vowel. -/
def postnasalDeletion : PhonRule where
  name := "Postnasal /t/ Deletion"
  target := Segment.ofSpecs
    [(Feature.continuant, false), (Feature.coronal, true),
     (Feature.anterior, true), (Feature.voice, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(Feature.nasal, true)])]
  rightContext := [.seg (Segment.ofSpecs [(Feature.syllabic, true)])]

-- ============================================================================
-- § 8: Verification Theorems
-- ============================================================================

/-- Every segment matches itself as a pattern. -/
theorem matchesPattern_refl (s : Segment) :
    s.matchesPattern s = true := by
  unfold Segment.matchesPattern
  apply List.all_eq_true.mpr
  intro f _
  cases s.spec f <;> simp

/-- Applying an empty change (no features specified) is the identity. -/
theorem applyChanges_ofSpecs_nil (s : Segment) :
    s.applyChanges (Segment.ofSpecs []) = s := by
  unfold Segment.applyChanges Segment.ofSpecs
  congr

/-- Derivation with no rules is the identity. -/
theorem derive_nil (input : List Segment) :
    derive [] input = input := by
  unfold derive
  simp only [List.foldl_nil]

end Phonology.RuleBased
