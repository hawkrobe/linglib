/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

## References

* [N. Chomsky and M. Halle, *The Sound Pattern of English* (1968)][chomsky-halle-1968]
* [C. D. Johnson, *Formal Aspects of Phonological Description* (1972)][johnson-1972]
* [R. M. Kaplan and M. Kay, *Regular Models of Phonological Rule Systems* (1994)][kaplan-kay-1994]
* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [J. Chandlee, *Strictly Local Phonological Processes* (2014)][chandlee-2014]
* [J. Chandlee and J. Heinz, *Strict Locality and Phonological Maps* (2018)][chandlee-heinz-2018]
* [M. Mohri, *Finite-State Transducers in Language and Speech Processing* (1997)][mohri-1997]
-/
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.ISL
import Mathlib.Data.Finset.Piecewise

/-!
# Local phonological rewrite rules

A **local rewrite rule** is a triple `(target, effect, context)` denoting a
featurally-conditioned transformation of segment strings. The SPE notation
`A → B / C __ D` — "every segment matching natural class `A` becomes `B`
between context `C` and `D`" — originates with Chomsky and Halle; the
characterization of ordered SPE-rule cascades as regular relations is due to
Johnson and to Kaplan and Kay, with pedagogical exposition in Hayes.

In the modern subregular setting these rules are a surface notation for the
**Input Strictly Local (ISL)** functions of Chandlee and of Chandlee and Heinz,
rather than a cognitive theory of phonological grammar (that role is held by
constraint-based frameworks such as `Phonology/OptimalityTheory/`).

## Main definitions

* `ContextElem` — a segment pattern or word boundary.
* `Effect` — feature merge, deletion, or assimilation of a feature class to a
  neighbour (SPE alpha-variables; node spreading when the class is natural).
* `Rule` — the `target / effect / leftContext / rightContext` schema, with
  `Rule.leftReach` and `Rule.rightReach` the input it inspects on each side.
* `Rule.apply` — a single left-to-right scan with simultaneous application.
* `derive` — an ordered-rule cascade (extrinsic ordering, the SPE convention).
* `Rule.toISLRule`, `Rule.toSubsequentialTransducer` — the two machine
  presentations of a rule.

## Main results

* `matchRightContext_take`, `matchLeftContext_rtake`, `Effect.apply_rtake`,
  `Effect.apply_append` — contexts and effects read bounded windows, so a verdict
  factors through `leftReach` symbols to the left and `rightReach` to the right.
* `Rule.isLeftInputStrictlyLocal` — a rule reading nothing to its right is
  `(leftReach + 1)`-Left-ISL.
* `Rule.isLeftSubsequential` — over a finite segment alphabet every rule is
  Left-Subsequential, via a transducer that delays emission by `rightReach`
  symbols and flushes the buffer at the word end.

## Implementation notes

Application is single-pass and simultaneous: context matches and copied values
are read from the input, not the partially-rewritten output (Chomsky and Halle,
Chandlee and Heinz). `Effect` covers feature change, deletion, and copying a
feature class from the adjacent input segment — Chomsky and Halle's
alpha-variables, which is `Finset.piecewise` on the class — so insertion,
metathesis and coalescence are not expressible, and application is neither
iterative/directional nor cyclic. Iterative spreading lies in the strictly
larger Output Strictly Local class (`Subregular.OSLRule`).

## Todo

* `Rule.apply` over **boundary-augmented** input. Padding the string with word
  boundaries turns the right context into lookahead the padding pays for, and
  the rule becomes `k`-Left-ISL with
  `k = r.leftReach + r.rightReach + 1`. Over raw strings that statement does
  not hold in general — a bounded left window cannot see the right context —
  which is why `Rule.isLeftInputStrictlyLocal` assumes no right reach and
  `Rule.isLeftSubsequential` is what survives without it.
-/

namespace Subregular.LocalRewrite

open Phonology

/-! ### Context elements and effects -/

/-- An element of a rule's structural description. Context positions
hold either a segment pattern (a natural class via `Segment` partial
specification) or a word boundary marker. -/
inductive ContextElem where
  /-- A segment matching a natural-class pattern. -/
  | seg : Segment → ContextElem
  /-- A word boundary (Hayes notation: `]word` or `#`). -/
  | wordBoundary : ContextElem

/-- The structural change effected by a rule. -/
inductive Effect where
  /-- Merge a feature bundle into the target segment.
      SPE notation: `A → B` where B is a partial specification. -/
  | changeFeatures : Segment → Effect
  /-- Delete the target segment. SPE notation: `A → ∅`. -/
  | delete : Effect
  /-- Assimilate the features of the class `C` to the following segment: the alpha-variable
      change `A → [αF, βG, …] / __ [αF, βG, …]` for `C = {F, G, …}`, and the spreading of a
      class node when `C` is a natural class (`Phonology/FeatureGeometry.lean`). -/
  | copyRight : Finset Feature → Effect
  /-- Assimilate the features of the class `C` to the preceding segment. -/
  | copyLeft : Finset Feature → Effect

/-- How many segments to the left of the target an effect reads. -/
def Effect.leftReach : Effect → ℕ
  | .copyLeft _ => 1
  | _ => 0

/-- How many segments to the right of the target an effect reads. -/
def Effect.rightReach : Effect → ℕ
  | .copyRight _ => 1
  | _ => 0

/-- Apply an effect to a target `s` standing between the prefix `w` and the suffix `d`:
`none` deletes the segment, and a class copy takes the neighbour's values on the class,
leaving the target unchanged at a word edge. -/
def Effect.apply (e : Effect) (w : List Segment) (s : Segment) (d : List Segment) :
    Option Segment :=
  match e with
  | .changeFeatures change => some (Features.Bundle.merge change s)
  | .delete => none
  | .copyRight C => some (d.head?.elim s λ t => C.piecewise t s)
  | .copyLeft C => some (w.getLast?.elim s λ t => C.piecewise t s)

/-- An effect reads at most `leftReach` symbols of the prefix. -/
theorem Effect.apply_rtake (e : Effect) {n : ℕ} (h : e.leftReach ≤ n) (w : List Segment)
    (s : Segment) (d : List Segment) : e.apply (w.rtake n) s d = e.apply w s d := by
  cases e with
  | changeFeatures _ => rfl
  | delete => rfl
  | copyRight _ => rfl
  | copyLeft C =>
    have h1 : 1 ≤ n := by simpa [Effect.leftReach] using h
    simp only [Effect.apply, List.getLast?_rtake _ h1]

/-- An effect reads at most `rightReach` symbols of the suffix. -/
theorem Effect.apply_append (e : Effect) (w : List Segment) (s : Segment) (d d' : List Segment)
    (h : e.rightReach ≤ d.length) : e.apply w s (d ++ d') = e.apply w s d := by
  cases e with
  | changeFeatures _ => rfl
  | delete => rfl
  | copyLeft _ => rfl
  | copyRight C =>
    have hd : d ≠ [] := by rintro rfl; simp [Effect.rightReach] at h
    simp only [Effect.apply, List.head?_append_of_ne_nil d hd]

/-! ### Rules -/

/-- A **local rewrite rule** in SPE notation `A → B / C __ D`.

* `target` — natural class `A` matched by the affected segment.
* `effect` — structural change `B`: feature merge or deletion.
* `leftContext` — preceding context `C`, ordered left-to-right (so the
  rightmost element is closest to the target).
* `rightContext` — following context `D`, ordered left-to-right.

The `name` field is informational. -/
structure Rule where
  name : String := ""
  target : Segment
  effect : Effect
  leftContext : List ContextElem := []
  rightContext : List ContextElem := []

/-- The input symbols to the left of the target a rule reads: its left context and whatever its
effect copies. -/
def Rule.leftReach (r : Rule) : ℕ := max r.leftContext.length r.effect.leftReach

/-- The input symbols to the right of the target a rule reads: its right context and whatever
its effect copies. -/
def Rule.rightReach (r : Rule) : ℕ := max r.rightContext.length r.effect.rightReach

/-! ### Context matching -/

/-- Match a right-context list against the suffix `right` to the right
of the current position. Both lists are scanned head-to-head:
`right`'s head is the segment immediately following the target. -/
def matchRightContext : List ContextElem → List Segment → Bool
  | [], _ => true
  | .wordBoundary :: rest, [] => matchRightContext rest []
  | .wordBoundary :: _, _ :: _ => false  -- expected end of word
  | .seg p :: rest, s :: rs => decide (p ≤ s) && matchRightContext rest rs
  | .seg _ :: _, [] => false  -- expected segment, none follows

/-- Match a left-context list against the prefix `left` to the left of
the current position. Context elements are ordered left-to-right (so
the rightmost element is closest to the target); we reverse both lists
once and then scan head-to-head. -/
def matchLeftContext (ctx : List ContextElem) (left : List Segment) : Bool :=
  matchRightContext ctx.reverse left.reverse

/-! ### Rule application -/

/-- Apply a single rule to a segment string. Scans left-to-right; at
every position where the target and contexts match, applies the effect.
Application is **simultaneous** in the SPE sense (convention (39),
Chomsky and Halle p. 344): contexts are matched against the *input*,
not the partially-rewritten output — the prefix `left` accumulates the
original segments, so a rule's own output never feeds its later matches.
Cf. Chandlee and Heinz.

The recursion is structural on `right` (the unprocessed suffix), so
`Rule.apply` reduces cleanly under `decide` for finite inputs. -/
def Rule.apply (r : Rule) (input : List Segment) : List Segment :=
  go [] input
where
  go : List Segment → List Segment → List Segment
    | _, [] => []
    | left, s :: right =>
      if decide (r.target ≤ s)
          && matchLeftContext r.leftContext left
          && matchRightContext r.rightContext right then
        match r.effect.apply left s right with
        | some s' => s' :: go (left ++ [s]) right
        | none => go (left ++ [s]) right  -- deletion
      else
        s :: go (left ++ [s]) right

/-- Apply an ordered sequence of rules. Each rule sees the output of the
previous rule (extrinsic ordering, the SPE convention). -/
def derive (rules : List Rule) (input : List Segment) : List Segment :=
  rules.foldl (fun s r => r.apply s) input

/-! ### Bounded context windows

A context list of length `n` inspects at most `n` symbols, so both matchers
factor through a bounded window — the right one through a prefix, the left one
through a suffix. The word boundary is what makes this delicate: it matches
exactly when the string is exhausted, so a window must be long enough to tell
a genuinely short string from a truncated one. A window of the context's own
length is: it is exhausted only when the string is. -/

theorem matchRightContext_take (ctx : List ContextElem) (right : List Segment) :
    matchRightContext ctx (right.take ctx.length) = matchRightContext ctx right := by
  induction ctx generalizing right with
  | nil => rfl
  | cons c rest ih => cases c <;> cases right <;> simp [matchRightContext, ih]

theorem matchLeftContext_rtake (ctx : List ContextElem) (left : List Segment) :
    matchLeftContext ctx (left.rtake ctx.length) = matchLeftContext ctx left := by
  have h : (left.rtake ctx.length).reverse = left.reverse.take ctx.reverse.length := by
    simp [List.rtake_eq_reverse_take_reverse]
  rw [matchLeftContext, h, matchRightContext_take, matchLeftContext]

/-- Any window at least as long as the context reads the same. -/
theorem matchLeftContext_rtake_of_le (ctx : List ContextElem) {n : ℕ} (h : ctx.length ≤ n)
    (left : List Segment) : matchLeftContext ctx (left.rtake n) = matchLeftContext ctx left := by
  rw [← matchLeftContext_rtake ctx (left.rtake n), List.rtake_rtake, min_eq_left h,
    matchLeftContext_rtake]

/-- A suffix at least as long as the context reads the same as its extensions. -/
theorem matchRightContext_append_of_le (ctx : List ContextElem) {d : List Segment}
    (d' : List Segment) (h : ctx.length ≤ d.length) :
    matchRightContext ctx (d ++ d') = matchRightContext ctx d := by
  rw [← matchRightContext_take ctx d, ← matchRightContext_take ctx (d ++ d'),
    List.take_append_of_le_length h]

/-! ### The verdict at a position -/

/-- The output block a rule contributes at one position: the effect applied when
target, left context `w` and right context `d` all match, and the untouched
segment otherwise. -/
def Rule.verdict (r : Rule) (w : List Segment) (s : Segment) (d : List Segment) :
    List Segment :=
  if decide (r.target ≤ s) && matchLeftContext r.leftContext w
      && matchRightContext r.rightContext d then
    (r.effect.apply w s d).toList
  else [s]

/-- `Rule.apply` emits one `Rule.verdict` per input position. -/
theorem Rule.apply_go_cons (r : Rule) (left : List Segment) (s : Segment)
    (right : List Segment) :
    Rule.apply.go r left (s :: right)
      = r.verdict left s right ++ Rule.apply.go r (left ++ [s]) right := by
  cases hc : decide (r.target ≤ s) && matchLeftContext r.leftContext left
      && matchRightContext r.rightContext right <;>
    cases he : r.effect.apply left s right <;> simp [Rule.apply.go, Rule.verdict, hc, he]

/-- The verdict reads only the last `leftReach` symbols of the prefix. -/
theorem Rule.verdict_rtake (r : Rule) (w : List Segment) (s : Segment) (d : List Segment) :
    r.verdict (w.rtake r.leftReach) s d = r.verdict w s d := by
  rw [Rule.verdict, Rule.verdict,
    matchLeftContext_rtake_of_le r.leftContext (n := r.leftReach) (le_max_left _ _),
    Effect.apply_rtake r.effect (n := r.leftReach) (le_max_right _ _)]

/-- The verdict reads only the first `rightReach` symbols of the suffix. -/
theorem Rule.verdict_append (r : Rule) (w : List Segment) (s : Segment) (d e : List Segment)
    (h : r.rightReach ≤ d.length) : r.verdict w s (d ++ e) = r.verdict w s d := by
  rw [Rule.verdict, Rule.verdict,
    matchRightContext_append_of_le _ _
      ((le_max_left _ _ : r.rightContext.length ≤ r.rightReach).trans h),
    Effect.apply_append _ _ _ _ _ ((le_max_right _ _ : r.effect.rightReach ≤ r.rightReach).trans h)]

/-! ### The bounded-window scan -/

/-- `Rule.apply` rewritten to carry only the last `leftReach` input symbols: the unbounded
prefix of `Rule.apply.go` is replaced by the window the rule can actually inspect. -/
def Rule.scan (r : Rule) (w : List Segment) : List Segment → List Segment
  | [] => []
  | s :: right => r.verdict w s right ++ r.scan ((w ++ [s]).rtake r.leftReach) right

/-- Truncating the prefix to the rule's left reach loses nothing. -/
theorem Rule.scan_rtake (r : Rule) (left right : List Segment) :
    r.scan (left.rtake r.leftReach) right = Rule.apply.go r left right := by
  induction right generalizing left with
  | nil => rfl
  | cons s right ih =>
    rw [Rule.scan, Rule.verdict_rtake, List.rtake_append_rtake, ih, Rule.apply_go_cons]

/-- `Rule.apply` is the bounded-window scan started from the empty window. -/
theorem Rule.apply_eq_scan (r : Rule) : r.apply = r.scan [] := by
  funext input
  show Rule.apply.go r [] input = _
  simpa using (r.scan_rtake [] input).symm

/-! ### No right reach: Input Strict Locality

A rule that reads nothing to its right — no right context and no copy from the right —
has a verdict depending only on the last `leftReach` input symbols and the current one,
exactly the `(leftReach + 1)`-ISL window of Chandlee and of Chandlee and Heinz. -/

/-- The ISL rule computing a rewrite with no right reach. The hypothesis is the
applicability condition: with a positive right reach the lookahead `[]` supplied here is
the end-of-word one, not the one `Rule.apply` uses. -/
def Rule.toISLRule (r : Rule) (_h : r.rightReach = 0) :
    ISLRule (r.leftReach + 1) Segment Segment where
  windowOutput w s := r.verdict w s []

private theorem Rule.applyAux_toISLRule (r : Rule) (h : r.rightReach = 0)
    (w input : List Segment) : (r.toISLRule h).applyAux w input = r.scan w input := by
  induction input generalizing w with
  | nil => rfl
  | cons s xs ih =>
    have hv : (r.toISLRule h).windowOutput w s = r.verdict w s xs := by
      show r.verdict w s [] = r.verdict w s xs
      simpa using (r.verdict_append w s [] xs (by simp [h])).symm
    rw [ISLRule.applyAux_cons, hv, Nat.add_sub_cancel, Rule.scan, ih]

theorem Rule.toISLRule_apply (r : Rule) (h : r.rightReach = 0) :
    (r.toISLRule h).apply = r.apply := by
  funext input
  show (r.toISLRule h).applyAux [] input = _
  rw [r.applyAux_toISLRule h, Rule.apply_eq_scan]

/-- **A rewrite rule with no right reach is Left-ISL**, with `k` one more than its left
reach. -/
theorem Rule.isLeftInputStrictlyLocal (r : Rule) (h : r.rightReach = 0) :
    IsLeftInputStrictlyLocal (r.leftReach + 1) r.apply :=
  ⟨r.toISLRule h, r.toISLRule_apply h⟩

/-! ### The general case: left-subsequentiality

A positive right reach is lookahead, which a left-to-right scan cannot have.
The transducer buys it with delay: it leaves the last `rightReach` segments
unjudged in a buffer, so that the oldest buffered segment always has its full
right context in hand, and judges what remains buffered against the word end in
`finalOutput`. That final flush is what the right context costs — `ofWindow`,
and with it every ISL rule, emits nothing at the end. -/

/-- The delayed-emission state: the left window of the oldest undecided segment,
paired with the lookahead buffer of segments whose right context is still
incomplete. -/
abbrev Rule.State (r : Rule) : Type :=
  {l : List Segment // l.length ≤ r.leftReach} ×
    {l : List Segment // l.length ≤ r.rightReach}

/-- The delayed transducer for an arbitrary rewrite rule. Reading `x` appends it
to the buffer; whatever that pushes out of the buffer has acquired its full right
context, so it is judged and enters the left window. `finalOutput` judges the
remaining buffer against the end of the word, where a short lookahead is exactly
what `matchRightContext` expects. -/
def Rule.toSubsequentialTransducer (r : Rule) :
    SubsequentialTransducer r.State Segment Segment where
  start := (⟨[], Nat.zero_le _⟩, ⟨[], Nat.zero_le _⟩)
  step s x :=
    (⟨(s.1.val ++ (s.2.val ++ [x]).rdrop r.rightReach).rtake r.leftReach,
        List.length_rtake_le _ _⟩,
      ⟨(s.2.val ++ [x]).rtake r.rightReach, List.length_rtake_le _ _⟩)
  output s x :=
    ((s.2.val ++ [x]).rdrop r.rightReach).flatMap fun b =>
      r.verdict s.1.val b ((s.2.val ++ [x]).rtake r.rightReach)
  finalOutput s := r.scan s.1.val s.2.val

/-- From any state the delayed transducer judges the buffer and the remaining
input together: the delay is invisible in the total output. -/
theorem Rule.runFrom_toSubsequentialTransducer (r : Rule) (s : r.State)
    (input : List Segment) :
    r.toSubsequentialTransducer.runFrom s input = r.scan s.1.val (s.2.val ++ input) := by
  induction input generalizing s with
  | nil => simp [Rule.toSubsequentialTransducer]
  | cons x xs ih =>
    obtain ⟨⟨w, hw⟩, buf, hbuf⟩ := s
    rw [SubsequentialTransducer.runFrom_cons, ih]
    simp only [Rule.toSubsequentialTransducer, show buf ++ x :: xs = (buf ++ [x]) ++ xs by simp]
    rcases Nat.lt_or_ge buf.length r.rightReach with h | h
    · have hle : (buf ++ [x]).length ≤ r.rightReach := by simp; omega
      rw [show (buf ++ [x]).rdrop r.rightReach = [] by simp [List.rdrop]; omega,
        List.rtake_of_length_le hle]
      simp [List.rtake_of_length_le hw]
    · obtain ⟨b, rest, hb⟩ : ∃ b rest, buf ++ [x] = b :: rest :=
        List.exists_cons_of_ne_nil (by simp)
      have hrest : rest.length = r.rightReach := by
        have hl := congrArg List.length hb; simp at hl; omega
      rw [hb, show (b :: rest).rdrop r.rightReach = [b] by simp [List.rdrop, hrest],
        show (b :: rest).rtake r.rightReach = rest by simp [List.rtake, hrest],
        List.cons_append, Rule.scan, r.verdict_append w b rest xs hrest.ge]
      simp

/-- The delayed transducer computes the rule. -/
theorem Rule.run_toSubsequentialTransducer (r : Rule) :
    r.toSubsequentialTransducer.run = r.apply := by
  funext input
  rw [SubsequentialTransducer.run, r.runFrom_toSubsequentialTransducer]
  simp [Rule.apply_eq_scan, Rule.toSubsequentialTransducer]

/-- **Every local rewrite rule is Left-Subsequential.** `Segment` is a partial
valuation of the 26 features of Hayes, so it is finite but carries no
`Fintype` instance (its `Flat` slots are deliberately opaque); the hypothesis
supplies the finite alphabet Mohri assumes without forcing a
`3 ^ 26`-element enumeration on every consumer of this file. -/
theorem Rule.isLeftSubsequential [Fintype Segment] (r : Rule) :
    IsLeftSubsequential r.apply :=
  r.run_toSubsequentialTransducer ▸ r.toSubsequentialTransducer.isLeftSubsequential

end Subregular.LocalRewrite
