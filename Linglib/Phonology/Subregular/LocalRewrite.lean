/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Basic

/-!
# Local phonological rewrite rules

A **local rewrite rule** is a triple `(target, effect, context)` denoting a
featurally-conditioned transformation of segment strings. The SPE notation
`A → B / C __ D` — "every segment matching natural class `A` becomes `B`
between context `C` and `D`" — originates with [chomsky-halle-1968]; the
characterization of ordered SPE-rule cascades as regular relations is
[johnson-1972], [kaplan-kay-1994], with pedagogical exposition in [hayes-2009].

In the modern subregular setting these rules are a surface notation for the
**Input Strictly Local (ISL)** functions of [chandlee-2014], [chandlee-heinz-2018],
rather than a cognitive theory of phonological grammar (that role is held by
constraint-based frameworks such as `Phonology/OptimalityTheory/`).

## Main definitions

* `ContextElem` — a segment pattern or word boundary.
* `Effect` — feature merge or deletion.
* `Rule` — the `target / effect / leftContext / rightContext` schema.
* `Rule.apply` — a single left-to-right scan with simultaneous application.
* `derive` — an ordered-rule cascade (extrinsic ordering, the SPE convention).

## Implementation notes

Application is single-pass and simultaneous: context matches are evaluated
against the input, not the partially-rewritten output ([chomsky-halle-1968],
[chandlee-heinz-2018]). `Effect` covers only feature change and deletion, so
insertion, metathesis, coalescence, and alpha-notation agreement variables are
not expressible, and application is neither iterative/directional nor cyclic.
Iterative spreading lies in the strictly larger Output Strictly Local class
(`Core/Computability/Subregular/Function/OSL.lean`).

## Todo

* Prove `Rule.apply` is a `k`-Left-ISL function with
  `k = r.leftContext.length + r.rightContext.length + 1`, exhibiting an `ISLRule`
  over `List Segment` with word boundaries internalised
  (cf. `Core/Computability/Subregular/Function/ISL.lean`).
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

/-- Apply an effect to a target segment. Returns `none` if the segment
is deleted; `some s'` if features are merged into `s'`. -/
def Effect.apply (e : Effect) (s : Segment) : Option Segment :=
  match e with
  | .changeFeatures change => some (s.applyChanges change)
  | .delete => none

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

/-! ### Context matching -/

/-- Match a right-context list against the suffix `right` to the right
of the current position. Both lists are scanned head-to-head:
`right`'s head is the segment immediately following the target. -/
def matchRightContext : List ContextElem → List Segment → Bool
  | [], _ => true
  | .wordBoundary :: rest, [] => matchRightContext rest []
  | .wordBoundary :: _, _ :: _ => false  -- expected end of word
  | .seg p :: rest, s :: rs => s.matchesPattern p && matchRightContext rest rs
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
[chomsky-halle-1968] p. 344): contexts are matched against the *input*,
not the partially-rewritten output — the prefix `left` accumulates the
original segments, so a rule's own output never feeds its later matches.
Cf. [chandlee-heinz-2018].

The recursion is structural on `right` (the unprocessed suffix), so
`Rule.apply` reduces cleanly under `decide` for finite inputs. -/
def Rule.apply (r : Rule) (input : List Segment) : List Segment :=
  go [] input
where
  go : List Segment → List Segment → List Segment
    | _, [] => []
    | left, s :: right =>
      if s.matchesPattern r.target
          && matchLeftContext r.leftContext left
          && matchRightContext r.rightContext right then
        match r.effect.apply s with
        | some s' => s' :: go (left ++ [s]) right
        | none => go (left ++ [s]) right  -- deletion
      else
        s :: go (left ++ [s]) right

/-- Apply an ordered sequence of rules. Each rule sees the output of the
previous rule (extrinsic ordering, the SPE convention). -/
def derive (rules : List Rule) (input : List Segment) : List Segment :=
  rules.foldl (fun s r => r.apply s) input

end Subregular.LocalRewrite
