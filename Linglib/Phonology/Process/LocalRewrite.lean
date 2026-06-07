/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Featural.Features
import Linglib.Core.Computability.Subregular.Function.ISL

/-!
# Local Phonological Rewrite Rules

A **local rewrite rule** is a triple `(target, effect, context)` that
specifies a featurally-conditioned transformation of segment strings. The
canonical SPE notation `A → B / C __ D` originates with [chomsky-halle-1968]
*The Sound Pattern of English*; the formal-language characterization of
ordered SPE-rule cascades as regular relations is [johnson-1972] and
[kaplan-kay-1994]. Pedagogical exposition: [hayes-2009] Ch 6.
The notation denotes the function "every segment matching natural class
`A` becomes `B` when preceded by context `C` and followed by context `D`."

## Theoretical framing (2026)

Local rewrite rules are not a *theory* of phonology in the 2026 sense —
the cognitive-theory claim that ordered rules with extrinsic ordering
correctly model phonological grammars is a 1960s framing largely
superseded by Optimality Theory (`OptimalityTheory/`) and its
constraint-based descendants. What survives in 2026 mainstream
computational phonology is the **formal-language-theoretic** role:
local rewrite rules characterize a particular subclass of regular
relations — specifically the **Input Strictly Local (ISL) functions**
of [chandlee-2014] [chandlee-heinz-2018].

This file therefore frames `Rule` as a **convenient surface notation**
for local maps, with the formal claim grounded in
`Core/Computability/Subregular/Function/ISL.lean`. The connection is
made explicit by `Rule.apply_isInputStrictlyLocal` (currently a
documented `sorry` — the construction of the witness `ISLRule` requires
careful handling of word-boundary contexts via the augmented alphabet
`Option Segment`, deferred to a follow-up PR).

## Sibling architectures

| Framework | Key file | Relation to `LocalRewrite` |
|---|---|---|
| Tier-based alternation | `Process/Alternation.lean` | `TierRule` (Belth 2026); a single tier-adjacent context `LocalRewrite.Rule` is subsumed by `TierRule` (subsumption bridge deferred). |
| Optimality Theory | `OptimalityTheory/` | Constraint-ranking (parallel evaluation); SPE-vs-OT is the central theoretical fault line of late-20th-century phonology. |
| Harmonic Serialism | `Core/Optimization/OT/HarmonicSerialism.lean` | Iterative constraint-based; named in HS docstring as architecturally-distinct alternative for counterfeeding. |
| Stratal OT | `OptimalityTheory/Stratal.lean` | Constraint-ranking *within* strata, with extrinsic strata ordering — keeps SPE-style derivationality at the stratum boundary. |
| Output-driven (OSL/WD) | `Core/Computability/Subregular/Function/{OSL,Hierarchy}.lean` | Iterative spreading and bidirectional harmony — strictly above the ISL class that LocalRewrite occupies. |

## What this file does NOT cover

* **Alpha-notation / agreement variables** — the SPE `[α voice] → [α voice]`
  device for assimilation. The current schema cannot state Yawelmani
  vowel harmony, Sanskrit ruki, or Turkish backness/rounding harmony as
  single rules without explosion.
* **Insertion / metathesis / coalescence** — `Effect` covers only feature
  change and deletion. SPE rules of the form `∅ → V / __` (epenthesis)
  or `AB → BA` (metathesis) are not expressible.
* **Iterative / directional application** — `apply` is single-pass
  simultaneous. Iterative left-to-right or right-to-left application
  (Howard 1972, Johnson 1972) requires a different architecture; the
  modern subregular characterization places iterative spreading in the
  Output Strictly Local class (`Function/OSL.lean`), which is strictly
  above ISL.
* **Cyclic / stratal application** — handled in
  `OptimalityTheory/Stratal.lean`.
* **Tone, autosegmental representations** — Jardine 2016 shows tone
  phenomena are non-subsequential; out of scope for any subregular
  function class. See `Phonology/Autosegmental/`.

## Main definitions

* `ContextElem` — segment pattern or word boundary.
* `Effect` — feature merge or deletion.
* `Rule` — `target / effect / leftContext / rightContext` schema.
* `Rule.apply` — left-to-right scan, simultaneous application.
* `derive` — ordered-rule cascade (extrinsic ordering).

This file replaces `Process/RuleBased/Defs.lean` (deleted), which framed
the substrate as "the SPE rule formalism following Hayes Ch 6."
-/

namespace Phonology.LocalRewrite

open Phonology

-- ============================================================================
-- § 1: Context Elements and Effects
-- ============================================================================

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

-- ============================================================================
-- § 2: Rules
-- ============================================================================

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

-- ============================================================================
-- § 3: Context Matching
-- ============================================================================

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

-- ============================================================================
-- § 4: Rule Application
-- ============================================================================

/-- Apply a single rule to a segment string. Scans left-to-right; at
every position where the target and contexts match, applies the effect.
Application is **simultaneous**: context matches are evaluated against
the *input* (the prefix `left` accumulates original segments, not their
post-rule values), per the SPE default ([chomsky-halle-1968] p. 344;
[chandlee-heinz-2018] §5.1).

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

-- ============================================================================
-- § 5: Subregular Grounding (deferred bridge)
-- ============================================================================

/-! ### Headline classification (deferred)

Every `Rule.apply` is conjecturally a `k`-Left-ISL function in the sense
of [chandlee-heinz-2018], where `k = r.leftContext.length +
r.rightContext.length + 1`. The construction exhibits an `ISLRule k
(Option Segment) (Option Segment)` whose `windowOutput`:

1. Augments input to `List (Option Segment)` with `none` as the word
   boundary (mirroring `Subregular/Basic.lean`'s `Augmented α` pattern).
2. Fires the rule when the window's central position matches `target`
   and the surrounding window matches both contexts (`wordBoundary` ↦
   `none`).
3. For rules with right context of length `n`, the FST emits output
   delayed by `n` symbols (Chandlee-Heinz §4 simulation; see
   `Function/Hierarchy.lean::ISLRule.toSFST` for the analogous
   simulation pattern at the abstract level).
4. Strips boundary markers from the output to recover `List Segment`.

The theorem is **not stated** in this PR rather than stated with
`sorry` — the right-context output-delay construction is non-trivial and
the audit (mathlib reviewer B2) flagged the previous `sorry`'d shape
(`∃ k, IsInputStrictlyLocal k (fun input : List (Option Segment) => …)`)
as malformed: the function should live over `List Segment` directly with
boundary handling internalised, and the existential `k` should be the
explicit `r.leftContext.length + r.rightContext.length + 1`. Land the
witness construction in a dedicated `Phonology/Process/
LocalRewriteISL.lean` follow-up file once a Studies consumer needs the
explicit classification (the `MeinhardtEtAl2024.lean` Studies file
demonstrates substrate use without going through `Rule.apply`). -/
end Phonology.LocalRewrite
