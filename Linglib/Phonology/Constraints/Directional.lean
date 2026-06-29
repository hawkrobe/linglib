/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Defs

/-!
# Directional constraints as position-indexed blocks

[lamont-2022b]'s **directional constraint evaluation**, realized in the canonical
constraint substrate. A directional constraint maps each candidate to a per-position
violation *vector* compared lexicographically (Eisner 2000; [lamont-2022b]). The key
observation ([lamont-2022b] §1.3) is that "a locus at position `i` relates to one at
`i+1` exactly as a higher-ranked constraint relates to a lower one … violation vectors
are ordered lexicographically, which is exactly how candidates are ordered with respect
to an entire constraint set in OT". So a directional constraint with **single-segment
loci** over a **length-preserving** GEN *is* a position-indexed block of binary
constraints, spliced into a ranking and compared under the canonical `ViolationProfile`
lex order (`Core.Optimization.Evaluation.lexLE_ofFn`) — no new mechanism beyond the
`CON`/`ViolationProfile` substrate already present.

`directionalBlock n locus` is that block: at each position `i < n` it flags whether
`locus i` holds. Splice it into a ranking forward for left-to-right evaluation (`⇒`),
or `.reverse` for right-to-left (`⇐`) — "the positions are reversed in the violation
vector" ([lamont-2022b] §1.3, Fig 1.9).

## Main definitions

* `directionalBlock` — the position-indexed block of binary constraints.

## Consumers

* `Tone.starFloatBlock` — `*FLOAT` directional float deletion ([mcpherson-lamont-2026]).
* `Lamont2022c.parseSigmaBlock` — `Parse(σ)` directional footing ([lamont-2022c]).

## Scope

This covers the *single-segment-loci, length-preserving* case — both current consumers
(a floating tone / an unfooted syllable is a single position, and neither GEN changes
the position count). [lamont-2022b]'s general formulation additionally handles
multi-segment loci (the opposite-edge projection that rules out "locus folding", §2.3)
and length-changing GEN (step-relative positions, fn. 10); those are deferred until a
consumer exercises them.
-/

namespace Constraints

/-- A **directional constraint** with single-segment loci over length-preserving GEN
([lamont-2022b]): the position-indexed block of binary constraints `i ↦ ⟦locus i⟧`,
for positions `i < n`. Spliced into a ranking and compared under the canonical lex
profile this is directional EVAL — `⇒` (left-to-right) for the forward block, `⇐` for
`.reverse`. The block's `i`-th coordinate is exactly the directional violation vector's
`i`-th entry, so the spliced profile equals the directional one
(`Core.Optimization.Evaluation.lexLE_ofFn`). -/
def directionalBlock {C : Type*} (n : ℕ) (locus : Fin n → C → Prop)
    [∀ i, DecidablePred (locus i)] : List (Constraint C) :=
  (List.finRange n).map (fun i => Constraint.binary (locus i))

end Constraints
