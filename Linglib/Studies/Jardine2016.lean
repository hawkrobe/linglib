/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Correspondence

/-!
# Jardine (2016): transformations as correspondence-graph relations

[jardine-2016] (Ch. 7) presents a phonological process as a **relation** between input
and output, given by correspondence graphs carved out of GEN by banned-subgraph
constraints. This file exercises the `Autosegmental.Correspondence` substrate on the
intervocalic-voicing schema (Jardine's running example): a faithfulness constraint
`*[p↔p]` — forbidding a `p` that corresponds to a `p` — admits the voicing
correspondence `apa ↔ aba` and rejects the faithful `apa ↔ apa`.

## Scope

This demonstrates the constraint mechanism at the correspondence-graph level. The full
relation-level result `R(CG(φ)) = R_voice` additionally requires GEN (`CG(Γ)`, the
correspondence graphs built from primitives), which fixes the correspondence structure;
and Jardine's *output-only* markedness `*VTV` needs the arc-labelled-subgraph refinement
(Ch. 7 fn. 7). Both are deferred — see `Autosegmental/Correspondence.lean`.
-/

namespace Jardine2016

open Autosegmental Correspondence

/-- Toy alphabet for intervocalic voicing: a vowel `a`, voiceless `p`, voiced `b`. -/
inductive Seg | a | p | b
  deriving DecidableEq, Repr

/-- A correspondence graph over the one alphabet (input and output both `Seg`). -/
abbrev CGraph := Graph Seg Seg

/-- The faithfulness banned subgraph `*[pⁱ↔p]`: a `p` corresponding to a `p`. Forbidding
    it forces an intervocalic `p` to change. -/
def noPP : CGraph := ⟨.ofList [Seg.p], .ofList [Seg.p], {(0, 0)}⟩

/-- The voicing correspondence `apa ↔ aba`: identity positions, the medial `p`
    corresponding to a `b`. -/
def gVoice : CGraph :=
  ⟨.ofList [Seg.a, .p, .a], .ofList [Seg.a, .b, .a], {(0, 0), (1, 1), (2, 2)}⟩

/-- The faithful correspondence `apa ↔ apa`: the medial `p` stays `p`. -/
def gFaithful : CGraph :=
  ⟨.ofList [Seg.a, .p, .a], .ofList [Seg.a, .p, .a], {(0, 0), (1, 1), (2, 2)}⟩

/-- `gVoice` reads input `apa`, output `aba`. -/
theorem gVoice_io : input gVoice = [Seg.a, .p, .a] ∧ output gVoice = [Seg.a, .b, .a] := by
  decide

/-- The voicing correspondence is **admitted** by the `*[p↔p]` grammar (no `p↔p`). -/
theorem gVoice_specified : specifiedBy [noPP] gVoice := by decide

/-- The faithful correspondence is **rejected** — it contains a `p↔p`. -/
theorem gFaithful_rejected : ¬ specifiedBy [noPP] gFaithful := by decide

/-- Hence `apa ↔ aba` lies in the relation presented by the local grammar `*[p↔p]`,
    witnessed by `gVoice` ([jardine-2016] Def. 25). -/
theorem voicing_local : rel (specifiedBy [noPP]) [Seg.a, .p, .a] [Seg.a, .b, .a] :=
  ⟨gVoice, gVoice_specified, by decide, by decide⟩

end Jardine2016
