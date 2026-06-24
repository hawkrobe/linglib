/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.ASL

/-!
# Jardine (2019): the expressivity of autosegmental grammars

[jardine-2019] defines `ASL^g` — stringsets given by forbidden-subgraph grammars over
autosegmental representations interpreted through a realization `g` — and places the
tone class `ASL^{gT}` in the subregular hierarchy. This file instantiates the
`Autosegmental.ASL` substrate with the tone realization `gT` (Fig. 23) and checks a
banned-subgraph constraint over its realizations.

## Scope

`Autosegmental.realize` uses the project's *bridge-only* `concat` (the coproduct), so
this captures patterns invariant under tonal merging (here: banning an `H-L-H` tone
sequence, [jardine-2019]'s `*HLH`). [jardine-2019]'s full `g_T` uses the OCP-*merging*
concat (`g_T(Hⁿ)` = one H node), which is what renders genuinely non-local patterns
(unbounded tone plateauing) local in the AR; that merging realization (via the gluing
concat / `OCP.collapse`) and the relation-level `L = ASL^{gT}` equivalences are
deferred — see `Autosegmental/Realization.lean`.
-/

namespace Jardine2019

open Autosegmental

/-- The tone alphabet ([jardine-2019] §2): high, low, falling. -/
inductive ToneSym | H | L | F
  deriving DecidableEq, Repr

/-- The tone-bearing unit (a mora). -/
inductive Mora | μ
  deriving DecidableEq, Repr

/-- The tone realization `g_T` ([jardine-2019] (23)): `H`/`L` are a single tone on one
    mora; the falling tone `F` is an `H-L` contour on one mora (multiple association). -/
def gT : ToneSym → AR ToneSym Mora
  | .H => ⟨⟨.ofList [.H], .ofList [.μ], {(0, 0)}⟩, by decide⟩
  | .L => ⟨⟨.ofList [.L], .ofList [.μ], {(0, 0)}⟩, by decide⟩
  | .F => ⟨⟨.ofList [.H, .L], .ofList [.μ], {(0, 0), (1, 0)}⟩, by decide⟩

/-- The forbidden subgraph `*HLH` ([jardine-2019] (3)): an `H-L-H` tone sequence, three
    tones each on their own mora. -/
def hlh : Graph ToneSym Mora :=
  ⟨.ofList [.H, .L, .H], .ofList [.μ, .μ, .μ], {(0, 0), (1, 1), (2, 2)}⟩

/-- `HLH` is excluded: its realization contains the `*HLH` subgraph. -/
theorem hlh_excluded : [ToneSym.H, .L, .H] ∉ ASL gT [hlh] := by decide

/-- `HL` is admitted (no `H-L-H`). -/
theorem hl_included : [ToneSym.H, .L] ∈ ASL gT [hlh] := by decide

/-- `LHL` is admitted (no `H-L-H`). -/
theorem lhl_included : [ToneSym.L, .H, .L] ∈ ASL gT [hlh] := by decide

/-- And the constraint reaches inside longer strings: `HHLH` is excluded (the medial
    `H-L-H` realizes the forbidden subgraph). -/
theorem hhlh_excluded : [ToneSym.H, .H, .L, .H] ∉ ASL gT [hlh] := by decide

end Jardine2019
