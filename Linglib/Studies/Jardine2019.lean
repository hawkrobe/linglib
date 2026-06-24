/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.ASL
import Linglib.Phonology.Autosegmental.Collapse

/-!
# Jardine (2019): the expressivity of autosegmental grammars

[jardine-2019] defines `ASL^g` — stringsets given by forbidden-subgraph grammars over
autosegmental representations interpreted through a realization `g` — and places the
tone class `ASL^{gT}` in the subregular hierarchy. This file instantiates the
`Autosegmental.ASL` substrate with the tone realization `gT` and checks
banned-subgraph constraints over its realizations.

## Scope

Two realizations are checked, against the same forbidden tone melody `*HLH`:

* `Autosegmental.realize` uses the project's *bridge-only* `concat` (the coproduct), so
  an `H`-plateau `Hⁿ` stays `n` separate `H` nodes. Banning `*HLH` over `realize` then
  catches only a *local* `H-L-H` (three adjacent tonal nodes) — `hlh_excluded`.
* `Autosegmental.realizeMerged` (`Collapse.lean`) is [jardine-2019]'s OCP-*merging*
  `g_T`: `g_T(Hⁿ)` is a *single* `H` node multiply associated. Banning `*HLH` over
  `realizeMerged` becomes genuinely **non-local** — it forbids `H⁺ L⁺ H⁺` for *any*
  plateau widths, because the plateaus collapse to single nodes before the melody is
  read (`hlhTier_merged_excludes_plateau` vs `hlhTier_unmerged_admits_plateau`).

The relation-level `L = ASL^{gT}` equivalences ([jardine-2019]) remain future work.
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

/-! ### The OCP-merging realization: non-local tone plateauing

[jardine-2019]'s `g_T` is OCP-*merging* — an `H`-plateau `Hⁿ` is a single `H` node, not
`n` of them. `realizeMerged` (`Collapse.lean`) supplies that merge. Against it we ban
the *tonal-tier melody* `*HLH` — an `H-L-H` sequence read off the tone tier alone
(`hlhTier`: upper `[H, L, H]`, no morae pinned), so the constraint is on tonal adjacency
after merging, not on per-mora docking. This is where merging buys non-local power:
`H⁺ L⁺ H⁺` is excluded for *any* plateau widths, because the plateaus collapse first. -/

/-- The forbidden **tonal-tier melody** `*HLH`: an `H-L-H` sequence of adjacent tonal
    nodes, with the mora tier left unconstrained (empty lower tier, no links). Read off
    the tone tier after OCP merging, this is the genuine non-local plateauing ban —
    contrast `hlh`, whose diagonal per-mora docking makes it sensitive to plateau width. -/
def hlhTier : Graph ToneSym Mora :=
  ⟨.ofList [.H, .L, .H], .ofList [], ∅⟩

/-- The merging variant of `ASL`: the same forbidden-subgraph preimage, taken along the
    OCP-merging realization `realizeMerged` instead of the bridge-only `realize`. -/
def ASL' (g₀ : ToneSym → AR ToneSym Mora) (B : List (Graph ToneSym Mora)) : Language ToneSym :=
  realizeMerged g₀ ⁻¹' { A | isFreeOf B A }

instance (g₀ : ToneSym → AR ToneSym Mora) (B : List (Graph ToneSym Mora))
    (w : List ToneSym) : Decidable (w ∈ ASL' g₀ B) :=
  inferInstanceAs (Decidable (isFreeOf B (realizeMerged g₀ w)))

/-- `LHHLH` is excluded under merging: the `HH`-plateau merges, so the tone tier reads
    `L-H-L-H` and the medial `H-L-H` melody appears ([jardine-2019]'s `*HLH`). -/
theorem lhhlh_merged_excluded : [ToneSym.L, .H, .H, .L, .H] ∉ ASL' gT [hlhTier] := by decide

/-- A single `H`-plateau is admitted under merging: `HHH` collapses to one `H` node, so
    the tone tier is just `H` — no `H-L-H` melody to forbid. -/
theorem hhh_merged_included : [ToneSym.H, .H, .H] ∈ ASL' gT [hlhTier] := by decide

/-- **The non-local power merging buys.** An *unbounded* plateau `HH-LL-HH` is excluded
    under `realizeMerged`: every run collapses, so the tone tier reads `H-L-H` and the
    melody appears — no matter the plateau widths. -/
theorem hlhTier_merged_excludes_plateau :
    [ToneSym.H, .H, .L, .L, .H, .H] ∉ ASL' gT [hlhTier] := by decide

/-- The same string is **admitted** under the non-merging `realize`: with the plateaus
    kept apart, the tone tier reads `H-H-L-L-H-H`, which has no three *adjacent* `H-L-H`
    nodes. The contrast with `hlhTier_merged_excludes_plateau` is exactly the non-local
    expressivity OCP merging adds — the local `hlh_excluded` constraint cannot see it. -/
theorem hlhTier_unmerged_admits_plateau :
    [ToneSym.H, .H, .L, .L, .H, .H] ∈ ASL gT [hlhTier] := by decide

end Jardine2019
