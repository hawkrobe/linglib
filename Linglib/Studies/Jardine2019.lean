/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.ASL
import Linglib.Phonology.Autosegmental.Collapse
import Linglib.Core.Computability.Subregular.Language.ContainsFactor

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

## Subregular placement

[jardine-2019] places the bridge-only class `ASL` strictly inside the star-free
languages. We prove the **link-free fragment**: when no forbidden subgraph carries
association lines, `ASL g₀ B` is star-free (`Autosegmental.ASL.isStarFree_of_links_empty`)
— over any alphabet, no `[Finite S]` needed — because such a grammar is a Boolean
combination of per-tier factor constraints, each the inverse image of a star-free
contains-factor language ([schutzenberger-1965] [mcnaughton-papert-1971]) along a tier
projection. The `*HLH` tonal-tier melody `hlhTier` is one such constraint
(`hlhTier_isStarFree`).

The genuinely autosegmental case — links coupling the two tiers — is deeper: a forbidden
subgraph can match with an unlinked run-end arbitrarily far from its linked core, so a
bounded sliding-window scanner over the realization is unsound; a two-tape synchronising
aperiodic recognizer is needed, and is left to future work.

The relation-level `L = ASL^{gT}` equivalences ([jardine-2019]) remain future work.
-/

namespace Autosegmental

open Graph

variable {S α β : Type*}

/-- For a single **link-free** forbidden subgraph `F`, the strings whose realization
contains `F` form a star-free language: the intersection of two per-tier
factor-occurrence constraints, each the inverse image (`comap`) of a star-free
contains-factor language along a tier projection. -/
theorem isStarFree_occur_of_links_empty (g₀ : S → AR α β) (F : Graph α β) (hF : F.links = ∅) :
    Language.IsStarFree {w : List S | SubgraphEmbeds F (realize g₀ w).toGraph} := by
  have hset : {w : List S | SubgraphEmbeds F (realize g₀ w).toGraph}
      = {w : List S | F.upper.toList <:+: upperProj g₀ (FreeMonoid.ofList w)}
        ∩ {w : List S | F.lower.toList <:+: lowerProj g₀ (FreeMonoid.ofList w)} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [subgraphEmbeds_iff_infix_of_links_empty F (realize g₀ w).toGraph hF,
      realize_upper_toList, realize_lower_toList]
  rw [hset]
  exact ((Language.isStarFree_containsFactor F.upper.toList).comap (upperProj g₀)).inter
        ((Language.isStarFree_containsFactor F.lower.toList).comap (lowerProj g₀))

/-- **Link-free autosegmental SL sets are star-free.** When every forbidden subgraph in
`B` has no association lines, `ASL g₀ B` is star-free — over *any* symbol alphabet, with
no `[Finite S]` hypothesis, since each tier's contains-factor recognizer is a fixed
finite aperiodic monoid. A link-free forbidden grammar is exactly a Boolean combination
of per-tier factor constraints; the genuinely autosegmental case (links coupling the
tiers) is the deeper part of [jardine-2019]'s placement and is not covered here. -/
theorem ASL.isStarFree_of_links_empty (g₀ : S → AR α β) (B : List (Graph α β))
    (hB : ∀ F ∈ B, F.links = ∅) : (ASL g₀ B).IsStarFree := by
  induction B with
  | nil =>
    have : ASL g₀ [] = Set.univ := by ext w; simp [ASL, isFreeOf, Graph.Free]
    rw [this]; exact Language.isStarFree_univ
  | cons F B' ih =>
    have hFmem : F.links = ∅ := hB F (List.mem_cons_self ..)
    have ih' := ih (fun F' hF' => hB F' (List.mem_cons_of_mem _ hF'))
    have hset : ASL g₀ (F :: B') =
        {w : List S | SubgraphEmbeds F (realize g₀ w).toGraph}ᶜ ∩ ASL g₀ B' := by
      ext w
      show (∀ G ∈ F :: B', ¬ SubgraphEmbeds G (realize g₀ w).toGraph) ↔ _
      rw [List.forall_mem_cons]; exact Iff.rfl
    rw [hset]
    exact (isStarFree_occur_of_links_empty g₀ F hFmem).compl.inter ih'

end Autosegmental

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

/-- **The `*HLH` tonal-tier melody set is star-free.** `hlhTier` carries no association
lines, so `ASL gT [hlhTier]` falls in the link-free fragment
(`ASL.isStarFree_of_links_empty`): a concrete instance of [jardine-2019]'s `ASL ⊊ SF`
placement that the bridge-only realization already settles. -/
theorem hlhTier_isStarFree : (ASL gT [hlhTier]).IsStarFree :=
  ASL.isStarFree_of_links_empty gT [hlhTier] (fun F hF => by
    rw [List.mem_singleton] at hF; subst hF; rfl)

end Jardine2019
