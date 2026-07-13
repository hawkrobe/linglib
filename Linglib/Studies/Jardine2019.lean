/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.ASL
import Linglib.Phonology.Autosegmental.OCP
import Linglib.Phonology.Autosegmental.Junction
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
  an `H`-plateau `Hⁿ` stays `n` separate `H` nodes. Banning `*HLH` over `AR.realize` then
  catches only a *local* `H-L-H` (three adjacent tonal nodes) — `hlh_excluded`.
* `Autosegmental.realizeMerged` (`Collapse.lean`) is [jardine-2019]'s OCP-*merging*
  `g_T`: `g_T(Hⁿ)` is a *single* `H` node multiply associated. Banning `*HLH` over
  `AR.realizeMerged` becomes genuinely **non-local** — it forbids `H⁺ L⁺ H⁺` for *any*
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

variable {S : Type*}

/-! #### The star-free placement in coordinates -/

section Coordinate

variable {ι : Type*} [Finite ι] {τ : ι → Type*}

/-- For a single link-free forbidden factor, the strings whose realization
    contains it form a star-free language: the finite intersection of per-tier
    factor constraints, each the inverse image of a star-free contains-factor
    language along a tier projection. -/
theorem AR.isStarFree_occur_of_link_free
    (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι))
    [∀ s, Finite (g₀ s).obj.V]
    (F : AR (Sigma.fst : ((i : ι) × τ i) → ι)) [Finite F.obj.V]
    (hF : ∀ i j p q, ¬ F.link i j p q) :
    Language.IsStarFree {w : List S | F.FactorEmbeds (Autosegmental.realize g₀ w)} := by
  have hset : {w : List S | F.FactorEmbeds (Autosegmental.realize g₀ w)}
      = ⋂ i, {w : List S | F.tierWord i <:+: tierProj g₀ i (FreeMonoid.ofList w)} := by
    ext w
    haveI := Autosegmental.realize.instFinite g₀ w
    simp only [Set.mem_setOf_eq, Set.mem_iInter,
      AR.factorEmbeds_iff_infix_of_link_free hF, tierProj_ofList]
    exact Iff.rfl
  rw [hset]
  exact Language.IsStarFree.iInter fun i =>
    (Language.isStarFree_containsFactor (F.tierWord i)).comap (tierProj g₀ i)

/-- **Link-free autosegmental SL sets are star-free**, on the graph foundation:
    when no forbidden factor carries association lines, `AR.ASL` is
    a Boolean combination of per-tier factor constraints. -/
theorem AR.ASL.isStarFree_of_link_free
    (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι))
    [∀ s, Finite (g₀ s).obj.V]
    (B : List {F : AR (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V})
    (hB : ∀ F ∈ B, haveI := F.property; ∀ i j p q, ¬ F.val.link i j p q) :
    (AR.ASL g₀ B).IsStarFree := by
  induction B with
  | nil =>
    have : AR.ASL g₀ ([] :
        List {F : AR (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V})
        = Set.univ :=
      Set.eq_univ_of_forall fun w F hF => absurd hF (List.not_mem_nil)
    rw [this]
    exact Language.isStarFree_univ
  | cons F B' ih =>
    have hFl := hB F (List.mem_cons_self ..)
    have ih' := ih fun F' hF' => hB F' (List.mem_cons_of_mem _ hF')
    have hset : AR.ASL g₀ (F :: B') =
        {w : List S | haveI := F.property
          F.val.FactorEmbeds (Autosegmental.realize g₀ w)}ᶜ ∩ AR.ASL g₀ B' := by
      ext w
      show (∀ G ∈ F :: B', _) ↔ _
      rw [List.forall_mem_cons]
      exact Iff.rfl
    rw [hset]
    haveI := F.property
    exact (AR.isStarFree_occur_of_link_free g₀ F.val hFl).compl.inter ih'

end Coordinate

end Autosegmental

namespace Jardine2019

open Autosegmental

/-- The tone alphabet ([jardine-2019] §2): high, low, falling. -/
inductive ToneSym | H | L | F
  deriving DecidableEq, Repr

/-- The tone-bearing unit (a mora). -/
inductive Mora | μ
  deriving DecidableEq, Repr

/-- Two-tier tone representations (melody over `true`, morae over `false`). -/
abbrev TRep := AR
  (Sigma.fst : ((b : Bool) × TwoTier ToneSym Mora b) → Bool)

/-- Link presentations from finite pair lists. -/
def mkL (links : List (ℕ × ℕ)) (i j : Bool) (p q : ℕ) : Prop :=
  i = true ∧ j = false ∧ (p, q) ∈ links

instance (links : List (ℕ × ℕ)) (i j : Bool) (p q : ℕ) :
    Decidable (mkL links i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Build a representation from a tone melody, morae, and links. -/
abbrev mk (tones : List ToneSym) (moras : List Mora) (links : List (ℕ × ℕ)) : TRep :=
  AR.ofData
    (fun b => match b with
      | true => (tones : List (TwoTier ToneSym Mora true))
      | false => moras)
    (mkL links)

theorem mk_embeds_iff {tF tX : List ToneSym} {bF bX : List Mora}
    {lF lX : List (ℕ × ℕ)} :
    (mk tF bF lF).FactorEmbeds (mk tX bX lX) ↔
      dataEmbeds
        (fun b => match b with
          | true => (tF : List (TwoTier ToneSym Mora true))
          | false => bF)
        (fun b => match b with
          | true => (tX : List (TwoTier ToneSym Mora true))
          | false => bX)
        (mkL lF) (mkL lX) :=
  AR.factorEmbeds_ofData_iff

/-- The forbidden subgraph `*HLH` ([jardine-2019] (3)): an `H-L-H` tone
    sequence, three tones each on their own mora. -/
abbrev hlh : TRep := mk [.H, .L, .H] [.μ, .μ, .μ] [(0, 0), (1, 1), (2, 2)]

/-! ### The bridge-only realization: local `*HLH`

The realization of a tone string under the bridge-only tensor is, in flattened
presentation, the diagonal literal — one tone per mora (`gT` (23), with `F` an
`H-L` contour). The `*HLH` verdicts compute through the data-level checker. -/

/-- `HLH` is excluded: its realization contains the `*HLH` subgraph. -/
theorem hlh_excluded :
    hlh.FactorEmbeds (mk [.H, .L, .H] [.μ, .μ, .μ] [(0, 0), (1, 1), (2, 2)]) := by
  rw [mk_embeds_iff]; decide

/-- `HL` is admitted (no `H-L-H`). -/
theorem hl_included :
    ¬ hlh.FactorEmbeds (mk [.H, .L] [.μ, .μ] [(0, 0), (1, 1)]) := by
  rw [mk_embeds_iff]; decide

/-- `LHL` is admitted (no `H-L-H`). -/
theorem lhl_included :
    ¬ hlh.FactorEmbeds (mk [.L, .H, .L] [.μ, .μ, .μ] [(0, 0), (1, 1), (2, 2)]) := by
  rw [mk_embeds_iff]; decide

/-- The constraint reaches inside longer strings: `HHLH` is excluded (the
    medial `H-L-H` realizes the forbidden subgraph). -/
theorem hhlh_excluded :
    hlh.FactorEmbeds
      (mk [.H, .H, .L, .H] [.μ, .μ, .μ, .μ] [(0, 0), (1, 1), (2, 2), (3, 3)]) := by
  rw [mk_embeds_iff]; decide

/-! ### The OCP-merging realization: non-local tone plateauing

[jardine-2019]'s `g_T` is OCP-*merging*: an `H`-plateau `Hⁿ` fuses to a single
`H` node (`AR.collapse`). Against the merged forms we ban the
**tonal-tier melody** `*HLH` — adjacent tonal nodes, morae unconstrained —
which is where merging buys non-local power: `H⁺ L⁺ H⁺` is excluded for *any*
plateau widths, because the plateaus collapse first. -/

/-- The forbidden tonal-tier melody `*HLH`: no morae pinned, no links. -/
abbrev hlhTier : TRep := mk [.H, .L, .H] [] []

/-- `LHHLH` is excluded under merging: the `HH`-plateau fuses, the tone tier
    reads `L-H-L-H`, and the medial `H-L-H` melody appears. -/
theorem lhhlh_merged_excluded :
    hlhTier.FactorEmbeds
      (mk [.L, .H, .L, .H] [.μ, .μ, .μ, .μ, .μ]
        [(0, 0), (1, 1), (1, 2), (2, 3), (3, 4)]) := by
  rw [mk_embeds_iff]; decide

/-- A single `H`-plateau is admitted under merging: `HHH` fuses to one `H`. -/
theorem hhh_merged_included :
    ¬ hlhTier.FactorEmbeds (mk [.H] [.μ, .μ, .μ] [(0, 0), (0, 1), (0, 2)]) := by
  rw [mk_embeds_iff]; decide

/-- **The non-local power merging buys**: the unbounded plateau `HH-LL-HH`
    fuses to tone tier `H-L-H`, so the melody appears — at any widths. -/
theorem hlhTier_merged_excludes_plateau :
    hlhTier.FactorEmbeds
      (mk [.H, .L, .H] [.μ, .μ, .μ, .μ, .μ, .μ]
        [(0, 0), (0, 1), (1, 2), (1, 3), (2, 4), (2, 5)]) := by
  rw [mk_embeds_iff]; decide

/-- The same string **unmerged** is admitted: the plateaus stay apart, the tone
    tier reads `H-H-L-L-H-H`, and no three adjacent nodes spell `H-L-H`. The
    contrast with `hlhTier_merged_excludes_plateau` is exactly the non-local
    expressivity OCP merging adds. -/
theorem hlhTier_unmerged_admits_plateau :
    ¬ hlhTier.FactorEmbeds
      (mk [.H, .H, .L, .L, .H, .H] [.μ, .μ, .μ, .μ, .μ, .μ]
        [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]) := by
  rw [mk_embeds_iff]; decide

/-- **The `*HLH` tonal-tier melody set is star-free**: `hlhTier` carries no
    links, so any grammar built from it falls in the link-free fragment
    (`AR.ASL.isStarFree_of_link_free`) — a concrete instance of
    [jardine-2019]'s `ASL ⊊ SF` placement. -/
theorem hlhTier_link_free : ∀ i j p q, ¬ hlhTier.link i j p q := by
  intro i j p q hl
  rcases (AR.link_ofData i j p q).mp hl with
    ⟨-, -, -, ⟨-, -, h⟩ | ⟨-, -, h⟩⟩ <;> exact absurd h (List.not_mem_nil)

end Jardine2019
