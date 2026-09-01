/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Linglib.Phonology.Autosegmental.OCP
import Linglib.Phonology.Subregular.ContainsFactor
import Linglib.Phonology.Tone.Basic

/-!
# Jardine (2019): the expressivity of autosegmental grammars

[jardine-2019] defines, for a map `g` from symbols to autosegmental graph primitives
(Definition 1) extended to strings by merging concatenation (Definition 2), the stringset
`L(B^g)` of a finite set `B` of forbidden connected subgraphs — the strings whose graph
contains none of them — and the class `ASL^g` of such sets (§5.3). The tone class `ASL^{gT}`
uses `gT` of (23): `H` and `L` are a tone over a mora, `F` a falling `H L` contour over one;
merging fuses `gT(Hⁿ)` into a single `H` over `n` morae (Fig. 10). Theorem 2 places the
class strictly inside the star-free sets; Theorems 3 and 4 make it incomparable with SL,
TSL and SP.

`gT` on strings is `realizeMerged`, the tensor realization with its melody runs fused. Its
tier words and lines compute from the words (`AR.free_realizeMerged_iff_of_eq_ofWords`), so
membership in `L(B^{gT})` decides for concrete grammars. The unmerged `AR.realize` is the
project's bridge-only realization, kept for the contrast merging makes.

## Main definitions

* `Sym`, `gT` — Σ_T = {H, L, F} and (23).
* `ASL` — `L(B^{gT})`; the grammars `spreadGrammar` (26) and `utpGrammar` (33).

## Main results

* (27): `HH` and `HF` are out of `L({(26)})`, the listed strings up to length three in.
* (32): the listed strings of `L_UTP` are in `L(B_UTP)`; `HLH`, `LHHLH` and the unbounded
  plateau `HHLLHH` are out — while `HHLLHH` is free of `B_UTP` under the unmerged
  realization (`HHLLHH_free_realize`): the non-local reach that merging buys.
* Theorem 3's observation: `gT(HL)` is a subgraph of `gT(HF)` (`realizeMerged_HL_embeds_HF`),
  so no forbidden-subgraph grammar excludes `HL` without excluding `HF`
  (`not_mem_ASL_HF_of_not_mem_ASL_HL`).
* The link-free fragment of the unmerged class is star-free
  (`isStarFree_free_realize_of_link_free`): a grammar without association lines is a Boolean
  combination of per-tier factor constraints, each the inverse image of a star-free
  contains-factor language ([schutzenberger-1965], [mcnaughton-papert-1971]) along a tier
  projection; `utpGrammar`'s melody constraint is one (`isStarFree_free_realize_hlh`).
  Theorem 2 for the merged class, via FO-definability, is not formalized.
-/

namespace Jardine2019

open Autosegmental Tone Tone.TRN

/-- The string alphabet Σ_T = {H, L, F} (§5.2.2): a high, low or falling-toned mora. -/
inductive Sym | H | L | F
  deriving DecidableEq, Repr

/-- The melody of a symbol's primitive: `F` is the falling contour `H L`. -/
def Sym.melody : Sym → List TRN
  | .H => [TRN.H]
  | .L => [TRN.L]
  | .F => [TRN.H, TRN.L]

/-- The mora, the paper's tone-bearing unit. -/
abbrev μ : TBUKind := .mora

/-- `gT` (23): a symbol's melody over one mora, fully associated. -/
def gT (s : Sym) : TieredAR Bool (TwoTier TRN TBUKind) :=
  AR.ofWords s.melody [μ] fun _ _ => True

instance (s : Sym) : Finite (gT s).obj.V :=
  inferInstanceAs (Finite (AR.ofWords s.melody [μ] fun _ _ => True).obj.V)

theorem gT_eq (s : Sym) : gT s = AR.ofWords s.melody [μ] fun _ _ => True := rfl

/-- The merged realization of a string, read as a representation of words. -/
abbrev merged (w : List Sym) :=
  AR.ofWords (OCP.collapse (w.map Sym.melody).flatten) (w.map fun _ => [μ]).flatten
    (mergedLinks (w.map Sym.melody).flatten
      (blockLinks Sym.melody (fun _ => [μ]) (fun _ _ _ => True) w))

/-- The unmerged realization of a string, read as a representation of words. -/
abbrev unmerged (w : List Sym) :=
  AR.ofWords (w.map Sym.melody).flatten (w.map fun _ => [μ]).flatten
    (blockLinks Sym.melody (fun _ => [μ]) (fun _ _ _ => True) w)

/-- `L(B^{gT})` (§5.3): the strings whose merged realization is free of the grammar. -/
def ASL (B : List {F : TieredAR Bool (TwoTier TRN TBUKind) // Finite F.obj.V}) :
    Language Sym :=
  {w | (realizeMerged true gT w).Free B}

theorem mem_ASL_iff {B : List {F : TieredAR Bool (TwoTier TRN TBUKind) // Finite F.obj.V}}
    {w : List Sym} : w ∈ ASL B ↔ (merged w).Free B :=
  AR.free_realizeMerged_iff_of_eq_ofWords _ _ _ gT gT_eq B w

theorem free_realize_iff (B : List {F : TieredAR Bool (TwoTier TRN TBUKind) // Finite F.obj.V})
    (w : List Sym) : (AR.realize gT w).Free B ↔ (unmerged w).Free B :=
  AR.free_realize_iff_of_eq_ofWords _ _ _ gT gT_eq B w

/-! ### The grammars of (26) and (33) -/

/-- (26): a tone over two morae. -/
abbrev spread := AR.ofWords [H] [μ, μ] fun _ _ => True

/-- (3), the melody `H L H`. -/
abbrev hlh := AR.ofWords [H, L, H] ([] : List TBUKind) fun _ _ => False

/-- The falling contour: `H L` over one mora. -/
abbrev fall := AR.ofWords [H, L] [μ] fun _ _ => True

/-- The grammar of (26): no tone over two morae. -/
def spreadGrammar : List {F : TieredAR Bool (TwoTier TRN TBUKind) // Finite F.obj.V} :=
  [⟨spread, inferInstance⟩]

/-- `B_UTP` (33): no `H L H` melody, no contour. -/
def utpGrammar : List {F : TieredAR Bool (TwoTier TRN TBUKind) // Finite F.obj.V} :=
  [⟨hlh, inferInstance⟩, ⟨fall, inferInstance⟩]

theorem mem_ASL_spreadGrammar_iff (w : List Sym) :
    w ∈ ASL spreadGrammar ↔ ¬ spread.FactorEmbeds (merged w) := by
  simp only [mem_ASL_iff, spreadGrammar, AR.free_cons, AR.free_nil, and_true]

theorem mem_ASL_utpGrammar_iff (w : List Sym) :
    w ∈ ASL utpGrammar ↔ ¬ hlh.FactorEmbeds (merged w) ∧ ¬ fall.FactorEmbeds (merged w) := by
  simp only [mem_ASL_iff, utpGrammar, AR.free_cons, AR.free_nil, and_true]

instance (w : List Sym) : Decidable (w ∈ ASL spreadGrammar) :=
  decidable_of_iff _ (mem_ASL_spreadGrammar_iff w).symm

instance (w : List Sym) : Decidable (w ∈ ASL utpGrammar) :=
  decidable_of_iff _ (mem_ASL_utpGrammar_iff w).symm

/-! ### The data of (27) and (32) -/

/-- (27): `HH` and `HF` are out — their fused `H` spans two morae. -/
theorem HH_not_mem_ASL_spread : [.H, .H] ∉ ASL spreadGrammar := by decide

theorem HF_not_mem_ASL_spread : [.H, .F] ∉ ASL spreadGrammar := by decide

/-- (27): the listed strings up to length three are in. -/
theorem mem_ASL_spread :
    ∀ w ∈ [[], [.L], [.H], [.F], [.L, .L], [.L, .H], [.L, .F], [.H, .L], [.F, .H], [.F, .F],
      [.L, .L, .L], [.L, .L, .H], [.L, .L, .F], [.L, .H, .L], [.L, .F, .L], [.L, .F, .F],
      [.H, .L, .L], [.H, .L, .H], [.H, .L, .F]], w ∈ ASL spreadGrammar := by
  decide

/-- (32): the listed strings of `L_UTP` are in. -/
theorem mem_ASL_utp :
    ∀ w ∈ [[], [.L], [.H], [.L, .L], [.L, .H], [.H, .L], [.H, .H], [.L, .L, .L], [.L, .L, .H],
      [.L, .H, .L], [.L, .H, .H], [.H, .L, .L], [.H, .H, .L], [.H, .H, .H], [.L, .L, .L, .L],
      [.L, .L, .L, .H], [.L, .L, .H, .L], [.L, .L, .H, .H], [.L, .H, .L, .L], [.L, .H, .H, .L],
      [.L, .H, .H, .H], [.H, .L, .L, .L], [.H, .H, .L, .L], [.H, .H, .H, .L], [.H, .H, .H, .H]],
      w ∈ ASL utpGrammar := by
  decide

/-- `HLH` is out: its melody is `H L H`. -/
theorem HLH_not_mem_ASL_utp : [.H, .L, .H] ∉ ASL utpGrammar := by decide

/-- `LHHLH` is out: the `HH` plateau fuses and the melody reads `L H L H`. -/
theorem LHHLH_not_mem_ASL_utp : [.L, .H, .H, .L, .H] ∉ ASL utpGrammar := by decide

/-- The unbounded plateau `HHLLHH` is out: both plateaus fuse and the melody reads `H L H`,
at any widths. -/
theorem HHLLHH_not_mem_ASL_utp : [.H, .H, .L, .L, .H, .H] ∉ ASL utpGrammar := by decide

/-- The same string is free of `B_UTP` under the unmerged realization: its melody reads
`H H L L H H`, and no three adjacent nodes spell `H L H` — the reach merging buys. -/
theorem HHLLHH_free_realize : (AR.realize gT [.H, .H, .L, .L, .H, .H]).Free utpGrammar := by
  rw [free_realize_iff]
  simp only [utpGrammar, AR.free_cons, AR.free_nil, and_true]
  decide

/-! ### Theorem 3: contours contain their pure counterparts -/

/-- `gT(HL)` is a subgraph of `gT(HF)`: the falling contour on the second mora contains
the `L` on it. -/
theorem realizeMerged_HL_embeds_HF :
    (realizeMerged true gT [.H, .L]).FactorEmbeds (realizeMerged true gT [.H, .F]) :=
  (AR.factorEmbeds_congr
    (AR.tierWord_realizeMerged_eq_tierWord_ofWords _ _ _ gT gT_eq _)
    (AR.link_realizeMerged_iff_link_ofWords _ _ _ gT gT_eq _)
    (AR.tierWord_realizeMerged_eq_tierWord_ofWords _ _ _ gT gT_eq _)
    (AR.link_realizeMerged_iff_link_ofWords _ _ _ gT gT_eq _)).mpr (by decide)

/-- Hence no forbidden-subgraph grammar excludes `HL` without excluding `HF` (Theorem 3):
a subgraph of `gT(HL)` is a subgraph of `gT(HF)`. -/
theorem not_mem_ASL_HF_of_not_mem_ASL_HL
    (B : List {F : TieredAR Bool (TwoTier TRN TBUKind) // Finite F.obj.V})
    (h : [.H, .L] ∉ ASL B) : [.H, .F] ∉ ASL B :=
  fun hHF => h fun F hF hemb => hHF F hF (hemb.trans realizeMerged_HL_embeds_HF)

/-! ### The link-free fragment of the unmerged class is star-free -/

section StarFree

variable {S : Type*} {ι : Type*} [Finite ι] {τ : ι → Type*}
  (g₀ : S → TieredAR ι τ) [∀ s, Finite (g₀ s).obj.V]

/-- For a link-free forbidden factor, the strings whose unmerged realization contains it
form a star-free language: the intersection of per-tier factor constraints, each the
inverse image of a star-free contains-factor language along a tier projection. -/
theorem isStarFree_factorEmbeds_realize_of_link_free (F : TieredAR ι τ) [Finite F.obj.V]
    (hF : ∀ i j p q, ¬ F.link i j p q) :
    Language.IsStarFree {w : List S | F.FactorEmbeds (AR.realize g₀ w)} := by
  have hset : {w : List S | F.FactorEmbeds (AR.realize g₀ w)}
      = ⋂ i, {w : List S | F.tierWord i <:+: AR.tierProj g₀ i (FreeMonoid.ofList w)} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, AR.factorEmbeds_iff_infix_of_link_free hF,
      AR.tierProj_ofList]
    exact Iff.rfl
  rw [hset]
  exact Language.IsStarFree.iInter fun i =>
    (Language.isStarFree_containsFactor (F.tierWord i)).comap (AR.tierProj g₀ i)

/-- A grammar without association lines specifies a star-free set of strings under the
unmerged realization. -/
theorem isStarFree_free_realize_of_link_free
    (B : List {F : TieredAR ι τ // Finite F.obj.V})
    (hB : ∀ F ∈ B, ∀ i j p q, ¬ F.val.link i j p q) :
    Language.IsStarFree {w : List S | (AR.realize g₀ w).Free B} := by
  induction B with
  | nil =>
    simpa [AR.free_nil] using Language.isStarFree_univ (α := S)
  | cons F B ih =>
    have hset : {w : List S | (AR.realize g₀ w).Free (F :: B)} =
        {w : List S | F.val.FactorEmbeds (AR.realize g₀ w)}ᶜ ∩
          {w : List S | (AR.realize g₀ w).Free B} := by
      ext w
      simp [AR.free_cons]
    rw [hset]
    exact (isStarFree_factorEmbeds_realize_of_link_free g₀ F.val
      (hB F (List.mem_cons_self ..))).compl.inter
      (ih fun F' hF' => hB F' (List.mem_cons_of_mem _ hF'))

end StarFree

/-- The melody constraint of `B_UTP` is link-free, so under the unmerged realization it
specifies a star-free set. -/
theorem isStarFree_free_realize_hlh :
    Language.IsStarFree {w : List Sym | (AR.realize gT w).Free [⟨hlh, inferInstance⟩]} :=
  isStarFree_free_realize_of_link_free gT _ fun F hF => by
    rw [List.mem_singleton] at hF
    subst hF
    exact AR.not_link_ofWords_false _ _

end Jardine2019
