/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Linglib.Phonology.Autosegmental.OCP
import Linglib.Phonology.Subregular.ContainsFactor
import Linglib.Phonology.Tone.Basic
import Linglib.Data.Examples.Jardine2019

/-!
# Jardine (2019): the expressivity of autosegmental grammars

This file formalizes [jardine-2019], the class of autosegmentally strictly local stringsets. A
map `g` from symbols to autosegmental graph primitives, Definition 1, extends to strings by
merging concatenation, Definition 2, and a finite set `B` of forbidden connected subgraphs
describes the strings whose graph contains none of them, `L(B^g)`, Section 5.3; `ASL^g` is the
class of such sets. The tone class uses `gT` of (23): `H` and `L` are a tone over a mora and `F` a
falling `H L` contour over one, and merging fuses a run of `H`s into a single `H` over its morae,
Figure 10, which is what lets a local grammar state a non-local dependency. On strings `gT` is
`realizeMerged`, whose tier words and lines compute from the words, so membership in `L(B^{gT})`
decides: the grammar (26) admits exactly the strings of (27) and excludes `HH` and `HF`, and the
grammar `B_UTP`, (33), admits the strings of `L_UTP`, (32) (`rows_agree`), and excludes the
unbounded plateau `HHLLHH`, which the unmerged realization leaves free
(`HHLLHH_free_realize`). Theorem 3's observation, that `gT(HL)` is a subgraph of `gT(HF)`, so
that no forbidden-subgraph grammar excludes `HL` without excluding `HF`, is
`not_mem_ASL_HF_of_not_mem_ASL_HL`; and the link-free fragment of the unmerged class is
star-free, each forbidden factor the inverse image of a contains-factor language along a tier
projection ([schutzenberger-1965], [mcnaughton-papert-1971], `isStarFree_free_realize_of_link_free`).

## Implementation notes

* The unmerged `AR.realize` is kept for the contrast merging makes; Theorem 2 for the merged
  class, by first-order definability, and the incomparability halves of Theorems 3 and 4 that
  rest on it are not formalized.
* The stringsets (27) and (32) are rows; `HLH`, `LHHLH` and `HHLLHH` are the file's witnesses of
  the melody constraint at increasing widths.

## References

* [jardine-2019]
* [schutzenberger-1965]
* [mcnaughton-papert-1971]
-/

namespace Jardine2019

open Autosegmental Data.Examples Tone Tone.TRN

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
  AR.ofWords s.melody [μ] λ _ _ => True

instance (s : Sym) : Finite (gT s).obj.V :=
  inferInstanceAs (Finite (AR.ofWords s.melody [μ] λ _ _ => True).obj.V)

theorem gT_eq (s : Sym) : gT s = AR.ofWords s.melody [μ] λ _ _ => True := rfl

/-- The merged realization of a string, read as a representation of words. -/
abbrev merged (w : List Sym) :=
  AR.ofWords (OCP.collapse (w.map Sym.melody).flatten) (w.map λ _ => [μ]).flatten
    (mergedLinks (w.map Sym.melody).flatten
      (blockLinks Sym.melody (λ _ => [μ]) (λ _ _ _ => True) w))

/-- The unmerged realization of a string, read as a representation of words. -/
abbrev unmerged (w : List Sym) :=
  AR.ofWords (w.map Sym.melody).flatten (w.map λ _ => [μ]).flatten
    (blockLinks Sym.melody (λ _ => [μ]) (λ _ _ _ => True) w)

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
abbrev spread := AR.ofWords [H] [μ, μ] λ _ _ => True

/-- (3), the melody `H L H`. -/
abbrev hlh := AR.ofWords [H, L, H] ([] : List TBUKind) λ _ _ => False

/-- The falling contour: `H L` over one mora. -/
abbrev fall := AR.ofWords [H, L] [μ] λ _ _ => True

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

/-- The two grammars of the paper's examples. -/
inductive Grammar
  | spread
  | utp
  deriving DecidableEq

/-- A row: a string, the grammar it is tested against, and whether it is in the set. -/
structure Row where
  string : List Sym
  grammar : Grammar
  member : Bool
  deriving DecidableEq

/-- A symbol from its spelling. -/
def Sym.ofChar : Char → Sym
  | 'H' => .H
  | 'F' => .F
  | _ => .L

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let w ← e.feature? "string"
  let g ← match e.feature? "grammar" with
    | some "26" => some Grammar.spread
    | some "33" => some Grammar.utp
    | _ => none
  let m ← e.feature? "member"
  some ⟨w.toList.map Sym.ofChar, g, m = "yes"⟩

/-- The strings of (27) with the `HH` and `HF` the grammar (26) excludes, and those of (32). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The set a row's grammar describes. -/
def Grammar.set : Grammar → Language Sym
  | .spread => ASL spreadGrammar
  | .utp => ASL utpGrammar

instance (g : Grammar) (w : List Sym) : Decidable (w ∈ g.set) := by
  cases g <;> simp only [Grammar.set] <;> infer_instance

/-- The grammar (26) admits the strings of (27) and excludes `HH` and `HF`, whose fused `H`
spans two morae, and `B_UTP` admits the strings of `L_UTP`, (32). -/
theorem rows_agree : ∀ r ∈ rows, r.string ∈ r.grammar.set ↔ r.member = true := by decide

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
  λ hHF => h λ F hF hemb => hHF F hF (hemb.trans realizeMerged_HL_embeds_HF)

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
  exact Language.IsStarFree.iInter λ i =>
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
      (ih λ F' hF' => hB F' (List.mem_cons_of_mem _ hF'))

end StarFree

/-- The melody constraint of `B_UTP` is link-free, so under the unmerged realization it
specifies a star-free set. -/
theorem isStarFree_free_realize_hlh :
    Language.IsStarFree {w : List Sym | (AR.realize gT w).Free [⟨hlh, inferInstance⟩]} :=
  isStarFree_free_realize_of_link_free gT _ λ F hF => by
    rw [List.mem_singleton] at hF
    subst hF
    exact AR.not_link_ofWords_false _ _

end Jardine2019
