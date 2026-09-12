import Linglib.Syntax.DependencyGrammar.Projectivity
import Linglib.Morphology.Word.Basic
import Linglib.Data.Treebank.Coverage.Kuhlmann2013
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# Kuhlmann (2013): Mildly Non-Projective Dependency Grammar

This file formalizes the structural side of [kuhlmann-2013], which reads lexicalized linear
context-free rewriting systems as dependency grammars and measures the non-projectivity that
parsing them has to pay for. The fan-out of a rule extracted from a treebank is the
block-degree of its head, one more than the substrate's gap degree (`blockDegree`), so
projectivity is block-degree one (`isProjective_iff_blockDegree_eq_one`). Well-nestedness,
which makes parsing polynomial through binarization, fails exactly when two sibling nodes
have interleaving yields (`not_isWellNested_iff_siblings`, the paper's Lemma 9 in the
substrate's terms). The Dutch and German verb clusters of Figure 1 separate the projective
from the non-projective order while keeping the dependencies fixed, and the trees of
Figures 10 and 11 witness block-degrees 2 and 3 and the independence of well-nestedness from
block-degree.

The treebank counts of Tables 3 and 4 are the rows of
`Data/Treebank/Coverage/Kuhlmann2013.json`, over which the paper's percentages are
recomputed: fan-out 1 loses between 11.16% and 23.15% of the trees (`treeLoss_projective`),
allowing fan-out 2 recovers more than 94% of the lost rules and trees
(`reduction_gapDegreeLe1`), and adding well-nestedness still recovers more than 92% of the
rules (`reduction_wellNested`).

## Implementation notes

Positions are zero-based, so node `i` of a figure is position `i - 1`. The substrate's
`Graph.IsWellNested` is the paper's definition under the paper's own gloss: yields may overlap
only when one node dominates the other. Block-degree is the gap degree plus one, as the
paper's footnote on gap-degree observes. Percentages are recomputed from the rows as rounded
hundredths of a percent, the precision the paper prints. The lexicalized LCFRS machinery,
canonical grammars, the parsing algorithm, and the NP-hardness result are not formalized.

## TODO

* Table 3 prints 5,839 rules for Arabic, on which the fan-out 1 loss of 411 rules is 7.04%,
  not the 0.74% the paper states; the printed value is kept and Arabic is excluded from
  `ruleLoss_projective`.
* The paper gives Turkish's well-nested rule-loss reduction as 92.65%; the rows give 92.64%.
-/

namespace Kuhlmann2013

open DependencyGrammar Relation
open Morphology (Word)
open Data.Treebank.Coverage

variable {n : ℕ} {g : Graph n}

/-! ### Block-degree (§7.1) -/

/-- The block-degree of a graph: the maximal number of blocks a node's yield falls into, one
more than the gap degree. -/
def blockDegree (g : Graph n) : ℕ := g.gapDegree + 1

/-- A tree is projective iff its block-degree is 1. -/
theorem isProjective_iff_blockDegree_eq_one :
    g.IsProjective ↔ blockDegree g = 1 := by
  rw [Graph.isProjective_iff_gapDegree_eq_zero, blockDegree]
  omega

/-! ### Well-nestedness (§8.1) -/

/-- Lemma 9: a tree is ill-nested iff two sibling nodes have interleaving yields. -/
theorem not_isWellNested_iff_siblings (hT : g.IsTree) :
    ¬ g.IsWellNested ↔ ∃ p u v, g.Adj p u ∧ g.Adj p v ∧ u ≠ v ∧ g.Interleave u v := by
  constructor
  · intro h
    simp only [Graph.IsWellNested, not_forall, not_or] at h
    obtain ⟨u, v, hI, huv, hvu⟩ := h
    have : Fact g.IsTree := ⟨hT⟩
    let u₀ : DominanceOrder g := u
    let v₀ : DominanceOrder g := v
    have hau : u₀ ⊓ v₀ ≤ u₀ := inf_le_left
    have hav : u₀ ⊓ v₀ ≤ v₀ := inf_le_right
    change Dominates g _ _ at hau hav
    rcases ReflTransGen.cases_head hau with hu | ⟨u', hu', hu'u⟩
    · rw [hu] at hav
      exact absurd hav huv
    rcases ReflTransGen.cases_head hav with hv | ⟨v', hv', hv'v⟩
    · rw [hv] at hau
      exact absurd hau hvu
    refine ⟨_, u', v', hu', hv', λ he => ?_, ?_⟩
    · subst he
      let u'₀ : DominanceOrder g := u'
      have h₁ : u'₀ ≤ u₀ := hu'u
      have h₂ : u'₀ ≤ v₀ := hv'v
      have hle := le_inf h₁ h₂
      change Dominates g _ _ at hle
      exact not_adj_dominates hT.acyclic hu' hle
    · obtain ⟨a, ha, b, hb, c, hc, d, hd, halt⟩ := hI
      exact ⟨a, hu'u.trans ha, b, hu'u.trans hb, c, hv'v.trans hc, d, hv'v.trans hd, halt⟩
  · rintro ⟨p, u, v, hpu, hpv, huv, hI⟩ hW
    rcases hW u v hI with h | h
    · exact not_adj_dominates hT.acyclic hpu
        ((Dominates.antisymm hT.acyclic (Dominates.to_head hT h huv hpv) (.single hpu)) ▸ .refl)
    · exact not_adj_dominates hT.acyclic hpv
        ((Dominates.antisymm hT.acyclic (Dominates.to_head hT h huv.symm hpu) (.single hpv)) ▸
          .refl)

/-! ### Figure 1: nested against cross-serial

The German order nests the verb–argument dependencies and is projective; the Dutch order
crosses them and is not, at gap degree 1. -/

/-- Dutch cross-serial: *dat Jan Piet Marie zag helpen lezen*. -/
def dutchCrossSerial : Graph 7 :=
  .ofArcs
    [Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB,
     Word.mk' "lezen" .VERB]
    0
    [(0, 4, .dep), (4, 1, .nsubj), (4, 5, .xcomp),
     (5, 2, .nsubj), (5, 6, .xcomp), (6, 3, .nsubj)]

/-- German nested: *dass Jan Piet Marie lesen helfen sah*. -/
def germanNested : Graph 7 :=
  .ofArcs
    [Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB,
     Word.mk' "sah" .VERB]
    0
    [(0, 6, .dep), (6, 1, .nsubj), (6, 5, .xcomp),
     (5, 2, .nsubj), (5, 4, .xcomp), (4, 3, .nsubj)]

theorem dutchCrossSerial_isTree : dutchCrossSerial.IsTree := by decide
theorem germanNested_isTree : germanNested.IsTree := by decide

/-- The cross-serial order is non-projective and the nested order is projective. -/
theorem figure1_projectivity : ¬ dutchCrossSerial.IsProjective ∧ germanNested.IsProjective := by
  decide

/-- Block-degree 2 against block-degree 1: the fan-out the extracted rule for *zag* needs. -/
theorem figure1_blockDegree :
    blockDegree dutchCrossSerial = 2 ∧ blockDegree germanNested = 1 := by
  decide

/-- Cross-serial dependencies are well-nested, though not planar. -/
theorem dutchCrossSerial_isWellNested :
    dutchCrossSerial.IsWellNested ∧ ¬ dutchCrossSerial.IsPlanar := by
  decide +kernel

/-! ### Figures 10 and 11: block-degree and well-nestedness -/

/-- An unlabelled position. -/
private def dot : Word := Word.mk' "•" .X

/-- Figure 10, `D₁`: the yield of node 2 falls into the blocks {2, 3} and {6}. -/
def fig10D1 : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, .dep), (0, 4, .dep), (4, 3, .dep), (1, 2, .dep), (2, 5, .dep)]

/-- Figure 10, `D₂`: the yield of node 1 falls into the blocks {1}, {3} and {6}. -/
def fig10D2 : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 1
    [(1, 0, .dep), (1, 4, .dep), (4, 3, .dep), (0, 2, .dep), (2, 5, .dep)]

/-- Block-degrees 2 and 3 (Example 6). -/
theorem figure10_blockDegree : blockDegree fig10D1 = 2 ∧ blockDegree fig10D2 = 3 := by
  decide

/-- Figure 11, `D₁`: non-projective with no overlapping yields at all. -/
def fig11D1 : Graph 4 :=
  .ofArcs [dot, dot, dot, dot] 1 [(1, 0, .dep), (1, 2, .dep), (0, 3, .dep)]

/-- Figure 11, `D₂`: the yields of nodes 1 and 2 overlap, but node 1 dominates node 2. -/
def fig11D2 : Graph 4 :=
  .ofArcs [dot, dot, dot, dot] 0 [(0, 2, .dep), (2, 1, .dep), (1, 3, .dep)]

/-- Figure 11, `D₃`: the yields of the sibling nodes 2 and 3 overlap. -/
def fig11D3 : Graph 5 :=
  .ofArcs [dot, dot, dot, dot, dot] 0 [(0, 2, .dep), (2, 4, .dep), (0, 1, .dep), (1, 3, .dep)]

/-- Both well-nested trees of Figure 11 are non-projective (Example 8). -/
theorem figure11_wellNested :
    (fig11D1.IsWellNested ∧ ¬ fig11D1.IsProjective) ∧
      (fig11D2.IsWellNested ∧ ¬ fig11D2.IsProjective) := by
  decide +kernel

/-- In `D₂` the overlapping yields belong to a node and its descendant. -/
theorem fig11D2_interleave : fig11D2.Interleave 0 1 ∧ Dominates fig11D2 0 1 := by
  decide +kernel

/-- `D₃` is ill-nested, with the siblings of Lemma 9 at positions 1 and 2. -/
theorem fig11D3_not_isWellNested : ¬ fig11D3.IsWellNested :=
  (not_isWellNested_iff_siblings (by decide)).2
    ⟨0, 1, 2, by decide, by decide, by decide, by decide +kernel⟩

/-- Well-nestedness is independent of block-degree beyond 1: `D₂` and `D₃` both have
block-degree 2. -/
theorem figure11_blockDegree : blockDegree fig11D2 = 2 ∧ blockDegree fig11D3 = 2 := by
  decide

/-! ### Tables 3 and 4: coverage on dependency treebanks (§7.4, §8.4) -/

/-- The rows of Tables 3 and 4. -/
abbrev rows : List Row := Data.Treebank.Coverage.Kuhlmann2013.rows

/-- The loss under a row's constraint, in hundredths of a percent, rounded as the paper
prints it. -/
def lossBp (r : Row) : ℤ := round ((1 - r.coverage) * 10000)

/-- The items a treebank loses under a constraint. -/
def lost (treebank : String) (item : Item) (c : Constraint) : ℕ :=
  match rows.find? λ r => r.treebank = treebank ∧ r.item = item ∧ r.constraint = c with
  | some r => r.total - r.value
  | none => 0

/-- The reduction in loss under a constraint relative to the fan-out 1 baseline, in
hundredths of a percent. -/
def reductionBp (treebank : String) (item : Item) (c : Constraint) : ℤ :=
  round ((1 - (lost treebank item c : ℚ) / lost treebank item .projective) * 10000)

/-- Fan-out 1 loses between 11.16% (Arabic) and 23.15% (Czech) of the trees. -/
theorem treeLoss_projective :
    ∀ r ∈ rows, r.item = .trees → r.constraint = .projective →
      1116 ≤ lossBp r ∧ lossBp r ≤ 2315 := by
  decide +kernel

/-- Fan-out 1 loses between 1.23% (Danish) and 1.75% (Slovene) of the rules, Arabic's
printed total aside. -/
theorem ruleLoss_projective :
    ∀ r ∈ rows, r.item = .rules → r.constraint = .projective → r.treebank ≠ "Arabic" →
      123 ≤ lossBp r ∧ lossBp r ≤ 175 := by
  decide +kernel

/-- Allowing fan-out 2 reduces rule loss by 94.16% (Turkish) to 99.76% (Arabic) and tree loss
by 94.31% (Turkish) to 99.39% (Arabic). -/
theorem reduction_gapDegreeLe1 :
    ∀ r ∈ rows, r.constraint = .gapDegreeLe 1 →
      (r.item = .rules →
        9416 ≤ reductionBp r.treebank .rules (.gapDegreeLe 1) ∧
          reductionBp r.treebank .rules (.gapDegreeLe 1) ≤ 9976) ∧
      (r.item = .trees →
        9431 ≤ reductionBp r.treebank .trees (.gapDegreeLe 1) ∧
          reductionBp r.treebank .trees (.gapDegreeLe 1) ≤ 9939) := by
  decide +kernel

/-- Block-degree 2 costs Czech 0.02% of its rules and under 0.5% of its trees. -/
theorem czech_gapDegreeLe1 :
    ∀ r ∈ rows, r.treebank = "Czech" → r.constraint = .gapDegreeLe 1 →
      (r.item = .rules → lossBp r = 2) ∧ (r.item = .trees → lossBp r < 50) := by
  decide +kernel

/-- Well-nested rules of fan-out at most 2 still reduce rule loss by more than 92% relative
to fan-out 1, up to 99.51% (Arabic). -/
theorem reduction_wellNested :
    ∀ r ∈ rows, r.constraint = .gapDegreeLeWellNested 1 → r.item = .rules →
      9264 ≤ reductionBp r.treebank .rules (.gapDegreeLeWellNested 1) ∧
        reductionBp r.treebank .rules (.gapDegreeLeWellNested 1) ≤ 9951 := by
  decide +kernel

end Kuhlmann2013
