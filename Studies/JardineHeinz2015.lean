/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.MergeConcat
public import Linglib.Phonology.Tone.Basic

/-!
# Jardine and Heinz (2015): A Concatenation Operation to Derive Autosegmental Graphs

Jardine and Heinz derive autosegmental graphs by concatenating graph primitives. Concatenation
bridges the two graphs tier by tier and merges the last melody node of the first with the first
melody node of the second when the two bear the same label (`AR.mergeConcat`); a string denotes
the left fold of its symbols' primitives (`AR.mergeRealize`). The operation has the empty graph
as unit and is associative, and it preserves the No-Crossing Constraint and, over OCP-clean
primitives, the OCP; these are the theorems of `Autosegmental/MergeConcat.lean`.

Because only the seam merges, a primitive that violates the OCP keeps its violation. The
authors use this for Kishambaa, where a high-toned noun with a downstepped second high contrasts
with one whose high spreads over both morae: a primitive `H H` with only its second `H` linked
derives the downstep, and concatenating then collapsing every run, the method they set aside,
would derive the spread instead.

## Main statements

* `mergeConcat_G₁_G₂`: Example 3, the merge of `b` with `b` at the seam (Figure 4).
* `mergeRealize_γ₁_γ₂`, `mergeRealize_γ₁_γ₁`: the Kishambaa graphs of Figure 12.
* `realizeMerged_γ₁_γ₂`, `not_nonempty_fullIso_realizeMerged`: collapsing after concatenation
  derives the spread graph for the downstep form, so it does not agree with merging
  concatenation once a primitive violates the OCP.

## References

* [jardine-heinz-2015]
-/

@[expose] public section

namespace JardineHeinz2015

open Autosegmental

/-! ### Example 1: concatenation merges the seam -/

/-- The melody symbols `a` and `b` of Example 1. -/
inductive Mel
  | a
  | b
  deriving DecidableEq

/-- Example 1's labels: melody symbols over `true`, and the one timing symbol `c` over
`false`. -/
abbrev Γ := TwoTier Mel Unit

/-- `G₁` of Figure 2: the melody `a b`, both associated to one timing node. -/
abbrev G₁ : TieredAR Bool Γ := AR.primitive [.a, .b] ()

/-- `G₂` of Figure 2: `b` over a timing node. -/
abbrev G₂ : TieredAR Bool Γ := AR.primitive [.b] ()

/-- The graph of Figure 4: `a` then the merged `b`, over two timing nodes, with the merged `b`
associated to both. -/
abbrev fig4 : TieredAR Bool Γ := AR.ofWords [.a, .b] [(), ()] fun p q ↦ q = 0 ∨ p = 1

/-- Concatenating `G₁` and `G₂` merges their `b` nodes (Example 3, Figure 4). -/
theorem mergeConcat_G₁_G₂ : Nonempty (Graph.Iso (AR.mergeConcat true G₁ G₂).obj fig4.obj) := by
  refine AR.nonempty_fullIso_iff.mpr ⟨fun i ↦ ?_, AR.link_iff_of_true_false fun r s ↦ ?_⟩
  · cases i <;> simp [OCP.mergeAppend]
  · simp only [AR.link_mergeConcat, AR.link_ofWords, AR.mergeOffset]
    simp [OCP.mergeOffset]
    omega

/-! ### Kishambaa: an OCP-violating primitive -/

open Tone Tone.TRN

/-- The mora, the tone-bearing unit. -/
abbrev μ : TBUKind := .mora

/-- The symbols of the Kishambaa alphabet (Figure 13). -/
inductive Sym
  | γ₁
  | γ₂
  deriving DecidableEq

/-- `γ₁` is a high-toned mora; `γ₂` is a mora carrying a high preceded by a floating high. -/
def Sym.melody : Sym → List TRN
  | .γ₁ => [H]
  | .γ₂ => [H, H]

/-- The lines of a symbol's primitive: `γ₁`'s high is linked, and only the second high of
`γ₂`. -/
def Sym.lines : Sym → ℕ → ℕ → Prop
  | .γ₁ => fun _ _ ↦ True
  | .γ₂ => fun p _ ↦ p = 1

instance : ∀ s : Sym, DecidableRel s.lines
  | .γ₁ => fun _ _ ↦ inferInstanceAs (Decidable True)
  | .γ₂ => fun p _ ↦ inferInstanceAs (Decidable (p = 1))

/-- The primitives of Figure 13. -/
def g (s : Sym) : TieredAR Bool (TwoTier TRN TBUKind) := AR.ofWords s.melody [μ] s.lines

instance (s : Sym) : Finite (g s).obj.V := inferInstanceAs (Finite (AR.ofWords _ _ _).obj.V)

/-- `g(γ₂)` violates the OCP. -/
theorem not_isCleanAt_g_γ₂ : ¬ (g .γ₂).IsCleanAt true := by
  simp [AR.IsCleanAt, g, Sym.melody]

/-- Figure 12a, 'snake': one high spread over two morae. -/
abbrev snake : TieredAR Bool (TwoTier TRN TBUKind) := AR.ofWords [H] [μ, μ] fun _ _ ↦ True

/-- Figure 12b, 'sheep': a high and a downstepped high, one per mora. -/
abbrev sheep : TieredAR Bool (TwoTier TRN TBUKind) := AR.ofWords [H, H] [μ, μ] fun p q ↦ p = q

/-- `γ₁γ₁` derives the spread high of Figure 12a. -/
theorem mergeRealize_γ₁_γ₁ :
    Nonempty (Graph.Iso (AR.mergeRealize true g [.γ₁, .γ₁]).obj snake.obj) := by
  refine AR.nonempty_fullIso_iff.mpr ⟨fun i ↦ ?_, AR.link_iff_of_true_false fun r s ↦ ?_⟩
  · cases i <;> simp [AR.mergeRealize, AR.mergeStep, g, Sym.melody, OCP.mergeAppend]
  · simp only [AR.mergeRealize, AR.mergeStep, List.foldl_cons, List.foldl_nil,
      AR.link_mergeConcat, AR.link_ofWords, AR.mergeOffset, g, Sym.melody, Sym.lines]
    simp [OCP.mergeOffset]
    omega

/-- `γ₁γ₂` derives the high and downstepped high of Figure 12b: the floating high of `γ₂`
merges with the high of `γ₁`, and the linked high stays distinct. -/
theorem mergeRealize_γ₁_γ₂ :
    Nonempty (Graph.Iso (AR.mergeRealize true g [.γ₁, .γ₂]).obj sheep.obj) := by
  refine AR.nonempty_fullIso_iff.mpr ⟨fun i ↦ ?_, AR.link_iff_of_true_false fun r s ↦ ?_⟩
  · cases i <;> simp [AR.mergeRealize, AR.mergeStep, g, Sym.melody, OCP.mergeAppend]
  · simp only [AR.mergeRealize, AR.mergeStep, List.foldl_cons, List.foldl_nil,
      AR.link_mergeConcat, AR.link_ofWords, AR.mergeOffset, g, Sym.melody, Sym.lines]
    simp [OCP.mergeOffset]
    omega

/-- Collapsing every run after concatenating merges all three highs of `γ₁γ₂`, deriving the
spread graph of Figure 12a instead. -/
theorem realizeMerged_γ₁_γ₂ :
    Nonempty (Graph.Iso (realizeMerged true g [.γ₁, .γ₂]).obj snake.obj) := by
  refine AR.nonempty_fullIso_iff.mpr ⟨fun i ↦ ?_, AR.link_iff_of_true_false fun r s ↦ ?_⟩
  · refine (AR.tierWord_realizeMerged_eq_tierWord_ofWords Sym.melody (fun _ ↦ [μ]) Sym.lines
      _ i).trans ?_
    cases i
    · simp
    · simp only [AR.tierWord_ofWords_true]
      decide
  · refine (AR.link_realizeMerged_iff_link_ofWords Sym.melody (fun _ ↦ [μ]) Sym.lines
      _ true false r s).trans ?_
    rw [AR.link_ofWords, AR.link_ofWords]
    constructor
    · rintro ⟨hr, hs, -⟩
      exact ⟨hr, hs, trivial⟩
    · rintro ⟨hr, hs, -⟩
      simp only [List.length_singleton, Nat.lt_one_iff] at hr
      subst hr
      refine ⟨by decide, hs, ?_⟩
      revert s
      decide

/-- Once a primitive violates the OCP, collapsing after concatenation does not compute
merging concatenation: the two realizations of `γ₁γ₂` differ. -/
theorem not_nonempty_fullIso_realizeMerged :
    ¬ Nonempty (Graph.Iso (AR.mergeRealize true g [.γ₁, .γ₂]).obj
      (realizeMerged true g [.γ₁, .γ₂]).obj) := by
  rintro ⟨e⟩
  obtain ⟨e₁⟩ := mergeRealize_γ₁_γ₂
  obtain ⟨e₂⟩ := realizeMerged_γ₁_γ₂
  have := AR.tierWord_eq_of_iso (e₁.symm.trans (e.trans e₂)) true
  simp at this

end JardineHeinz2015
