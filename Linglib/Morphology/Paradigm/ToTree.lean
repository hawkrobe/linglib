/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Word.Tree
import Linglib.Morphology.Paradigm.Function

/-!
# The paradigm function into word trees
[bonami-stump-2016] [spencer-2013]

The engine's state type `Z` is unconstrained, so the paradigm function runs at
`Z := Word.Tree M` as readily as at material sequences. An affix-transparent
vocabulary interprets into both, and `toList` intertwines the two runs
(`toList_paradigmFunction_tree`); the emitted tree's stem is the chosen leaf
under any classification counting the vocabulary's material as inflectional
([spencer-2013]'s inflection-hood by provenance), and a kind-coherent
vocabulary emits a kind-coherent tree.

## Main declarations

* `AffixAction` — a prefix or suffix action carrying its affix; interprets
  into the engine at trees (`toTreeAction`) and at sequences (`toAction`)
* `toList_paradigmFunction_tree`, `stem_paradigmFunction_tree`,
  `isKindCoherent_paradigmFunction_tree` — linearization, stem, and coherence
  of the tree-valued run
-/

namespace Morphology.PFM

open Morphology Morphology.Exponence Morphology.Word

variable {M L P : Type*}

/-! ### The affix-transparent vocabulary -/

/-- A prefix or suffix action carrying its affix; rules over `AffixAction`
cannot carry referrals. -/
inductive AffixAction (M : Type*) where
  /-- Prepend the affix. -/
  | pre (m : M)
  /-- Append the affix. -/
  | suf (m : M)

/-- The affix an action attaches. -/
def AffixAction.material : AffixAction M → M
  | .pre m => m
  | .suf m => m

/-- Apply an affix action to a tree. -/
def AffixAction.apply : AffixAction M → Word.Tree M → Word.Tree M
  | .pre m, t => .prefixed m t
  | .suf m, t => .suffixed t m

/-- Apply an affix action to a material sequence. -/
def AffixAction.applyList : AffixAction M → List M → List M
  | .pre m, l => m :: l
  | .suf m, l => l ++ [m]

/-- The engine interpretation at tree-valued state. -/
def AffixAction.toTreeAction (a : AffixAction M) : Action (Word.Tree M) P :=
  .const a.apply

/-- The engine interpretation at material sequences. -/
def AffixAction.toAction (a : AffixAction M) : Action (List M) P :=
  .const a.applyList

theorem AffixAction.toList_apply (a : AffixAction M) (t : Word.Tree M) :
    (a.apply t).toList = a.applyList t.toList := by
  cases a <;> rfl

theorem AffixAction.apply_stem {infl : M → Bool} (a : AffixAction M)
    (t : Word.Tree M) (h : infl a.material) :
    (a.apply t).stem infl = t.stem infl := by
  cases a <;> simp [apply, material] at h ⊢ <;> simp [Word.Tree.stem, h]

/-- The affix is bound on the side `apply` places it. -/
def AffixAction.KindCoherent : AffixAction Morph → Prop
  | .pre m => m.side? = some .before
  | .suf m => m.side? = some .after

theorem AffixAction.apply_isKindCoherent {a : AffixAction Morph} (ha : a.KindCoherent)
    {t : Word.Tree Morph} (ht : t.IsKindCoherent) : (a.apply t).IsKindCoherent := by
  cases a <;> exact ⟨ha, ht⟩

/-! ### The tree-valued run -/

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

theorem toList_evalBlockForm (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (t : Word.Tree M) (σ : P) :
    (evalBlockForm (fun t => LindexZ t.toList)
        (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ)).toList
      = evalBlockForm LindexZ (b.map (Rule.mapPayload AffixAction.toAction))
          (t.toList, σ) := by
  simp only [evalBlockForm, selectMinimal_map_payload]
  rcases selectMinimal b (LindexZ t.toList, σ) with _ | ⟨rk, rp, rpl⟩
  · rfl
  · cases rpl <;> rfl

theorem stem_evalBlockForm {infl : M → Bool} (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (hb : ∀ r ∈ b, infl r.payload.material)
    (t : Word.Tree M) (σ : P) :
    (evalBlockForm (fun t => LindexZ t.toList)
        (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ)).stem infl
      = t.stem infl := by
  simp only [evalBlockForm, selectMinimal_map_payload]
  cases h : selectMinimal b (LindexZ t.toList, σ) with
  | none => rfl
  | some r => exact AffixAction.apply_stem r.payload t (hb r (selectMinimal_mem h))

theorem isKindCoherent_evalBlockForm (LindexZ : List Morph → L)
    (b : List (Rule L P (AffixAction Morph))) (hb : ∀ r ∈ b, r.payload.KindCoherent)
    (t : Word.Tree Morph) (ht : t.IsKindCoherent) (σ : P) :
    (evalBlockForm (fun t => LindexZ t.toList)
        (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ)).IsKindCoherent := by
  simp only [evalBlockForm, selectMinimal_map_payload]
  cases h : selectMinimal b (LindexZ t.toList, σ) with
  | none => exact ht
  | some r => exact r.payload.apply_isKindCoherent (hb r (selectMinimal_mem h)) ht

end

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]
variable (LindexZ : List M → L) (blocks : List (List (Rule L P (AffixAction M))))

theorem toList_blocksEval (t : Word.Tree M) (σ : P) :
    ((blocksEval (fun t => LindexZ t.toList)
        (blocks.map (List.map (Rule.mapPayload AffixAction.toTreeAction))) (t, σ)).1).toList
      = (blocksEval LindexZ
          (blocks.map (List.map (Rule.mapPayload AffixAction.toAction))) (t.toList, σ)).1 := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, blocksEval, List.foldl_cons]
    rw [show evalBlock (fun t : Word.Tree M => LindexZ t.toList)
          (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ)
        = (evalBlockForm (fun t : Word.Tree M => LindexZ t.toList)
            (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ), σ) from rfl]
    simp only [blocksEval] at ih
    rw [ih]
    rw [toList_evalBlockForm]
    rfl

/-- The tree-valued run linearizes to the sequence-valued run: the recorded
structure is what the engine did. -/
theorem toList_paradigmFunction_tree (stemLeaf : L × P → M) (c : L × P) :
    (paradigmFunction (fun t => LindexZ t.toList) (fun c => .root (stemLeaf c))
        (blocks.map (List.map (Rule.mapPayload AffixAction.toTreeAction))) c).1.toList
      = (paradigmFunction LindexZ (fun c => [stemLeaf c])
          (blocks.map (List.map (Rule.mapPayload AffixAction.toAction))) c).1 := by
  simp only [paradigmFunction]
  exact toList_blocksEval LindexZ blocks (.root (stemLeaf c)) c.2

variable {infl : M → Bool}

theorem stem_blocksEval (hbs : ∀ b ∈ blocks, ∀ r ∈ b, infl r.payload.material)
    (t : Word.Tree M) (σ : P) :
    ((blocksEval (fun t => LindexZ t.toList)
        (blocks.map (List.map (Rule.mapPayload AffixAction.toTreeAction))) (t, σ)).1).stem infl
      = t.stem infl := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, blocksEval, List.foldl_cons]
    rw [show evalBlock (fun t : Word.Tree M => LindexZ t.toList)
          (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ)
        = (evalBlockForm (fun t : Word.Tree M => LindexZ t.toList)
            (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ), σ) from rfl]
    simp only [blocksEval] at ih
    rw [ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb))]
    exact stem_evalBlockForm LindexZ b (hbs b (List.mem_cons_self ..)) t σ

/-- Under any classification counting the vocabulary's material as
inflectional, the tree-valued run's stem is the chosen leaf. -/
theorem stem_paradigmFunction_tree (stemLeaf : L × P → M)
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, infl r.payload.material) (c : L × P) :
    (paradigmFunction (fun t => LindexZ t.toList) (fun c => .root (stemLeaf c))
        (blocks.map (List.map (Rule.mapPayload AffixAction.toTreeAction))) c).1.stem infl
      = .root (stemLeaf c) := by
  simp only [paradigmFunction]
  exact stem_blocksEval LindexZ blocks hbs (.root (stemLeaf c)) c.2

end

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]
variable (LindexZ : List Morph → L) (blocks : List (List (Rule L P (AffixAction Morph))))

theorem isKindCoherent_blocksEval
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, r.payload.KindCoherent)
    (t : Word.Tree Morph) (ht : t.IsKindCoherent) (σ : P) :
    ((blocksEval (fun t => LindexZ t.toList)
        (blocks.map (List.map (Rule.mapPayload AffixAction.toTreeAction))) (t, σ)).1).IsKindCoherent := by
  induction blocks generalizing t with
  | nil => exact ht
  | cons b bs ih =>
    simp only [List.map_cons, blocksEval, List.foldl_cons]
    rw [show evalBlock (fun t : Word.Tree Morph => LindexZ t.toList)
          (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ)
        = (evalBlockForm (fun t : Word.Tree Morph => LindexZ t.toList)
            (b.map (Rule.mapPayload AffixAction.toTreeAction)) (t, σ), σ) from rfl]
    simp only [blocksEval] at ih
    exact ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) _
      (isKindCoherent_evalBlockForm LindexZ b (hbs b (List.mem_cons_self ..)) t ht σ)

/-- A kind-coherent vocabulary over a root-or-free stem leaf emits a
kind-coherent tree. -/
theorem isKindCoherent_paradigmFunction_tree (stemLeaf : L × P → Morph)
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, r.payload.KindCoherent)
    (hstem : ∀ c : L × P, (stemLeaf c).kind = .root ∨ (stemLeaf c).kind = .free) (c : L × P) :
    (paradigmFunction (fun t => LindexZ t.toList) (fun c => .root (stemLeaf c))
        (blocks.map (List.map (Rule.mapPayload AffixAction.toTreeAction))) c).1.IsKindCoherent := by
  simp only [paradigmFunction]
  exact isKindCoherent_blocksEval LindexZ blocks hbs (.root (stemLeaf c)) (hstem c) c.2

end

end Morphology.PFM
