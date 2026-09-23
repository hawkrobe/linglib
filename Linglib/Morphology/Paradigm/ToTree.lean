/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Tree
public import Linglib.Morphology.Paradigm.Function

/-!
# The paradigm function into word trees

The engine's state type `Z` is unconstrained ([bonami-stump-2016]'s PFM1,
`Paradigm/Function.lean`), so the paradigm function runs at
`Z := Word.Tree M` as readily as at material sequences. An affix-transparent
vocabulary interprets into both, and `toList` intertwines the two runs
(`toList_paradigmFunction_tree`); the emitted tree's stem is the chosen leaf
under any classification counting the vocabulary's material as inflectional
([spencer-2013]'s inflection-hood by provenance), and a kind-coherent
vocabulary emits a kind-coherent tree.

## Main declarations

* `attachTreeAction`, `attachAction` — a side and its affix, as an engine
  action at trees and at sequences
* `toList_paradigmFunction_tree`, `stem_paradigmFunction_tree`,
  `isKindCoherent_paradigmFunction_tree` — linearization, stem, and coherence
  of the tree-valued run
-/

@[expose] public section

namespace Morphology.PFM

open Morphology Morphology.Exponence Morphology.Word

variable {M L P : Type*}

/-! ### The affix-transparent vocabulary -/

/-- The engine interpretation of attaching an affix on a side, at tree-valued
state; rules over `Morph.Side × M` cannot carry referrals. -/
def attachTreeAction (p : Morph.Side × M) : Action (Word.Tree M) P :=
  .const fun t => t.attach p.1 p.2

/-- The engine interpretation of attaching an affix on a side, at material
sequences. -/
def attachAction (p : Morph.Side × M) : Action (List M) P := .const (p.1.attach p.2)

/-- The affix is bound on the side it is attached. -/
def KindCoherent (p : Morph.Side × Morph) : Prop := p.2.kind.side? = some p.1

/-! ### The tree-valued run -/

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

theorem toList_evalBlockForm (LindexZ : List M → L)
    (b : List (Rule L P (Morph.Side × M))) (t : Word.Tree M) (σ : P) :
    (evalBlockForm (fun t => LindexZ t.toList)
        (b.map (Rule.mapPayload attachTreeAction)) (t, σ)).toList
      = evalBlockForm LindexZ (b.map (Rule.mapPayload attachAction))
          (t.toList, σ) := by
  simp only [evalBlockForm, selectMinimal_map_payload]
  rcases selectMinimal b (LindexZ t.toList, σ) with _ | ⟨rk, rp, _ | _, m⟩ <;> rfl

theorem stem_evalBlockForm {infl : M → Bool} (LindexZ : List M → L)
    (b : List (Rule L P (Morph.Side × M))) (hb : ∀ r ∈ b, infl r.payload.2)
    (t : Word.Tree M) (σ : P) :
    (evalBlockForm (fun t => LindexZ t.toList)
        (b.map (Rule.mapPayload attachTreeAction)) (t, σ)).stem infl
      = t.stem infl := by
  simp only [evalBlockForm, selectMinimal_map_payload]
  cases h : selectMinimal b (LindexZ t.toList, σ) with
  | none => rfl
  | some r => exact Word.Tree.stem_attach r.payload.1 t (hb r (selectMinimal_mem h))

theorem isKindCoherent_evalBlockForm (LindexZ : List Morph → L)
    (b : List (Rule L P (Morph.Side × Morph))) (hb : ∀ r ∈ b, KindCoherent r.payload)
    (t : Word.Tree Morph) (ht : t.IsKindCoherent) (σ : P) :
    (evalBlockForm (fun t => LindexZ t.toList)
        (b.map (Rule.mapPayload attachTreeAction)) (t, σ)).IsKindCoherent := by
  simp only [evalBlockForm, selectMinimal_map_payload]
  cases h : selectMinimal b (LindexZ t.toList, σ) with
  | none => exact ht
  | some r => exact Word.Tree.isKindCoherent_attach (hb r (selectMinimal_mem h)) ht

end

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]
variable (LindexZ : List M → L) (blocks : List (List (Rule L P (Morph.Side × M))))

theorem toList_blocksEval (t : Word.Tree M) (σ : P) :
    ((blocksEval (fun t => LindexZ t.toList)
        (blocks.map (List.map (Rule.mapPayload attachTreeAction))) (t, σ)).1).toList
      = (blocksEval LindexZ
          (blocks.map (List.map (Rule.mapPayload attachAction))) (t.toList, σ)).1 := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, blocksEval, List.foldl_cons]
    rw [show evalBlock (fun t : Word.Tree M => LindexZ t.toList)
          (b.map (Rule.mapPayload attachTreeAction)) (t, σ)
        = (evalBlockForm (fun t : Word.Tree M => LindexZ t.toList)
            (b.map (Rule.mapPayload attachTreeAction)) (t, σ), σ) from rfl]
    simp only [blocksEval] at ih
    rw [ih]
    rw [toList_evalBlockForm]
    rfl

/-- The tree-valued run linearizes to the sequence-valued run: the recorded
structure is what the engine did. -/
theorem toList_paradigmFunction_tree (stemLeaf : L × P → M) (c : L × P) :
    (paradigmFunction (fun t => LindexZ t.toList) (fun c => .root (stemLeaf c))
        (blocks.map (List.map (Rule.mapPayload attachTreeAction))) c).1.toList
      = (paradigmFunction LindexZ (fun c => [stemLeaf c])
          (blocks.map (List.map (Rule.mapPayload attachAction))) c).1 := by
  simp only [paradigmFunction]
  exact toList_blocksEval LindexZ blocks (.root (stemLeaf c)) c.2

variable {infl : M → Bool}

theorem stem_blocksEval (hbs : ∀ b ∈ blocks, ∀ r ∈ b, infl r.payload.2)
    (t : Word.Tree M) (σ : P) :
    ((blocksEval (fun t => LindexZ t.toList)
        (blocks.map (List.map (Rule.mapPayload attachTreeAction))) (t, σ)).1).stem infl
      = t.stem infl := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, blocksEval, List.foldl_cons]
    rw [show evalBlock (fun t : Word.Tree M => LindexZ t.toList)
          (b.map (Rule.mapPayload attachTreeAction)) (t, σ)
        = (evalBlockForm (fun t : Word.Tree M => LindexZ t.toList)
            (b.map (Rule.mapPayload attachTreeAction)) (t, σ), σ) from rfl]
    simp only [blocksEval] at ih
    rw [ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb))]
    exact stem_evalBlockForm LindexZ b (hbs b (List.mem_cons_self ..)) t σ

/-- Under any classification counting the vocabulary's material as
inflectional, the tree-valued run's stem is the chosen leaf. -/
theorem stem_paradigmFunction_tree (stemLeaf : L × P → M)
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, infl r.payload.2) (c : L × P) :
    (paradigmFunction (fun t => LindexZ t.toList) (fun c => .root (stemLeaf c))
        (blocks.map (List.map (Rule.mapPayload attachTreeAction))) c).1.stem infl
      = .root (stemLeaf c) := by
  simp only [paradigmFunction]
  exact stem_blocksEval LindexZ blocks hbs (.root (stemLeaf c)) c.2

end

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]
variable (LindexZ : List Morph → L) (blocks : List (List (Rule L P (Morph.Side × Morph))))

theorem isKindCoherent_blocksEval
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, KindCoherent r.payload)
    (t : Word.Tree Morph) (ht : t.IsKindCoherent) (σ : P) :
    ((blocksEval (fun t => LindexZ t.toList)
        (blocks.map (List.map (Rule.mapPayload attachTreeAction))) (t, σ)).1).IsKindCoherent := by
  induction blocks generalizing t with
  | nil => exact ht
  | cons b bs ih =>
    simp only [List.map_cons, blocksEval, List.foldl_cons]
    rw [show evalBlock (fun t : Word.Tree Morph => LindexZ t.toList)
          (b.map (Rule.mapPayload attachTreeAction)) (t, σ)
        = (evalBlockForm (fun t : Word.Tree Morph => LindexZ t.toList)
            (b.map (Rule.mapPayload attachTreeAction)) (t, σ), σ) from rfl]
    simp only [blocksEval] at ih
    exact ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) _
      (isKindCoherent_evalBlockForm LindexZ b (hbs b (List.mem_cons_self ..)) t ht σ)

/-- A kind-coherent vocabulary over a root-or-free stem leaf emits a
kind-coherent tree. -/
theorem isKindCoherent_paradigmFunction_tree (stemLeaf : L × P → Morph)
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, KindCoherent r.payload)
    (hstem : ∀ c : L × P, (stemLeaf c).kind = .root ∨ (stemLeaf c).kind = .free) (c : L × P) :
    (paradigmFunction (fun t => LindexZ t.toList) (fun c => .root (stemLeaf c))
        (blocks.map (List.map (Rule.mapPayload attachTreeAction))) c).1.IsKindCoherent := by
  simp only [paradigmFunction]
  exact isKindCoherent_blocksEval LindexZ blocks hbs (.root (stemLeaf c)) (hstem c) c.2

end

end Morphology.PFM
