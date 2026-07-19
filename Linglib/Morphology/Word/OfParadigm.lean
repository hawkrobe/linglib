/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Word.Tree
import Linglib.Morphology.Paradigm.Function

/-!
# The paradigm function realizes word structure
[bonami-stump-2016] [spencer-2013] [booij-2012]

An affix-transparent PFM sublanguage whose block fold emits a `Word.Tree`:
`toList_paradigmTree` proves the emitted tree linearizes to the engine's form,
`stem_paradigmTree` that its stem is the chosen leaf, and
`paradigmTree_isKindCoherent` that a kind-coherent vocabulary emits a
kind-coherent tree.

## Main declarations

* `Word.AffixAction`, `AffixAction.toAction`, `AffixAction.apply` — the
  sublanguage, its engine interpretation, and its tree action
* `Word.evalBlockTree`, `Word.paradigmTree` — the tree-emitting block step and
  block cascade
* `Word.toList_paradigmTree`, `Word.stem_paradigmTree`,
  `Word.paradigmTree_isKindCoherent` — linearization, stem, and coherence of
  the emitted tree

## Implementation notes

The engine's `Action.expo` is an opaque `P → Z → Z` — a rule knows its output,
not its affix; `AffixAction` carries the affix and interprets into `Action` by
`toAction`. Inflection-hood is engine provenance rather than stipulation
([spencer-2013]): any classification counting the vocabulary's material as
inflectional strips the output back to the stem leaf. Referrals are excluded
by type; circumfix and portmanteau actions, and the `String.join` corollary at
a fragment site, wait for their consumers.
-/

namespace Morphology.Word

open Morphology.PFM Morphology.Exponence

variable {M L P : Type*}

/-! ### The affix-transparent sublanguage -/

/-- A prefix or suffix action carrying its affix; rules over `AffixAction`
cannot carry referrals. -/
inductive AffixAction (M : Type*) where
  /-- Prepend the affix. -/
  | pre (m : M)
  /-- Append the affix. -/
  | suf (m : M)

/-- The engine interpretation over material sequences: prepend or append. -/
def AffixAction.toAction : AffixAction M → Action (List M) P
  | .pre m => .const ([m] ++ ·)
  | .suf m => .const (· ++ [m])

/-- The affix an action attaches. -/
def AffixAction.material : AffixAction M → M
  | .pre m => m
  | .suf m => m

/-- Apply an affix action to a tree. -/
def AffixAction.apply : AffixAction M → Word.Tree M → Word.Tree M
  | .pre m, t => .prefixed m t
  | .suf m, t => .suffixed t m

theorem AffixAction.apply_stem {infl : M → Bool} (a : AffixAction M)
    (t : Word.Tree M) (h : infl a.material) :
    (a.apply t).stem infl = t.stem infl := by
  cases a <;> simp [apply, material] at h ⊢ <;> simp [Word.Tree.stem, h]

/-! ### Vocabulary kind-coherence -/

/-- The affix is bound on the side `apply` places it. -/
def AffixAction.KindCoherent : AffixAction Morph → Prop
  | .pre m => m.side? = some .before
  | .suf m => m.side? = some .after

theorem AffixAction.apply_isKindCoherent {a : AffixAction Morph} (ha : a.KindCoherent)
    {t : Word.Tree Morph} (ht : t.IsKindCoherent) : (a.apply t).IsKindCoherent := by
  cases a <;> exact ⟨ha, ht⟩

/-! ### The tree-emitting engine -/

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

/-- The narrowest applicable rule's affix action applied to the tree; the tree
mirror of `evalBlockForm`. -/
def evalBlockTree (LindexZ : List M → L) (b : List (Rule L P (AffixAction M)))
    (tσ : Word.Tree M × P) : Word.Tree M :=
  match selectMinimal b (LindexZ tσ.1.toList, tσ.2) with
  | some r => r.payload.apply tσ.1
  | none => tσ.1

/-- Evaluate a block at a tree state, keeping the property set; the mirror of
`evalBlock`. -/
def evalBlockTreeState (LindexZ : List M → L) (b : List (Rule L P (AffixAction M)))
    (tσ : Word.Tree M × P) : Word.Tree M × P :=
  (evalBlockTree LindexZ b tσ, tσ.2)

/-- The block cascade folded over tree states from the stem leaf; the mirror
of `paradigmFunction`. -/
def paradigmTree (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    Word.Tree M × P :=
  blocks.foldl (fun tσ b => evalBlockTreeState LindexZ b tσ) (.root (stemLeaf c), c.2)

/-! ### The agreement theorem -/

theorem toList_evalBlockTree (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (t : Word.Tree M) (σ : P) :
    (evalBlockTree LindexZ b (t, σ)).toList
      = evalBlockForm LindexZ (b.map (Rule.mapPayload AffixAction.toAction)) (t.toList, σ) := by
  simp only [evalBlockTree, evalBlockForm, selectMinimal_map_payload]
  rcases selectMinimal b (LindexZ t.toList, σ) with _ | ⟨rk, rp, rpl⟩
  · rfl
  · cases rpl <;> rfl

theorem toList_foldl_evalBlockTreeState (LindexZ : List M → L)
    (blocks : List (List (Rule L P (AffixAction M)))) (t : Word.Tree M) (σ : P) :
    (blocks.foldl (fun tσ b => evalBlockTreeState LindexZ b tσ) (t, σ)).1.toList
      = ((blocks.map (List.map (Rule.mapPayload AffixAction.toAction))).foldl
          (fun wσ b => evalBlock LindexZ b wσ) (t.toList, σ)).1 := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hstep : ((evalBlockTree LindexZ b (t, σ)).toList, σ)
        = evalBlock LindexZ (b.map (Rule.mapPayload AffixAction.toAction)) (t.toList, σ) :=
      Prod.ext (toList_evalBlockTree LindexZ b t σ) rfl
    rw [show evalBlockTreeState LindexZ b (t, σ) = (evalBlockTree LindexZ b (t, σ), σ) from rfl,
      ih, hstep]

/-- The emitted tree linearizes to the form the engine computes over the
relabelled blocks. -/
theorem toList_paradigmTree (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    (paradigmTree LindexZ stemLeaf blocks c).1.toList
      = (paradigmFunction LindexZ (fun c => [stemLeaf c])
          (blocks.map (List.map (Rule.mapPayload AffixAction.toAction))) c).1 := by
  rw [paradigmTree, paradigmFunction, blocksEval]
  exact toList_foldl_evalBlockTreeState LindexZ blocks (.root (stemLeaf c)) c.2

/-! ### Inflection-hood by construction -/

variable {infl : M → Bool}

theorem stem_evalBlockTree (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (hb : ∀ r ∈ b, infl r.payload.material)
    (t : Word.Tree M) (σ : P) :
    (evalBlockTree LindexZ b (t, σ)).stem infl = t.stem infl := by
  simp only [evalBlockTree]
  cases h : selectMinimal b (LindexZ t.toList, σ) with
  | none => rfl
  | some r => exact AffixAction.apply_stem r.payload t (hb r (selectMinimal_mem h))

theorem stem_foldl_evalBlockTreeState (LindexZ : List M → L)
    (blocks : List (List (Rule L P (AffixAction M))))
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, infl r.payload.material) (t : Word.Tree M) (σ : P) :
    (blocks.foldl (fun tσ b => evalBlockTreeState LindexZ b tσ) (t, σ)).1.stem infl
      = t.stem infl := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [show evalBlockTreeState LindexZ b (t, σ) = (evalBlockTree LindexZ b (t, σ), σ) from rfl,
      ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb))]
    exact stem_evalBlockTree LindexZ b (hbs b (List.mem_cons_self ..)) t σ

/-- Under any classification counting the vocabulary's material as
inflectional, the emitted tree's stem is the chosen leaf. -/
theorem stem_paradigmTree (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M))))
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, infl r.payload.material) (c : L × P) :
    (paradigmTree LindexZ stemLeaf blocks c).1.stem infl = .root (stemLeaf c) := by
  rw [paradigmTree]
  exact stem_foldl_evalBlockTreeState LindexZ blocks hbs (.root (stemLeaf c)) c.2

/-! ### Kind-coherence by construction -/

theorem evalBlockTree_isKindCoherent (LindexZ : List Morph → L)
    (b : List (Rule L P (AffixAction Morph))) (hb : ∀ r ∈ b, r.payload.KindCoherent)
    (t : Word.Tree Morph) (ht : t.IsKindCoherent) (σ : P) :
    (evalBlockTree LindexZ b (t, σ)).IsKindCoherent := by
  simp only [evalBlockTree]
  cases h : selectMinimal b (LindexZ t.toList, σ) with
  | none => exact ht
  | some r => exact r.payload.apply_isKindCoherent (hb r (selectMinimal_mem h)) ht

theorem foldl_evalBlockTreeState_isKindCoherent (LindexZ : List Morph → L) :
    ∀ (blocks : List (List (Rule L P (AffixAction Morph)))) (t : Word.Tree Morph),
      t.IsKindCoherent → ∀ (σ : P),
      (∀ b ∈ blocks, ∀ r ∈ b, r.payload.KindCoherent) →
      (blocks.foldl (fun tσ b => evalBlockTreeState LindexZ b tσ) (t, σ)).1.IsKindCoherent
  | [], _, ht, _, _ => ht
  | b :: bs, t, ht, σ, hbs => by
    simp only [List.foldl_cons]
    rw [show evalBlockTreeState LindexZ b (t, σ) = (evalBlockTree LindexZ b (t, σ), σ) from rfl]
    exact foldl_evalBlockTreeState_isKindCoherent LindexZ bs (evalBlockTree LindexZ b (t, σ))
      (evalBlockTree_isKindCoherent LindexZ b (fun r hr => hbs b (by simp) r hr) t ht σ)
      σ (fun b' hb' => hbs b' (by simp [hb']))

/-- A kind-coherent vocabulary over a root-or-free stem leaf emits a
kind-coherent tree. -/
theorem paradigmTree_isKindCoherent (LindexZ : List Morph → L) (stemLeaf : L × P → Morph)
    (blocks : List (List (Rule L P (AffixAction Morph)))) (c : L × P)
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, r.payload.KindCoherent)
    (hstem : (stemLeaf c).kind = .root ∨ (stemLeaf c).kind = .free) :
    (paradigmTree LindexZ stemLeaf blocks c).1.IsKindCoherent := by
  rw [paradigmTree]
  exact foldl_evalBlockTreeState_isKindCoherent LindexZ blocks (.root (stemLeaf c)) hstem c.2 hbs

end

end Morphology.Word
