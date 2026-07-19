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

`Word/Tree` is the observation language (word-internal constituency, asserted
of a fragment's trees) and the PFM engine (`Paradigm/Function.lean`) the prediction
language (block cascades over material sequences, whose output is an unanalyzed
form). This file makes "the analysis is what the engine did" a theorem: an
affix-transparent PFM sublanguage whose block fold *emits* a `Word.Tree`,
with `toList_paradigmTree` proving that tree linearizes to the engine's form
— the same move `Linkage.realize_eq_paradigmFunction` made for PFM1↔PFM2.

The `Action.expo` payload is an opaque `P → Z → Z`, so a rule knows its output
but not its affix. `AffixAction` is the exponence-only refinement that carries the
affix (`pre`/`suf`), interpreted into `Action` by `toAction`. Every emitted node
is tagged `.inflectional`, so `stem_paradigmTree` reads inflection-hood off
engine provenance rather than stipulating it ([spencer-2013]): the whole output is
inflection above the chosen stem, and `Word.Tree.stem` ([booij-2012]) strips
back to `.root (stemLeaf c)`. When the vocabulary is kind-coherent,
`paradigmTree_isKindCoherent` derives that the emitted tree is `IsKindCoherent`
— the stipulate→derive companion of `stem_paradigmTree`.

Honest scope: referrals are excluded by type (no constructor); circumfix and
portmanteau actions, and the `String.join` corollary at a fragment site, wait for
their consumers.

## Main declarations

* `Rule.mapPayload`, `selectMinimal_map_payload` — relabel a rule's payload;
  narrowest-rule selection is payload-blind, so it commutes with the relabelling
* `Word.AffixAction`, `AffixAction.toAction`, `AffixAction.apply` — the
  affix-transparent sublanguage, its engine interpretation, and its tree action
* `Word.evalBlockTree`, `Word.paradigmTree` — the tree-emitting block step and
  block cascade
* `Word.toList_paradigmTree` — the emitted tree linearizes to the engine form
* `Word.stem_paradigmTree` — the emitted tree's stem is the chosen leaf
* `Word.AffixAction.KindCoherent`, `Word.paradigmTree_isKindCoherent` — the
  vocabulary-coherence hypothesis and the emitted tree's kind-coherence
-/

namespace Morphology.PFM

open Morphology Morphology.Exponence

variable {L P F F' : Type*}

/-- Relabel a rule's payload, keeping its class and property set. Applicability and
narrowness read only class and props, so selection is blind to the relabelling
(`selectMinimal_map_payload`). -/
def Rule.mapPayload (g : F → F') (r : Rule L P F) : Rule L P F' where
  klass := r.klass
  props := r.props
  payload := g r.payload

@[simp] theorem Rule.mapPayload_klass (g : F → F') (r : Rule L P F) :
    (r.mapPayload g).klass = r.klass := rfl

@[simp] theorem Rule.mapPayload_props (g : F → F') (r : Rule L P F) :
    (r.mapPayload g).props = r.props := rfl

section
variable [PartialOrder P]

@[simp] theorem Rule.mapPayload_lt_iff {g : F → F'} {r s : Rule L P F} :
    r.mapPayload g < s.mapPayload g ↔ r < s := Iff.rfl

end

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

/-- Payload relabelling commutes with narrowest-rule selection: `Applies` and `≤`
depend only on class and props (both preserved by `mapPayload`), so the same rule
wins on either side. -/
theorem selectMinimal_map_payload (g : F → F') (v : List (Rule L P F)) (c : L × P) :
    selectMinimal (v.map (Rule.mapPayload g)) c
      = (selectMinimal v c).map (Rule.mapPayload g) := by
  have hA : applicable (v.map (Rule.mapPayload g)) c
      = (applicable v c).map (Rule.mapPayload g) := by
    simp only [applicable, List.filter_map, Function.comp_def, Rule.applies_iff,
      Rule.mapPayload_klass, Rule.mapPayload_props]
    rfl
  rw [selectMinimal, selectMinimal, hA, List.find?_map]
  simp only [Function.comp_def, List.all_map, Rule.mapPayload_lt_iff]

end

end Morphology.PFM

namespace Morphology.Word

open Morphology.PFM Morphology.Exponence

variable {M L P : Type*}

/-! ### The affix-transparent sublanguage -/

/-- An **affix-transparent** action: a prefix or suffix carrying its own affix
payload. The exponence-only refinement of the engine's opaque `Action.expo`
(`toAction`) — a block of `Rule L P (AffixAction M)` cannot carry a referral, so
the sublanguage is exponence-only by type. -/
inductive AffixAction (M : Type*) where
  /-- Prepend the affix. -/
  | pre (m : M)
  /-- Append the affix. -/
  | suf (m : M)

/-- Interpret an affix action as an engine payload over material sequences
(`Z := List M`): prefixation prepends, suffixation appends. Both are
property-insensitive, so land in `Action.const` (hence `Action.expo`) — the
referral branch of `evalBlockForm` is dead for mapped rules. -/
def AffixAction.toAction : AffixAction M → Action (List M) P
  | .pre m => .const ([m] ++ ·)
  | .suf m => .const (· ++ [m])

/-- Apply an affix action to a term tree, tagging the node `.inflectional`
— inflection-hood by engine provenance ([spencer-2013]), not stipulation. -/
def AffixAction.apply : AffixAction M → Word.Tree M → Word.Tree M
  | .pre m, t => .prefixed m t .inflectional
  | .suf m, t => .suffixed t m .inflectional

theorem AffixAction.apply_stem (a : AffixAction M) (t : Word.Tree M) :
    (a.apply t).stem = t.stem := by cases a <;> rfl

/-! ### Vocabulary kind-coherence -/

/-- A vocabulary-level coherence hypothesis: a `pre` action carries a before-bound
morph, a `suf` action an after-bound one — the side its `Kind` records is the side
`apply` places it on. -/
def AffixAction.KindCoherent : AffixAction Morph → Prop
  | .pre m => m.side? = some .before
  | .suf m => m.side? = some .after

/-- Applying a kind-coherent affix action preserves kind-coherence: the emitted
node's affix sits on the side its `Kind` records. -/
theorem AffixAction.apply_isKindCoherent {a : AffixAction Morph} (ha : a.KindCoherent)
    {t : Word.Tree Morph} (ht : t.IsKindCoherent) : (a.apply t).IsKindCoherent := by
  cases a with
  | pre m => exact ⟨ha, ht⟩
  | suf m => exact ⟨ha, ht⟩

/-! ### The tree-emitting engine -/

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

/-- The tree produced by evaluating one block at a term state: apply the
narrowest applicable rule's affix action, leaving the tree unchanged when nothing
applies. The tree mirror of `evalBlockForm`. -/
def evalBlockTree (LindexZ : List M → L) (b : List (Rule L P (AffixAction M)))
    (tσ : Word.Tree M × P) : Word.Tree M :=
  match selectMinimal b (LindexZ tσ.1.toList, tσ.2) with
  | some r => r.payload.apply tσ.1
  | none => tσ.1

/-- Evaluate a block at a term state, keeping the property set — the mirror
of `evalBlock`. -/
def evalBlockTreeState (LindexZ : List M → L) (b : List (Rule L P (AffixAction M)))
    (tσ : Word.Tree M × P) : Word.Tree M × P :=
  (evalBlockTree LindexZ b tσ, tσ.2)

/-- The **tree-emitting paradigm function**: fold the block cascade over
term states from the stem leaf `.root (stemLeaf c)` — the mirror of
`paradigmFunction`. -/
def paradigmTree (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    Word.Tree M × P :=
  blocks.foldl (fun tσ b => evalBlockTreeState LindexZ b tσ) (.root (stemLeaf c), c.2)

/-! ### The agreement theorem -/

/-- One block step commutes: the emitted tree linearizes to the engine's form. -/
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

/-- **The engine output realizes the recorded structure**: the tree emitted by the
affix-transparent cascade linearizes to the form the PFM engine computes over the
relabelled blocks. The describe/explain division of labor as a theorem. -/
theorem toList_paradigmTree (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    (paradigmTree LindexZ stemLeaf blocks c).1.toList
      = (paradigmFunction LindexZ (fun c => [stemLeaf c])
          (blocks.map (List.map (Rule.mapPayload AffixAction.toAction))) c).1 := by
  rw [paradigmTree, paradigmFunction, blocksEval]
  exact toList_foldl_evalBlockTreeState LindexZ blocks (.root (stemLeaf c)) c.2

/-! ### Inflection-hood by construction -/

theorem stem_evalBlockTree (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (t : Word.Tree M) (σ : P) :
    (evalBlockTree LindexZ b (t, σ)).stem = t.stem := by
  simp only [evalBlockTree]
  cases selectMinimal b (LindexZ t.toList, σ) with
  | none => rfl
  | some r => exact AffixAction.apply_stem r.payload t

theorem stem_foldl_evalBlockTreeState (LindexZ : List M → L)
    (blocks : List (List (Rule L P (AffixAction M)))) (t : Word.Tree M) (σ : P) :
    (blocks.foldl (fun tσ b => evalBlockTreeState LindexZ b tσ) (t, σ)).1.stem = t.stem := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [show evalBlockTreeState LindexZ b (t, σ) = (evalBlockTree LindexZ b (t, σ), σ) from rfl, ih]
    exact stem_evalBlockTree LindexZ b t σ

/-- **Inflection-hood by construction** ([spencer-2013], [booij-2012]): every node
the cascade emits is `.inflectional`, so the emitted word's stem is exactly the
chosen leaf — the engine's whole output is inflection above the stem. -/
theorem stem_paradigmTree (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    (paradigmTree LindexZ stemLeaf blocks c).1.stem = .root (stemLeaf c) := by
  rw [paradigmTree]
  exact stem_foldl_evalBlockTreeState LindexZ blocks (.root (stemLeaf c)) c.2

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

/-- **Kind-coherence by construction**: when every vocabulary action places its
affix on the side its `Kind` records and the stem leaf is a root or free form,
the emitted tree is `IsKindCoherent`. The stipulate→derive companion of
`stem_paradigmTree`: coherence is read off engine provenance, not asserted. -/
theorem paradigmTree_isKindCoherent (LindexZ : List Morph → L) (stemLeaf : L × P → Morph)
    (blocks : List (List (Rule L P (AffixAction Morph)))) (c : L × P)
    (hbs : ∀ b ∈ blocks, ∀ r ∈ b, r.payload.KindCoherent)
    (hstem : (stemLeaf c).kind = .root ∨ (stemLeaf c).kind = .free) :
    (paradigmTree LindexZ stemLeaf blocks c).1.IsKindCoherent := by
  rw [paradigmTree]
  exact foldl_evalBlockTreeState_isKindCoherent LindexZ blocks (.root (stemLeaf c)) hstem c.2 hbs

end

end Morphology.Word
