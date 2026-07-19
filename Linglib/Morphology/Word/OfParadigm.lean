/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Word.Structure
import Linglib.Morphology.Paradigm.Function

/-!
# The paradigm function realizes word structure
[bonami-stump-2016] [spencer-2013] [booij-2012]

`Word/Structure` is the observation language (word-internal constituency, asserted
of a fragment's trees) and the PFM engine (`Paradigm/Function.lean`) the prediction
language (block cascades over payload sequences, whose output is an unanalyzed
form). This file makes "the analysis is what the engine did" a theorem: an
affix-transparent PFM sublanguage whose block fold *emits* a `Word.Structure`,
with `toList_paradigmStructure` proving that tree linearizes to the engine's form
— the same move `Linkage.realize_eq_paradigmFunction` made for PFM1↔PFM2.

The `Action.expo` payload is an opaque `P → Z → Z`, so a rule knows its output
but not its affix. `AffixAction` is the exponence-only refinement that carries the
affix (`pre`/`suf`), interpreted into `Action` by `toAction`. Every emitted node
is tagged `.inflectional`, so `stem_paradigmStructure` reads inflection-hood off
engine provenance rather than stipulating it ([spencer-2013]): the whole output is
inflection above the chosen stem, and `Word.Structure.stem` ([booij-2012]) strips
back to `.root (stemLeaf c)`.

Honest scope: referrals are excluded by type (no constructor); circumfix and
portmanteau actions, and the `String.join` corollary at a fragment site, wait for
their consumers.

## Main declarations

* `Rule.mapPayload`, `selectMinimal_map_payload` — relabel a rule's payload;
  narrowest-rule selection is payload-blind, so it commutes with the relabelling
* `Word.AffixAction`, `AffixAction.toAction`, `AffixAction.apply` — the
  affix-transparent sublanguage, its engine interpretation, and its tree action
* `Word.evalBlockStructure`, `Word.paradigmStructure` — the structure-emitting
  block step and block cascade
* `Word.toList_paradigmStructure` — the emitted tree linearizes to the engine form
* `Word.stem_paradigmStructure` — the emitted tree's stem is the chosen leaf
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
  /-- Prepend the payload. -/
  | pre (m : M)
  /-- Append the payload. -/
  | suf (m : M)

/-- Interpret an affix action as an engine payload over payload sequences
(`Z := List M`): prefixation prepends, suffixation appends. Both are
property-insensitive, so land in `Action.const` (hence `Action.expo`) — the
referral branch of `evalBlockForm` is dead for mapped rules. -/
def AffixAction.toAction : AffixAction M → Action (List M) P
  | .pre m => .const ([m] ++ ·)
  | .suf m => .const (· ++ [m])

/-- Apply an affix action to a structure tree, tagging the node `.inflectional`
— inflection-hood by engine provenance ([spencer-2013]), not stipulation. -/
def AffixAction.apply : AffixAction M → Word.Structure M → Word.Structure M
  | .pre m, t => .prefixed m t .inflectional
  | .suf m, t => .suffixed t m .inflectional

theorem AffixAction.apply_stem (a : AffixAction M) (t : Word.Structure M) :
    (a.apply t).stem = t.stem := by cases a <;> rfl

/-! ### The structure-emitting engine -/

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

/-- The tree produced by evaluating one block at a structure state: apply the
narrowest applicable rule's affix action, leaving the tree unchanged when nothing
applies. The structure mirror of `evalBlockForm`. -/
def evalBlockTree (LindexZ : List M → L) (b : List (Rule L P (AffixAction M)))
    (tσ : Word.Structure M × P) : Word.Structure M :=
  match selectMinimal b (LindexZ tσ.1.toList, tσ.2) with
  | some r => r.payload.apply tσ.1
  | none => tσ.1

/-- Evaluate a block at a structure state, keeping the property set — the mirror
of `evalBlock`. -/
def evalBlockStructure (LindexZ : List M → L) (b : List (Rule L P (AffixAction M)))
    (tσ : Word.Structure M × P) : Word.Structure M × P :=
  (evalBlockTree LindexZ b tσ, tσ.2)

/-- The **structure-emitting paradigm function**: fold the block cascade over
structure states from the stem leaf `.root (stemLeaf c)` — the mirror of
`paradigmFunction`. -/
def paradigmStructure (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    Word.Structure M × P :=
  blocks.foldl (fun tσ b => evalBlockStructure LindexZ b tσ) (.root (stemLeaf c), c.2)

/-! ### The agreement theorem -/

/-- One block step commutes: the emitted tree linearizes to the engine's form. -/
theorem toList_evalBlockTree (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (t : Word.Structure M) (σ : P) :
    (evalBlockTree LindexZ b (t, σ)).toList
      = evalBlockForm LindexZ (b.map (Rule.mapPayload AffixAction.toAction)) (t.toList, σ) := by
  simp only [evalBlockTree, evalBlockForm, selectMinimal_map_payload]
  rcases selectMinimal b (LindexZ t.toList, σ) with _ | ⟨rk, rp, rpl⟩
  · rfl
  · cases rpl <;> rfl

theorem toList_foldl_evalBlockStructure (LindexZ : List M → L)
    (blocks : List (List (Rule L P (AffixAction M)))) (t : Word.Structure M) (σ : P) :
    (blocks.foldl (fun tσ b => evalBlockStructure LindexZ b tσ) (t, σ)).1.toList
      = ((blocks.map (List.map (Rule.mapPayload AffixAction.toAction))).foldl
          (fun wσ b => evalBlock LindexZ b wσ) (t.toList, σ)).1 := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hstep : ((evalBlockTree LindexZ b (t, σ)).toList, σ)
        = evalBlock LindexZ (b.map (Rule.mapPayload AffixAction.toAction)) (t.toList, σ) :=
      Prod.ext (toList_evalBlockTree LindexZ b t σ) rfl
    rw [show evalBlockStructure LindexZ b (t, σ) = (evalBlockTree LindexZ b (t, σ), σ) from rfl,
      ih, hstep]

/-- **The engine output realizes the recorded structure**: the tree emitted by the
affix-transparent cascade linearizes to the form the PFM engine computes over the
relabelled blocks. The describe/explain division of labor as a theorem. -/
theorem toList_paradigmStructure (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    (paradigmStructure LindexZ stemLeaf blocks c).1.toList
      = (paradigmFunction LindexZ (fun c => [stemLeaf c])
          (blocks.map (List.map (Rule.mapPayload AffixAction.toAction))) c).1 := by
  rw [paradigmStructure, paradigmFunction, blocksEval]
  exact toList_foldl_evalBlockStructure LindexZ blocks (.root (stemLeaf c)) c.2

/-! ### Inflection-hood by construction -/

theorem stem_evalBlockTree (LindexZ : List M → L)
    (b : List (Rule L P (AffixAction M))) (t : Word.Structure M) (σ : P) :
    (evalBlockTree LindexZ b (t, σ)).stem = t.stem := by
  simp only [evalBlockTree]
  cases selectMinimal b (LindexZ t.toList, σ) with
  | none => rfl
  | some r => exact AffixAction.apply_stem r.payload t

theorem stem_foldl_evalBlockStructure (LindexZ : List M → L)
    (blocks : List (List (Rule L P (AffixAction M)))) (t : Word.Structure M) (σ : P) :
    (blocks.foldl (fun tσ b => evalBlockStructure LindexZ b tσ) (t, σ)).1.stem = t.stem := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [show evalBlockStructure LindexZ b (t, σ) = (evalBlockTree LindexZ b (t, σ), σ) from rfl, ih]
    exact stem_evalBlockTree LindexZ b t σ

/-- **Inflection-hood by construction** ([spencer-2013], [booij-2012]): every node
the cascade emits is `.inflectional`, so the emitted word's stem is exactly the
chosen leaf — the engine's whole output is inflection above the stem. -/
theorem stem_paradigmStructure (LindexZ : List M → L) (stemLeaf : L × P → M)
    (blocks : List (List (Rule L P (AffixAction M)))) (c : L × P) :
    (paradigmStructure LindexZ stemLeaf blocks c).1.stem = .root (stemLeaf c) := by
  rw [paradigmStructure]
  exact stem_foldl_evalBlockStructure LindexZ blocks (.root (stemLeaf c)) c.2

end

end Morphology.Word
