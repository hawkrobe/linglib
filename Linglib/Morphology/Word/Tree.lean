/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Morph

/-!
# Word-internal structure

A `Word.Tree M` is an operation-typed tree over the word-formation
signature: each constructor is one of [booij-2012]'s morphological
operations, with its own arity and material. Every subtree is a partial
word; the tree records derivational history and word-internal
constituency, which applying the operations as functions would forget.

## Main declarations

* `Word.Tree` — the operation-typed tree
* `Word.Tree.toList`, `Word.Tree.IsConcatenative` — linearization, and the
  shapes where it is the word's segmentation
* `Word.Tree.base`, `Word.Tree.stem`, `Word.Tree.roots` — [booij-2012]'s
  relational notions
* `Word.Tree.IsKindCoherent` — attachment kinds match their positions
-/

namespace Morphology.Word

/-! ### The reduplication index -/

/-- The type of a reduplication step. -/
inductive Tree.RedupType where
  /-- Copies the entire base (Javanese *omaha* → *omaha-omaha* "various
  houses"). -/
  | total
  /-- Copies a prosodic template (Javanese *tamu* → *tətamu* "to visit"). -/
  | partialCopy
  deriving DecidableEq, Repr

/-! ### The tree -/

/-- A tree of word-formation operations over material in `M`. -/
inductive Tree (M : Type*) where
  /-- A leaf, carrying a single element. -/
  | root : M → Tree M
  /-- Attach an affix before the base. -/
  | prefixed : M → Tree M → Tree M
  /-- Attach an affix after the base. -/
  | suffixed : Tree M → M → Tree M
  /-- Insert an affix within the base (Khmu *s⟨m⟩ka:t* "roughen"). -/
  | infixed : Tree M → M → Tree M
  /-- Wrap the base with a prefix and a suffix (German *Ge-sing-e* "singing"). -/
  | circumfixed : M → Tree M → M → Tree M
  /-- Join two stems (*bottle* + *factory*). -/
  | compound : Tree M → Tree M → Tree M
  /-- Total or partial reduplication. -/
  | reduplicated : Tree.RedupType → Tree M → Tree M
  /-- Convert without added material (noun *chain* → verb *to chain*). -/
  | converted : Tree M → Tree M
  deriving Repr

namespace Tree

variable {M N O : Type*} {t : Tree M} {l : List M}

/-! ### Linearization -/

/-- The material of the tree, in surface order on the concatenative
fragment; an infix follows its base and reduplicative copies contribute
nothing. -/
def toList : Tree M → List M
  | .root m => [m]
  | .prefixed afx base => afx :: base.toList
  | .suffixed base afx => base.toList ++ [afx]
  | .infixed base afx => base.toList ++ [afx]
  | .circumfixed pre base suf => pre :: base.toList ++ [suf]
  | .compound left right => left.toList ++ right.toList
  | .reduplicated _ base => base.toList
  | .converted base => base.toList

theorem toList_ne_nil (t : Tree M) : t.toList ≠ [] := by
  induction t <;> simp_all [toList]

def map (f : M → N) : Tree M → Tree N
  | .root m => .root (f m)
  | .prefixed afx base => .prefixed (f afx) (base.map f)
  | .suffixed base afx => .suffixed (base.map f) (f afx)
  | .infixed base afx => .infixed (base.map f) (f afx)
  | .circumfixed pre base suf => .circumfixed (f pre) (base.map f) (f suf)
  | .compound left right => .compound (left.map f) (right.map f)
  | .reduplicated rt base => .reduplicated rt (base.map f)
  | .converted base => .converted (base.map f)

/-- The word is built by concatenation alone. -/
def IsConcatenative : Tree M → Prop
  | .root _ => True
  | .prefixed _ b => b.IsConcatenative
  | .suffixed b _ => b.IsConcatenative
  | .compound l r => l.IsConcatenative ∧ r.IsConcatenative
  | .converted b => b.IsConcatenative
  | .infixed .. => False
  | .circumfixed .. => False
  | .reduplicated .. => False

instance decIsConcatenative : (t : Tree M) → Decidable t.IsConcatenative
  | .root _ => .isTrue trivial
  | .prefixed _ b | .suffixed b _ | .converted b => decIsConcatenative b
  | .compound l r => @instDecidableAnd _ _ (decIsConcatenative l) (decIsConcatenative r)
  | .infixed .. | .circumfixed .. | .reduplicated .. => .isFalse id

/-! ### Laws -/

@[simp] theorem map_id (t : Tree M) : t.map id = t := by
  induction t <;> simp [map, *]

theorem map_map (f : M → N) (g : N → O) (t : Tree M) :
    (t.map f).map g = t.map (g ∘ f) := by
  induction t <;> simp [map, *]

/-- Linearization is natural in the material. -/
theorem toList_map (f : M → N) (t : Tree M) :
    (t.map f).toList = t.toList.map f := by
  induction t <;> simp [map, toList, *]

/-! ### Structural measures -/

/-- The number of operations above the deepest root. -/
def depth : Tree M → Nat
  | .root _ => 0
  | .compound l r => max l.depth r.depth + 1
  | .prefixed _ b | .suffixed b _ | .infixed b _ | .circumfixed _ b _
  | .reduplicated _ b | .converted b => b.depth + 1

/-- A bare root has depth zero. -/
theorem depth_root (m : M) : (root m).depth = 0 := rfl

/-! ### Relational accessors -/

/-- The daughter the outermost operation applied to; `none` for a bare
root and for compounds. -/
def base : Tree M → Option (Tree M)
  | .root _ | .compound _ _ => none
  | .prefixed _ b | .suffixed b _ | .infixed b _ | .circumfixed _ b _
  | .reduplicated _ b | .converted b => some b

/-- The tree with outer affixation by `infl`-material stripped. -/
def stem (infl : M → Bool) : Tree M → Tree M
  | w@(.prefixed a b) => if infl a then b.stem infl else w
  | w@(.suffixed b a) => if infl a then b.stem infl else w
  | w@(.infixed b a) => if infl a then b.stem infl else w
  | w@(.circumfixed pre b suf) => if infl pre && infl suf then b.stem infl else w
  | w => w

/-- The material at the leaves. -/
def roots : Tree M → List M
  | .root m => [m]
  | .compound l r => l.roots ++ r.roots
  | .prefixed _ b | .suffixed b _ | .infixed b _ | .circumfixed _ b _
  | .reduplicated _ b | .converted b => b.roots

variable {infl : M → Bool}

theorem stem_root (m : M) : (root m).stem infl = root m := rfl

theorem stem_suffixed_of_infl {afx : M} (b : Tree M) (h : infl afx) :
    (suffixed b afx).stem infl = b.stem infl := by simp [stem, h]

theorem stem_suffixed_of_not_infl {afx : M} (b : Tree M) (h : ¬ infl afx) :
    (suffixed b afx).stem infl = suffixed b afx := by simp [stem, h]

/-! ### Kind coherence -/

/-- The material's `Kind`s agree with their positions — no `suffixed` node
holds a prefix morph — and every leaf is a root or a free form. -/
def IsKindCoherent : Tree Morph → Prop
  | .root m => m.kind = .root ∨ m.kind = .free
  | .prefixed m b => m.side? = some .before ∧ b.IsKindCoherent
  | .suffixed b m => m.side? = some .after ∧ b.IsKindCoherent
  | .circumfixed pre b suf =>
      pre.side? = some .before ∧ suf.side? = some .after ∧ b.IsKindCoherent
  | .compound l r => l.IsKindCoherent ∧ r.IsKindCoherent
  | .infixed b _ | .reduplicated _ b | .converted b => b.IsKindCoherent

instance decIsKindCoherent : (t : Tree Morph) → Decidable t.IsKindCoherent
  | .root m => inferInstanceAs (Decidable (_ ∨ _))
  | .prefixed m b => @instDecidableAnd _ _ inferInstance (decIsKindCoherent b)
  | .suffixed b m => @instDecidableAnd _ _ inferInstance (decIsKindCoherent b)
  | .circumfixed pre b suf =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ inferInstance (decIsKindCoherent b))
  | .compound l r => @instDecidableAnd _ _ (decIsKindCoherent l) (decIsKindCoherent r)
  | .infixed b _ | .reduplicated _ b | .converted b => decIsKindCoherent b

end Tree

end Morphology.Word
