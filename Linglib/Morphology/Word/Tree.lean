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
word; the tree records derivational history and word-internal constituency, which applying the operations as functions
would forget.

## Main declarations

* `Word.Tree` — the operation-typed tree
* `Word.Tree.toList`, `Word.Tree.toSequence?` — material linearization, and
  the concatenative fragment's material sequence
* `Word.Tree.base`, `Word.Tree.stem`, `Word.Tree.roots` — [booij-2012]'s
  relational notions
* `Word.Tree.IsKindCoherent` — attachment kinds match the positions
  carrying them
* `Word.Tree.map` — functorial relabelling of the material

## Implementation notes

`M` plays two roles: generator at the leaves (root and free morphs) and
label on the affixal operations. An affix is never a subtree, so its
boundness holds by construction; `toList` flattens both roles onto the
morph-sequence reading. The tree does not evaluate to surface strings:
concatenative surface forms are `String.join` over `toList`, and the
surface effect of the process constructors belongs to the process theories.
`IsKindCoherent` is a law, not a derivation — the tree is not built from
the attachment data. The theory layer instantiates `M := Morph`; fragments
with annotated morphs use richer leaf types. The token (`Morphology.Word`,
`Word/Basic.lean`) is separate: the token is what syntax sees, the tree is
how morphology built it.
-/

namespace Morphology.Word

/-! ### The operation indices -/

/-- The type of a reduplication step — an index on `Word.Tree`'s
reduplication operation, pending a copying-theory home. -/
inductive Tree.RedupType where
  /-- Copies the entire base (Javanese *omaha* → *omaha-omaha* "various
  houses", [booij-2012] from Uhlenbeck 1978). -/
  | total
  /-- Copies a prosodic template (Javanese *tamu* → *tətamu* "to visit",
  [booij-2012]); the copied material is determined by prosodic shape,
  which is process-theory content, not tree data. -/
  | partialCopy
  deriving DecidableEq, Repr

/-- Whether an affixation step is inflectional or derivational — the tag
that makes stems (inflection stripped) computable from the tree. -/
inductive Tree.AffixKind where
  | inflectional
  | derivational
  deriving DecidableEq, Repr

/-! ### The tree -/

/-- Hierarchical word structure as an operation-typed tree with material
in `M`: each constructor is a word-formation operation with its own
arity and material. The tree records derivational history and
word-internal constituency. -/
inductive Tree (M : Type*) where
  /-- Leaf node: a single element (free or bound). -/
  | root : M → Tree M
  /-- Attach an affix before the base. -/
  | prefixed : M → Tree M → optParam Tree.AffixKind .derivational → Tree M
  /-- Attach an affix after the base. -/
  | suffixed : Tree M → M → optParam Tree.AffixKind .derivational → Tree M
  /-- Insert an affix within the base (Khmu *s⟨m⟩ka:t* "roughen" from
      *ska:t* "rough", [booij-2012]); the insertion site is prosodically
      determined and is process-theory content, not tree data. -/
  | infixed : Tree M → M → optParam Tree.AffixKind .derivational → Tree M
  /-- Wrap the base with a prefix and a suffix.
      Example: German *Ge-sing-e* "singing" from *sing* ([booij-2012]). -/
  | circumfixed : M → Tree M → M → optParam Tree.AffixKind .derivational →
      Tree M
  /-- Two stems joined. Example: *bottle* + *factory* ([booij-2012]). -/
  | compound : Tree M → Tree M → Tree M
  /-- Total or partial reduplication. -/
  | reduplicated : Tree.RedupType → Tree M → Tree M
  /-- Conversion. Example: noun *chain* → verb *to chain* ([booij-2012]). -/
  | converted : Tree M → Tree M
  deriving Repr

namespace Tree

variable {M : Type*}

/-! ### Linearization -/

/-- All material of the tree in left-to-right surface order for
concatenative structure; an infix is appended after its base's material
(its surface position is prosodic, not positional), and reduplicative
copies contribute nothing. -/
def toList : Tree M → List M
  | .root m => [m]
  | .prefixed afx base _ => afx :: base.toList
  | .suffixed base afx _ => base.toList ++ [afx]
  | .infixed base afx _ => base.toList ++ [afx]
  | .circumfixed pre base suf _ => pre :: base.toList ++ [suf]
  | .compound left right => left.toList ++ right.toList
  | .reduplicated _ base => base.toList
  | .converted base => base.toList

/-- Relabel the material of the tree, keeping its shape. -/
def map {N : Type*} (f : M → N) : Tree M → Tree N
  | .root m => .root (f m)
  | .prefixed afx base k => .prefixed (f afx) (base.map f) k
  | .suffixed base afx k => .suffixed (base.map f) (f afx) k
  | .infixed base afx k => .infixed (base.map f) (f afx) k
  | .circumfixed pre base suf k => .circumfixed (f pre) (base.map f) (f suf) k
  | .compound left right => .compound (left.map f) (right.map f)
  | .reduplicated rt base => .reduplicated rt (base.map f)
  | .converted base => .converted (base.map f)

/-- The material sequence of the concatenative fragment. **Partial**:
`none` on infixation, circumfixation, and reduplication — discontinuous
and process morphology are constructions, not material sequences.
Conversion adds no material and projects through. -/
def toSequence? : Tree M → Option (List M)
  | .root m => some [m]
  | .prefixed afx b _ => (b.toSequence?).map (afx :: ·)
  | .suffixed b afx _ => (b.toSequence?).map (· ++ [afx])
  | .compound l r => do pure ((← l.toSequence?) ++ (← r.toSequence?))
  | .converted b => b.toSequence?
  | .infixed .. => none
  | .circumfixed .. => none
  | .reduplicated .. => none

/-- The projection is total exactly on the concatenative fragment: a
circumfixed word has no material-sequence projection. -/
theorem toSequence?_circumfixed (pre suf : M) (b : Tree M)
    (k : AffixKind) : (circumfixed pre b suf k).toSequence? = none := rfl

/-! ### Structural measures -/

/-- Morphological depth: the number of operations above the deepest root. -/
def depth : Tree M → Nat
  | .root _ => 0
  | .prefixed _ base _ => 1 + base.depth
  | .suffixed base _ _ => 1 + base.depth
  | .infixed base _ _ => 1 + base.depth
  | .circumfixed _ base _ _ => 1 + base.depth
  | .compound l r => 1 + max l.depth r.depth
  | .reduplicated _ base => 1 + base.depth
  | .converted base => 1 + base.depth

/-- A bare root has depth zero. -/
theorem depth_root (m : M) : (root m).depth = 0 := rfl

/-! ### Relational accessors

Root, stem, and base are *relational* notions over word structure, not
stored lexical fields: the base is what an operation applied to, the
stem is the word minus its inflection, roots are the unanalyzable
leaves. -/

/-- The immediate base of the outermost operation: the daughter tree for
affixation, reduplication, and conversion; `none` for a bare root and
for compounds (which have two constituents, not a base). -/
def base : Tree M → Option (Tree M)
  | .root _ => none
  | .prefixed _ b _ => some b
  | .suffixed b _ _ => some b
  | .infixed b _ _ => some b
  | .circumfixed _ b _ _ => some b
  | .compound _ _ => none
  | .reduplicated _ b => some b
  | .converted b => some b

/-- The stem: the tree with outer *inflectional* affixation stripped.
Derivational structure, compounding, reduplication, and conversion are
part of the stem. -/
def stem : Tree M → Tree M
  | .prefixed _ b .inflectional => b.stem
  | .suffixed b _ .inflectional => b.stem
  | .infixed b _ .inflectional => b.stem
  | .circumfixed _ b _ .inflectional => b.stem
  | w => w

/-- The root morphs: the leaves of the tree. A simplex word has one;
a compound has one per constituent. -/
def roots : Tree M → List M
  | .root m => [m]
  | .prefixed _ b _ => b.roots
  | .suffixed b _ _ => b.roots
  | .infixed b _ _ => b.roots
  | .circumfixed _ b _ _ => b.roots
  | .compound l r => l.roots ++ r.roots
  | .reduplicated _ b => b.roots
  | .converted b => b.roots

/-- A word with no inflection is its own stem. -/
theorem stem_root (m : M) : (root m).stem = root m := rfl

/-- Stripping inflection strips through stacked inflectional suffixes. -/
theorem stem_suffixed_infl (b : Tree M) (afx : M) :
    (suffixed b afx .inflectional).stem = b.stem := rfl

/-- Derivational affixation is stem-internal. -/
theorem stem_suffixed_deriv (b : Tree M) (afx : M) :
    (suffixed b afx .derivational).stem = suffixed b afx .derivational := rfl

/-! ### Kind coherence

A `Word.Tree Morph` carries `Morph` material whose `Kind`s could disagree
with the positions holding them (a `suffixed` node holding a prefix morph).
`IsKindCoherent` rules that out where `Kind` can speak. -/

/-- **Kind-coherence**: the material's `Kind`s agree with the positions carrying
them. A `prefixed` affix is bound on the `before` side, a `suffixed` affix
on the `after` side, a `circumfixed` node wraps a before-bound prefix and an
after-bound suffix, and every leaf is a root or a free form. Infixation,
reduplication, conversion, and compounding constrain no kind: `Kind` is
a segmental-only carrier — it cannot express infixal attachment, and
compounding joins stems. -/
def IsKindCoherent : Tree Morph → Prop
  | .root m => m.kind = .root ∨ m.kind = .free
  | .prefixed m b _ => m.side? = some .before ∧ b.IsKindCoherent
  | .suffixed b m _ => m.side? = some .after ∧ b.IsKindCoherent
  | .infixed b _ _ => b.IsKindCoherent
  | .circumfixed pre b suf _ =>
      pre.side? = some .before ∧ suf.side? = some .after ∧ b.IsKindCoherent
  | .compound l r => l.IsKindCoherent ∧ r.IsKindCoherent
  | .reduplicated _ b => b.IsKindCoherent
  | .converted b => b.IsKindCoherent

instance decIsKindCoherent : (t : Tree Morph) → Decidable t.IsKindCoherent
  | .root m => inferInstanceAs (Decidable (m.kind = .root ∨ m.kind = .free))
  | .prefixed m b _ =>
      have := decIsKindCoherent b
      inferInstanceAs (Decidable (m.side? = some .before ∧ IsKindCoherent b))
  | .suffixed b m _ =>
      have := decIsKindCoherent b
      inferInstanceAs (Decidable (m.side? = some .after ∧ IsKindCoherent b))
  | .infixed b _ _ => decIsKindCoherent b
  | .circumfixed pre b suf _ =>
      have := decIsKindCoherent b
      inferInstanceAs
        (Decidable (pre.side? = some .before ∧ suf.side? = some .after ∧ IsKindCoherent b))
  | .compound l r =>
      have := decIsKindCoherent l
      have := decIsKindCoherent r
      inferInstanceAs (Decidable (IsKindCoherent l ∧ IsKindCoherent r))
  | .reduplicated _ b => decIsKindCoherent b
  | .converted b => decIsKindCoherent b

end Tree

end Morphology.Word
