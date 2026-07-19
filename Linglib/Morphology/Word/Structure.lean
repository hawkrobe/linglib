/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Morph

/-!
# Word-internal structure

A `Word.Structure M` is an operation-typed tree with leaves and affixal
payloads in `M`: each constructor is a word-formation operation with its
own arity and payload ([hayes-2009]). The tree records derivational
history and word-internal constituency — what applying the operations as
functions would forget. [booij-2012]'s relational notions are the
accessors `base`, `stem`, and `roots`; `toList` linearizes the payloads
and `toSequence?` projects the concatenative fragment to its payload
sequence. The tree does not evaluate to surface strings: concatenative
surface forms are `String.join` over `toList`, and the surface effect of
process constructors (infixation, reduplication) belongs to the process
theories, not to string simulation here.

The theory layer instantiates `M := Morph`; fragments that annotate
their morphs (glosses) instantiate `M` with their own richer leaf type.
The token type (`Morphology.Word`, `Word/Basic.lean`) is deliberately
separate: the token is what syntax sees, the tree is how morphology
built it.
-/

namespace Morphology

/-! ### Reduplication and affix kinds -/

/-- The type of a reduplication step. -/
inductive RedupType where
  /-- Copies the entire base (Warlpiri *kijikiji* from *kiji*). -/
  | total
  /-- Copies a prosodic template (Ilokano *ag-tráb-trabáho*); the copied
  material is determined by prosodic shape, which is process-theory
  content, not tree data. -/
  | partialCopy
  deriving DecidableEq, Repr

/-- Whether an affixation step is inflectional or derivational — the tag
that makes stems (inflection stripped) computable from the tree. -/
inductive AffixKind where
  | inflectional
  | derivational
  deriving DecidableEq, Repr

/-! ### The structure tree -/

/-- Hierarchical word structure as an operation-typed tree with payloads
in `M`: each constructor is a word-formation operation with its own
arity and payload. The tree records derivational history and
word-internal constituency. -/
inductive Word.Structure (M : Type*) where
  /-- Leaf node: a single element (free or bound). -/
  | root : M → Word.Structure M
  /-- Attach a payload before the base. -/
  | prefixed : M → Word.Structure M → optParam AffixKind .derivational → Word.Structure M
  /-- Attach a payload after the base. -/
  | suffixed : Word.Structure M → M → optParam AffixKind .derivational → Word.Structure M
  /-- Insert a payload within the base (Tagalog *-um-* in *s⟨um⟩ulat*);
      the insertion site is prosodically determined and is process-theory
      content, not tree data. -/
  | infixed : Word.Structure M → M → optParam AffixKind .derivational → Word.Structure M
  /-- Wrap the base with a prefix and a suffix.
      Example: German *ge-mach-t*. -/
  | circumfixed : M → Word.Structure M → M → optParam AffixKind .derivational → Word.Structure M
  /-- Two stems joined. Example: *desk* + *lamp*. -/
  | compound : Word.Structure M → Word.Structure M → Word.Structure M
  /-- Total or partial reduplication. -/
  | reduplicated : RedupType → Word.Structure M → Word.Structure M
  /-- Conversion. Example: noun *telephone* → verb *to telephone*. -/
  | converted : Word.Structure M → Word.Structure M
  deriving Repr

namespace Word.Structure

variable {M : Type*}

/-! ### Payload linearization -/

/-- All payloads of the tree in left-to-right surface order for
concatenative structure; an infix is appended after its base's payloads
(its surface position is prosodic, not positional), and reduplicative
copies contribute nothing. -/
def toList : Word.Structure M → List M
  | .root m => [m]
  | .prefixed afx base _ => afx :: base.toList
  | .suffixed base afx _ => base.toList ++ [afx]
  | .infixed base afx _ => base.toList ++ [afx]
  | .circumfixed pre base suf _ => pre :: base.toList ++ [suf]
  | .compound left right => left.toList ++ right.toList
  | .reduplicated _ base => base.toList
  | .converted base => base.toList

/-- The payload sequence of the concatenative fragment. **Partial**:
`none` on infixation, circumfixation, and reduplication — discontinuous
and process morphology are constructions, not payload sequences.
Conversion is payload-vacuous and projects through. -/
def toSequence? : Word.Structure M → Option (List M)
  | .root m => some [m]
  | .prefixed afx b _ => (b.toSequence?).map (afx :: ·)
  | .suffixed b afx _ => (b.toSequence?).map (· ++ [afx])
  | .compound l r => do pure ((← l.toSequence?) ++ (← r.toSequence?))
  | .converted b => b.toSequence?
  | .infixed .. => none
  | .circumfixed .. => none
  | .reduplicated .. => none

/-- The projection is total exactly on the concatenative fragment: a
circumfixed word has no payload-sequence projection. -/
theorem toSequence?_circumfixed (pre suf : M) (b : Word.Structure M)
    (k : AffixKind) : (circumfixed pre b suf k).toSequence? = none := rfl

/-! ### Structural measures -/

/-- Morphological depth: the number of operations above the deepest root. -/
def depth : Word.Structure M → Nat
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
def base : Word.Structure M → Option (Word.Structure M)
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
def stem : Word.Structure M → Word.Structure M
  | .prefixed _ b .inflectional => b.stem
  | .suffixed b _ .inflectional => b.stem
  | .infixed b _ .inflectional => b.stem
  | .circumfixed _ b _ .inflectional => b.stem
  | w => w

/-- The root payloads: the leaves of the tree. A simplex word has one;
a compound has one per constituent. -/
def roots : Word.Structure M → List M
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
theorem stem_suffixed_infl (b : Word.Structure M) (afx : M) :
    (suffixed b afx .inflectional).stem = b.stem := rfl

/-- Derivational affixation is stem-internal. -/
theorem stem_suffixed_deriv (b : Word.Structure M) (afx : M) :
    (suffixed b afx .derivational).stem = suffixed b afx .derivational := rfl

end Word.Structure

end Morphology
