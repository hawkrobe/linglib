/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Morph

/-!
# Word-internal structure

A `Word.Structure` is a tree of morphemes whose constructors are the
morphological operations: affixation, compounding, reduplication, and
conversion ([hayes-2009]). Affixation carries an `AffixKind` tag, which
makes [booij-2012]'s relational notions computable as the accessors
`base`, `stem`, and `roots`. The partial fold `toExponent` projects
concatenative structure to a `Morph` sequence.

The token type (`Morphology.Word`, `Word/Basic.lean`) is deliberately
separate: the token is what syntax sees, the tree is how morphology
built it.
-/

namespace Morphology

/-! ### Morphemes -/

/-- A morpheme: the classical "minimal meaningful unit", kept as the
descriptive convenience the textbooks use. Carries its form as a `Morph`
and an optional gloss; attachment is `morph.kind`. Finer wordhood
classification (the clitic–affix cline) is diagnostic, derived in
`Studies/ZwickyPullum1983.lean`, not stored here. -/
structure Morpheme where
  morph  : Morph
  gloss  : String := ""
  deriving DecidableEq, Repr

/-- The surface string of a morpheme: its morph's segmental form. -/
def Morpheme.surface (m : Morpheme) : String := m.morph.form

/-! ### Reduplication and affix kinds -/

/-- The type of a reduplication step. -/
inductive RedupType where
  /-- Copies the entire base (Warlpiri *kijikiji* from *kiji*). -/
  | total
  /-- Copies a prosodic template; the copied material is stored explicitly
  since it depends on prosodic shape, determined at construction time
  (Ilokano *ag-tráb-trabáho*, partial copy *trab*). -/
  | partialCopy (copied : String)
  deriving DecidableEq, Repr

/-- Whether an affixation step is inflectional or derivational — the tag
that makes stems (inflection stripped) computable from the tree. -/
inductive AffixKind where
  | inflectional
  | derivational
  deriving DecidableEq, Repr

/-! ### The structure tree -/

/-- Hierarchical word structure as an operation-typed tree of morphemes:
each constructor is a word-formation operation with its own arity and
payload. The tree records derivational history and word-internal
constituency — what applying the operations as functions would forget. -/
inductive Word.Structure where
  /-- Leaf node: a single morpheme (free or bound). -/
  | root : Morpheme → Word.Structure
  /-- Attach morpheme before base. -/
  | prefixed : Morpheme → Word.Structure → optParam AffixKind .derivational → Word.Structure
  /-- Attach morpheme after base. -/
  | suffixed : Word.Structure → Morpheme → optParam AffixKind .derivational → Word.Structure
  /-- Insert morpheme at position `pos` within base's
      surface form. Example: Tagalog *-um-* in *s⟨um⟩ulat*. -/
  | infixed : Word.Structure → Morpheme → Nat → optParam AffixKind .derivational → Word.Structure
  /-- Wrap base with a prefix and suffix.
      Example: German *ge-mach-t*. -/
  | circumfixed : Morpheme → Word.Structure → Morpheme → optParam AffixKind .derivational → Word.Structure
  /-- Two stems joined. Example: *desk* + *lamp*. -/
  | compound : Word.Structure → Word.Structure → Word.Structure
  /-- Total or partial reduplication. -/
  | reduplicated : RedupType → Word.Structure → Word.Structure
  /-- Conversion. Example: noun *telephone* → verb *to telephone*. -/
  | converted : Word.Structure → Word.Structure
  deriving Repr

namespace Word.Structure

/-! ### Surface form -/

/-- The flat surface string of the morphological tree. -/
def surface : Word.Structure → String
  | .root m => m.surface
  | .prefixed afx base _ => afx.surface ++ base.surface
  | .suffixed base afx _ => base.surface ++ afx.surface
  | .infixed base afx pos _ =>
    let s := base.surface
    String.ofList (s.toList.take pos) ++ afx.surface ++ String.ofList (s.toList.drop pos)
  | .circumfixed pre base suf _ => pre.surface ++ base.surface ++ suf.surface
  | .compound left right => left.surface ++ right.surface
  | .reduplicated rt base =>
    match rt with
    | .total => base.surface ++ base.surface
    | .partialCopy copied => copied ++ base.surface
  | .converted base => base.surface

/-- Conversion preserves the surface form. -/
theorem surface_converted (w : Word.Structure) :
    (converted w).surface = w.surface := rfl

/-- The surface form of a compound is the concatenation of its parts. -/
theorem surface_compound (l r : Word.Structure) :
    (compound l r).surface = l.surface ++ r.surface := rfl

/-- Total reduplication doubles the surface form. -/
theorem surface_reduplicated_total (w : Word.Structure) :
    (reduplicated .total w).surface = w.surface ++ w.surface := rfl

/-! ### Morpheme linearization and boundaries -/

/-- Flatten the morphological tree into a list of morphemes. The order
is left-to-right surface order for concatenative structure; an infix is
appended after its base's morphemes (its *surface* position is `pos`,
not its list position), and reduplicative copies contribute no morpheme.
Morpheme boundaries are implicit: they fall between adjacent elements. -/
def morphemes : Word.Structure → List Morpheme
  | .root m => [m]
  | .prefixed afx base _ => afx :: base.morphemes
  | .suffixed base afx _ => base.morphemes ++ [afx]
  | .infixed base afx _ _ => base.morphemes ++ [afx]
  | .circumfixed pre base suf _ => pre :: base.morphemes ++ [suf]
  | .compound left right => left.morphemes ++ right.morphemes
  | .reduplicated _ base => base.morphemes
  | .converted base => base.morphemes

/-- The number of morphemes in the word. -/
def morphemeCount (w : Word.Structure) : Nat := w.morphemes.length

/-- A bare root contains exactly one morpheme. -/
theorem morphemeCount_root (m : Morpheme) : (root m).morphemeCount = 1 := rfl

/-- Positions of morpheme boundaries in the surface string. Each `Nat`
is a character offset where one morpheme ends and the next begins;
phonological rules can reference these positions. -/
def boundaryPositions : Word.Structure → List Nat
  | .root _ => []
  | .prefixed afx base _ =>
    let offset := afx.surface.length
    offset :: base.boundaryPositions.map (· + offset)
  | .suffixed base afx _ =>
    let baseLen := base.surface.length
    base.boundaryPositions ++ [baseLen, baseLen + afx.surface.length]
  | .infixed base afx pos _ =>
    let afxLen := afx.surface.length
    let baseBounds := base.boundaryPositions
    let shifted := baseBounds.map (λ b => if b ≥ pos then b + afxLen else b)
    (shifted ++ [pos, pos + afxLen]).mergeSort (· ≤ ·) |>.eraseDups
  | .circumfixed pre base _suf _ =>
    let preLen := pre.surface.length
    let baseLen := base.surface.length
    preLen :: (base.boundaryPositions.map (· + preLen)
      ++ [preLen + baseLen])
  | .compound left right =>
    let leftLen := left.surface.length
    left.boundaryPositions ++ [leftLen]
      ++ right.boundaryPositions.map (· + leftLen)
  | .reduplicated rt base =>
    match rt with
    | .total =>
      let baseLen := base.surface.length
      base.boundaryPositions ++ [baseLen]
        ++ base.boundaryPositions.map (· + baseLen)
    | .partialCopy copied =>
      let copiedLen := copied.length
      copiedLen :: base.boundaryPositions.map (· + copiedLen)
  | .converted base => base.boundaryPositions

/-! ### Structural predicates -/

/-- A word is simple if it is a bare root. -/
def IsSimple : Word.Structure → Prop
  | .root _ => True
  | _ => False

instance : DecidablePred IsSimple := fun w => by
  cases w <;> unfold IsSimple <;> infer_instance

/-- A word is a compound if its outermost operation joins two stems. -/
def IsCompound : Word.Structure → Prop
  | .compound _ _ => True
  | _ => False

instance : DecidablePred IsCompound := fun w => by
  cases w <;> unfold IsCompound <;> infer_instance

/-- A word is reduplicated if its outermost operation is reduplication. -/
def IsReduplicated : Word.Structure → Prop
  | .reduplicated _ _ => True
  | _ => False

instance : DecidablePred IsReduplicated := fun w => by
  cases w <;> unfold IsReduplicated <;> infer_instance

/-- A word is converted if its outermost operation is conversion. -/
def IsConverted : Word.Structure → Prop
  | .converted _ => True
  | _ => False

instance : DecidablePred IsConverted := fun w => by
  cases w <;> unfold IsConverted <;> infer_instance

/-- Morphological depth: the number of operations above the deepest root. -/
def depth : Word.Structure → Nat
  | .root _ => 0
  | .prefixed _ base _ => 1 + base.depth
  | .suffixed base _ _ => 1 + base.depth
  | .infixed base _ _ _ => 1 + base.depth
  | .circumfixed _ base _ _ => 1 + base.depth
  | .compound l r => 1 + max l.depth r.depth
  | .reduplicated _ base => 1 + base.depth
  | .converted base => 1 + base.depth

/-- A bare root has depth zero. -/
theorem depth_root (m : Morpheme) : (root m).depth = 0 := rfl

/-! ### Relational accessors

Root, stem, and base are *relational* notions over word structure, not
stored lexical fields: the base is what an operation applied to, the
stem is the word minus its inflection, roots are the unanalyzable
leaves. -/

/-- The immediate base of the outermost operation: the daughter tree for
affixation, reduplication, and conversion; `none` for a bare root and
for compounds (which have two constituents, not a base). -/
def base : Word.Structure → Option Word.Structure
  | .root _ => none
  | .prefixed _ b _ => some b
  | .suffixed b _ _ => some b
  | .infixed b _ _ _ => some b
  | .circumfixed _ b _ _ => some b
  | .compound _ _ => none
  | .reduplicated _ b => some b
  | .converted b => some b

/-- The stem: the tree with outer *inflectional* affixation stripped.
Derivational structure, compounding, reduplication, and conversion are
part of the stem. -/
def stem : Word.Structure → Word.Structure
  | .prefixed _ b .inflectional => b.stem
  | .suffixed b _ .inflectional => b.stem
  | .infixed b _ _ .inflectional => b.stem
  | .circumfixed _ b _ .inflectional => b.stem
  | w => w

/-- The root morphemes: the leaves of the tree. A simplex word has one;
a compound has one per constituent. -/
def roots : Word.Structure → List Morpheme
  | .root m => [m]
  | .prefixed _ b _ => b.roots
  | .suffixed b _ _ => b.roots
  | .infixed b _ _ _ => b.roots
  | .circumfixed _ b _ _ => b.roots
  | .compound l r => l.roots ++ r.roots
  | .reduplicated _ b => b.roots
  | .converted b => b.roots

/-- A word with no inflection is its own stem. -/
theorem stem_root (m : Morpheme) : (root m).stem = root m := rfl

/-- Stripping inflection strips through stacked inflectional suffixes. -/
theorem stem_suffixed_infl (b : Word.Structure) (afx : Morpheme) :
    (suffixed b afx .inflectional).stem = b.stem := rfl

/-- Derivational affixation is stem-internal. -/
theorem stem_suffixed_deriv (b : Word.Structure) (afx : Morpheme) :
    (suffixed b afx .derivational).stem = suffixed b afx .derivational := rfl

/-! ### The partial fold to morphs -/

/-- Project concatenative word structure to its `Morph` sequence.
**Partial**: `none` on infixation, circumfixation, and reduplication —
morphs are continuous and segmental, so discontinuous and process
morphology are constructions, not morph sequences. Conversion is
morph-vacuous and projects through. -/
def toExponent : Word.Structure → Option (List Morph)
  | .root m => some [m.morph]
  | .prefixed afx b _ => (b.toExponent).map (afx.morph :: ·)
  | .suffixed b afx _ => (b.toExponent).map (· ++ [afx.morph])
  | .compound l r => do pure ((← l.toExponent) ++ (← r.toExponent))
  | .converted b => b.toExponent
  | .infixed .. => none
  | .circumfixed .. => none
  | .reduplicated .. => none

/-- The fold is total exactly on the concatenative fragment: a
circumfixed word has no morph-sequence projection. -/
theorem toExponent_circumfixed (pre suf : Morpheme)
    (b : Word.Structure) (k : AffixKind) :
    (circumfixed pre b suf k).toExponent = none := rfl

end Word.Structure

end Morphology
