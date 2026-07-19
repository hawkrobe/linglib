import Linglib.Morphology.Morph
import Linglib.Features.Formative

/-!
# Word-internal structure
[hayes-2009] [booij-2012]

Hierarchical representation of word-internal structure via the
`Word.Structure` inductive type: a tree of morphemes where affixation,
compounding, reduplication, and conversion are structural operations —
the item-and-arrangement tree-of-morphemes lineage ([anderson-2015]
pp. 28-29), with `reduplicated`/`converted` as process-constructor
exceptions. Affixation constructors carry an `AffixKind` tag
(inflectional vs derivational), which is what makes [booij-2012]'s
relational notions computable as accessors: `base` (the immediate
daughter), `stem` (the tree with outer inflectional affixation
stripped), and `roots` (the leaf morphemes). The partial fold
`toExponent` projects concatenative structure to a `Morph` sequence and
is undefined on infixation, circumfixation, and reduplication — the
partiality is [haspelmath-2020]'s thesis that discontinuous and
process morphology are constructions, not morphs.

The token type (`Morphology.Word`, `Word/Basic.lean`) and this tree are
deliberately separate: the token is what syntax sees, the tree is how
morphology built it.
-/



-- ============================================================================
-- Morphological Word Structure
-- ============================================================================

namespace Morphology

open Features (MorphStatus AttachmentSide)

-- ============================================================================
-- §1: Morpheme
-- ============================================================================

/-- A morpheme: the classical "minimal meaningful unit" ([hayes-2009];
[anderson-2015] problematizes the classical definition — this carrier
keeps it as the descriptive convenience both textbooks use).

Carries its form as a `Morph` (`Morphology/Morph.lean`), an optional
gloss, and its morphological `status`. `status` (`MorphStatus`) and
`morph.kind` (`Morph.Kind`) are two independent axes: `status` grades
syntactic wordhood (free word / clitic / affix), while `morph.kind`
records the attachment notation (prefix, suffix, clitic, root). -/
structure Morpheme where
  morph  : Morph
  gloss  : String := ""
  status : MorphStatus := .freeWord
  deriving DecidableEq, Repr

/-- The surface string of a morpheme: its morph's segmental form. -/
def Morpheme.surface (m : Morpheme) : String := m.morph.form

-- ============================================================================
-- §2: Reduplication Type
-- ============================================================================

/-- Type of reduplication ([hayes-2009]).

- `total`: copies the entire base (Warlpiri *kijikiji* from *kiji*)
- `partialCopy copied`: copies a prosodic template; the copied material is
  stored explicitly since it depends on prosodic shape (determined at
  construction time, not derivable from strings alone).
  Example: Ilokano *ag-tráb-trabáho* (partial copy *trab*). -/
inductive RedupType where
  | total
  | partialCopy (copied : String)
  deriving DecidableEq, Repr

-- ============================================================================
-- §3: Word.Structure — Hierarchical Word Structure
-- ============================================================================

/-- Whether an affixation step is inflectional or derivational — the
tag [booij-2012] requires on word-formation operations so that stems
(inflection stripped) are computable from the tree. -/
inductive AffixKind where
  | inflectional
  | derivational
  deriving DecidableEq, Repr

/-- Hierarchical word structure as a tree of morphemes.

Each constructor corresponds to a morphological operation from
[hayes-2009]'s survey — the item-and-arrangement tree-of-morphemes
lineage ([anderson-2015] pp. 28-29), with `reduplicated`/`converted` as
process-constructor exceptions. The tree structure captures the
derivational history and word-internal constituency. -/
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

-- ============================================================================
-- §4: Surface Form
-- ============================================================================

/-- Extract the flat surface string from the morphological tree. -/
def Word.Structure.surface : Word.Structure → String
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

-- ============================================================================
-- §5: Morpheme Linearization & Boundaries
-- ============================================================================

/-- Flatten the morphological tree into a list of morphemes. The order
is left-to-right surface order for concatenative structure; an infix is
appended after its base's morphemes (its *surface* position is `pos`,
not its list position), and reduplicative copies contribute no morpheme.
Morpheme boundaries are implicit: they fall between adjacent elements. -/
def Word.Structure.morphemes : Word.Structure → List Morpheme
  | .root m => [m]
  | .prefixed afx base _ => afx :: base.morphemes
  | .suffixed base afx _ => base.morphemes ++ [afx]
  | .infixed base afx _ _ => base.morphemes ++ [afx]
  | .circumfixed pre base suf _ => pre :: base.morphemes ++ [suf]
  | .compound left right => left.morphemes ++ right.morphemes
  | .reduplicated _ base => base.morphemes
  | .converted base => base.morphemes

/-- Number of morphemes in the word. -/
def Word.Structure.morphemeCount (w : Word.Structure) : Nat := w.morphemes.length

/-- Positions of morpheme boundaries in the surface string.
Each `Nat` is a character offset where one morpheme ends and
the next begins. Phonological rules can reference these
positions ([hayes-2009]). -/
def Word.Structure.boundaryPositions : Word.Structure → List Nat
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

-- ============================================================================
-- §6: Structural Predicates
-- ============================================================================

/-- Is this word a bare root (single morpheme)? -/
def Word.Structure.IsSimple : Word.Structure → Prop
  | .root _ => True
  | _ => False

instance : DecidablePred Word.Structure.IsSimple := fun w => by
  cases w <;> unfold Word.Structure.IsSimple <;> infer_instance

/-- Is this word a compound? -/
def Word.Structure.IsCompound : Word.Structure → Prop
  | .compound _ _ => True
  | _ => False

instance : DecidablePred Word.Structure.IsCompound := fun w => by
  cases w <;> unfold Word.Structure.IsCompound <;> infer_instance

/-- Does this word involve reduplication? -/
def Word.Structure.IsReduplicated : Word.Structure → Prop
  | .reduplicated _ _ => True
  | _ => False

instance : DecidablePred Word.Structure.IsReduplicated := fun w => by
  cases w <;> unfold Word.Structure.IsReduplicated <;> infer_instance

/-- Is this word derived by conversion? -/
def Word.Structure.IsConverted : Word.Structure → Prop
  | .converted _ => True
  | _ => False

instance : DecidablePred Word.Structure.IsConverted := fun w => by
  cases w <;> unfold Word.Structure.IsConverted <;> infer_instance

/-- Morphological depth: number of derivational steps from the root(s). -/
def Word.Structure.depth : Word.Structure → Nat
  | .root _ => 0
  | .prefixed _ base _ => 1 + base.depth
  | .suffixed base _ _ => 1 + base.depth
  | .infixed base _ _ _ => 1 + base.depth
  | .circumfixed _ base _ _ => 1 + base.depth
  | .compound l r => 1 + max l.depth r.depth
  | .reduplicated _ base => 1 + base.depth
  | .converted base => 1 + base.depth


-- ============================================================================
-- §7: Booij relational accessors
-- ============================================================================

/-! [booij-2012] treats root, stem, and base as *relational* notions over
word structure, not stored lexical fields: the base is what an operation
applied to, the stem is the word minus its inflection, roots are the
unanalyzable leaves. -/

/-- The immediate base of the outermost operation ([booij-2012]): the
daughter tree for affixation, reduplication, and conversion; `none` for
a bare root and for compounds (which have two constituents, not a base). -/
def Word.Structure.base : Word.Structure → Option Word.Structure
  | .root _ => none
  | .prefixed _ b _ => some b
  | .suffixed b _ _ => some b
  | .infixed b _ _ _ => some b
  | .circumfixed _ b _ _ => some b
  | .compound _ _ => none
  | .reduplicated _ b => some b
  | .converted b => some b

/-- The stem ([booij-2012]): the tree with outer *inflectional*
affixation stripped. Derivational structure, compounding, reduplication,
and conversion are part of the stem. -/
def Word.Structure.stem : Word.Structure → Word.Structure
  | .prefixed _ b .inflectional => b.stem
  | .suffixed b _ .inflectional => b.stem
  | .infixed b _ _ .inflectional => b.stem
  | .circumfixed _ b _ .inflectional => b.stem
  | w => w

/-- The root morphemes ([booij-2012]): the leaves of the tree. A simplex
word has one; a compound has one per constituent. -/
def Word.Structure.roots : Word.Structure → List Morpheme
  | .root m => [m]
  | .prefixed _ b _ => b.roots
  | .suffixed b _ _ => b.roots
  | .infixed b _ _ _ => b.roots
  | .circumfixed _ b _ _ => b.roots
  | .compound l r => l.roots ++ r.roots
  | .reduplicated _ b => b.roots
  | .converted b => b.roots

/-- A word with no inflection is its own stem. -/
theorem Word.Structure.stem_root (m : Morpheme) :
    (Word.Structure.root m).stem = .root m := rfl

/-- Stripping inflection strips through stacked inflectional suffixes. -/
theorem Word.Structure.stem_suffixed_infl (b : Word.Structure) (afx : Morpheme) :
    (Word.Structure.suffixed b afx .inflectional).stem = b.stem := rfl

/-- Derivational affixation is stem-internal. -/
theorem Word.Structure.stem_suffixed_deriv (b : Word.Structure) (afx : Morpheme) :
    (Word.Structure.suffixed b afx .derivational).stem
      = .suffixed b afx .derivational := rfl

-- ============================================================================
-- §8: The partial fold to exponents
-- ============================================================================

/-- Project concatenative word structure to its `Morph` sequence
(`Exponent`). **Partial**: `none` on infixation, circumfixation, and
reduplication — [haspelmath-2020]'s thesis that morphs are continuous
and segmental, so discontinuous and process morphology are
constructions, not morph sequences. Conversion is morph-vacuous and
projects through. -/
def Word.Structure.toExponent : Word.Structure → Option Exponent
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
theorem Word.Structure.toExponent_circumfixed (pre suf : Morpheme)
    (b : Word.Structure) (k : AffixKind) :
    (Word.Structure.circumfixed pre b suf k).toExponent = none := rfl

-- ============================================================================
-- §9: Verification Theorems
-- ============================================================================

-- Surface form

/-- Conversion preserves the surface form. -/
theorem conversion_preserves_surface (w : Word.Structure) :
    (Word.Structure.converted w).surface = w.surface := by
  simp only [Word.Structure.surface]

/-- The surface form of a compound is the concatenation of its parts. -/
theorem compound_surface (l r : Word.Structure) :
    (Word.Structure.compound l r).surface = l.surface ++ r.surface := by
  simp only [Word.Structure.surface]

/-- Total reduplication doubles the surface form. -/
theorem total_redup_surface (w : Word.Structure) :
    (Word.Structure.reduplicated .total w).surface
      = w.surface ++ w.surface := by
  simp only [Word.Structure.surface]

-- Structure

/-- A bare root has depth zero. -/
theorem root_depth_zero (m : Morpheme) :
    (Word.Structure.root m).depth = 0 := by
  simp only [Word.Structure.depth]

/-- A bare root contains exactly one morpheme. -/
theorem root_morphemeCount_one (m : Morpheme) :
    (Word.Structure.root m).morphemeCount = 1 := by
  simp only [Word.Structure.morphemeCount, Word.Structure.morphemes, List.length]

end Morphology
