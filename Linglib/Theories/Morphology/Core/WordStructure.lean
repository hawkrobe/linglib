import Linglib.Core.Lexical.MorphRule
import Linglib.Theories.Morphology.Core.Circumfix

/-!
# Morphological Word Structure
@cite{hayes-2009}

Hierarchical representation of word-internal structure via the `MorphWord`
inductive type: a tree of morphemes where affixation, compounding,
reduplication, and conversion are structural operations.

## Design

`MorphWord` and `MorphRule` are complementary:
- `MorphRule` represents inflectional *processes* (`String → String`)
- `MorphWord` represents derivational/compositional *structure* (tree of
  morphemes)

Morpheme boundaries fall out naturally from linearization — the boundary
positions are implicit between adjacent morphemes in the flattened list.

## Constructors

| Constructor    | Operation                     | Example                        |
|----------------|-------------------------------|--------------------------------|
| `root`         | leaf morpheme                 | *walk*                         |
| `prefixed`     | prefix attachment             | *un-* + *happy*                |
| `suffixed`     | suffix attachment             | *walk* + *-ed*                 |
| `infixed`      | infix insertion               | Tagalog *-um-* in *sulat*     |
| `circumfixed`  | circumfix wrapping            | German *ge-mach-t*            |
| `compound`     | compounding                   | *desk* + *lamp*               |
| `reduplicated` | total or partial reduplication| Warlpiri *kijikiji*           |
| `converted`    | zero affixation / conversion  | noun *telephone* → verb       |

-/

namespace Morphology.WordStructure

open Core.Morphology (MorphStatus AttachmentSide)
open Morphology.Circumfix (CircumfixExponence)

-- ============================================================================
-- §1: Morpheme
-- ============================================================================

/-- A morpheme: the minimal meaningful unit (Hayes §5.1).

Carries a surface form, an optional gloss, and its morphological status
(free word, clitic, or affix). -/
structure Morpheme where
  form   : String
  gloss  : String := ""
  status : MorphStatus := .freeWord
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Reduplication Type
-- ============================================================================

/-- Type of reduplication (Hayes §5.2).

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
-- §3: MorphWord — Hierarchical Word Structure
-- ============================================================================

/-- Hierarchical word structure as a tree of morphemes.

Each constructor corresponds to a morphological operation from
Hayes §5.2–5.5. The tree structure captures the derivational
history and word-internal constituency. -/
inductive MorphWord where
  /-- Leaf node: a single morpheme (free or bound). -/
  | root : Morpheme → MorphWord
  /-- Hayes §5.2: attach morpheme before base. -/
  | prefixed : Morpheme → MorphWord → MorphWord
  /-- Hayes §5.2: attach morpheme after base. -/
  | suffixed : MorphWord → Morpheme → MorphWord
  /-- Hayes §5.2: insert morpheme at position `pos` within base's
      surface form. Example: Tagalog *-um-* in *s⟨um⟩ulat*. -/
  | infixed : MorphWord → Morpheme → Nat → MorphWord
  /-- Hayes §5.2: wrap base with a prefix and suffix.
      Example: German *ge-mach-t*. -/
  | circumfixed : Morpheme → MorphWord → Morpheme → MorphWord
  /-- Hayes §5.4: two stems joined. Example: *desk* + *lamp*. -/
  | compound : MorphWord → MorphWord → MorphWord
  /-- Hayes §5.2: total or partial reduplication. -/
  | reduplicated : RedupType → MorphWord → MorphWord
  /-- Hayes §5.2: zero affixation / conversion.
      Example: noun *telephone* → verb *to telephone*. -/
  | converted : MorphWord → MorphWord
  deriving Repr

-- ============================================================================
-- §4: Surface Form
-- ============================================================================

/-- Extract the flat surface string from the morphological tree. -/
def MorphWord.surface : MorphWord → String
  | .root m => m.form
  | .prefixed afx base => afx.form ++ base.surface
  | .suffixed base afx => base.surface ++ afx.form
  | .infixed base afx pos =>
    let s := base.surface
    String.ofList (s.toList.take pos) ++ afx.form ++ String.ofList (s.toList.drop pos)
  | .circumfixed pre base suf => pre.form ++ base.surface ++ suf.form
  | .compound left right => left.surface ++ right.surface
  | .reduplicated rt base =>
    match rt with
    | .total => base.surface ++ base.surface
    | .partialCopy copied => copied ++ base.surface
  | .converted base => base.surface

-- ============================================================================
-- §5: Morpheme Linearization & Boundaries
-- ============================================================================

/-- Flatten the morphological tree into a list of morphemes in linear
(left-to-right surface) order. Morpheme boundaries are implicit:
they fall between adjacent elements. -/
def MorphWord.morphemes : MorphWord → List Morpheme
  | .root m => [m]
  | .prefixed afx base => afx :: base.morphemes
  | .suffixed base afx => base.morphemes ++ [afx]
  | .infixed base afx _ => base.morphemes ++ [afx]
  | .circumfixed pre base suf =>
    ⟨pre.form, pre.gloss, .inflAffix⟩ :: base.morphemes
      ++ [⟨suf.form, suf.gloss, .inflAffix⟩]
  | .compound left right => left.morphemes ++ right.morphemes
  | .reduplicated _ base => base.morphemes
  | .converted base => base.morphemes

/-- Number of morphemes in the word. -/
def MorphWord.morphemeCount (w : MorphWord) : Nat := w.morphemes.length

/-- Positions of morpheme boundaries in the surface string.
Each `Nat` is a character offset where one morpheme ends and
the next begins. Phonological rules can reference these
positions (Hayes Chs 6–8). -/
def MorphWord.boundaryPositions : MorphWord → List Nat
  | .root _ => []
  | .prefixed afx base =>
    let offset := afx.form.length
    offset :: base.boundaryPositions.map (· + offset)
  | .suffixed base afx =>
    let baseLen := base.surface.length
    base.boundaryPositions ++ [baseLen, baseLen + afx.form.length]
  | .infixed base afx pos =>
    let afxLen := afx.form.length
    let baseBounds := base.boundaryPositions
    let shifted := baseBounds.map (λ b => if b ≥ pos then b + afxLen else b)
    (shifted ++ [pos, pos + afxLen]).mergeSort (· ≤ ·) |>.eraseDups
  | .circumfixed pre base _suf =>
    let preLen := pre.form.length
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
def MorphWord.IsSimple : MorphWord → Prop
  | .root _ => True
  | _ => False

instance : DecidablePred MorphWord.IsSimple := fun w => by
  cases w <;> unfold MorphWord.IsSimple <;> infer_instance

/-- Is this word a compound? -/
def MorphWord.IsCompound : MorphWord → Prop
  | .compound _ _ => True
  | _ => False

instance : DecidablePred MorphWord.IsCompound := fun w => by
  cases w <;> unfold MorphWord.IsCompound <;> infer_instance

/-- Does this word involve reduplication? -/
def MorphWord.IsReduplicated : MorphWord → Prop
  | .reduplicated _ _ => True
  | _ => False

instance : DecidablePred MorphWord.IsReduplicated := fun w => by
  cases w <;> unfold MorphWord.IsReduplicated <;> infer_instance

/-- Is this word derived by conversion (zero affixation)? -/
def MorphWord.IsConverted : MorphWord → Prop
  | .converted _ => True
  | _ => False

instance : DecidablePred MorphWord.IsConverted := fun w => by
  cases w <;> unfold MorphWord.IsConverted <;> infer_instance

/-- Morphological depth: number of derivational steps from the root(s). -/
def MorphWord.depth : MorphWord → Nat
  | .root _ => 0
  | .prefixed _ base => 1 + base.depth
  | .suffixed base _ => 1 + base.depth
  | .infixed base _ _ => 1 + base.depth
  | .circumfixed _ base _ => 1 + base.depth
  | .compound l r => 1 + max l.depth r.depth
  | .reduplicated _ base => 1 + base.depth
  | .converted base => 1 + base.depth

-- ============================================================================
-- §7: Bridge to CircumfixExponence
-- ============================================================================

/-- Convert a circumfixed `MorphWord` to a `CircumfixExponence`.
Returns `none` for non-circumfixed words. -/
def MorphWord.toCircumfixExponence : MorphWord → Option CircumfixExponence
  | .circumfixed pre base suf =>
    some { prefix_ := pre.form, suffix_ := suf.form
         , stem := base.surface }
  | _ => none

-- ============================================================================
-- §8: Verification Theorems
-- ============================================================================

-- Surface form

/-- Conversion preserves the surface form. -/
theorem conversion_preserves_surface (w : MorphWord) :
    (MorphWord.converted w).surface = w.surface := by
  simp only [MorphWord.surface]

/-- The surface form of a compound is the concatenation of its parts. -/
theorem compound_surface (l r : MorphWord) :
    (MorphWord.compound l r).surface = l.surface ++ r.surface := by
  simp only [MorphWord.surface]

/-- Total reduplication doubles the surface form. -/
theorem total_redup_surface (w : MorphWord) :
    (MorphWord.reduplicated .total w).surface
      = w.surface ++ w.surface := by
  simp only [MorphWord.surface]

-- Structure

/-- A bare root has depth zero. -/
theorem root_depth_zero (m : Morpheme) :
    (MorphWord.root m).depth = 0 := by
  simp only [MorphWord.depth]

/-- A bare root contains exactly one morpheme. -/
theorem root_morphemeCount_one (m : Morpheme) :
    (MorphWord.root m).morphemeCount = 1 := by
  simp only [MorphWord.morphemeCount, MorphWord.morphemes, List.length]

-- Bridge

/-- The circumfix bridge extracts the correct prefix, suffix, and stem. -/
theorem circumfixed_bridge (pre suf : Morpheme) (base : MorphWord) :
    (MorphWord.circumfixed pre base suf).toCircumfixExponence
      = some { prefix_ := pre.form, suffix_ := suf.form
             , stem := base.surface } := by
  simp only [MorphWord.toCircumfixExponence]

end Morphology.WordStructure
