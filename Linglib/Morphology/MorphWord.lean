import Linglib.Morphology.Morph
import Linglib.Morphology.Formative

/-!
# Morphological Word Structure
[hayes-2009]

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

-- ============================================================================
-- Circumfixal Exponence
--   (inlined from former Morphology/Circumfix.lean, sole external
--    consumer is Fragments/Tigrinya/ClausePrefixes.lean)
-- ============================================================================

/-! Circumfixal exponence wraps a stem with morphological material on both
sides (prefix + suffix). Theory-neutral surface description; how a circumfix
*arises* (head movement in DM, readjustment elsewhere) is theory-specific.

Examples: German *ge-mach-t*, Tigrinya *ʔay-...-n*, Malay *ke-baik-an*. -/

namespace Morphology.Circumfix

open Morphology (AttachmentSide)

/-- Circumfixal exponence: a stem wrapped by a prefix and suffix. -/
structure CircumfixExponence where
  prefix_ : String
  suffix_ : String
  stem : String
  gloss : String := ""
  deriving Repr, DecidableEq

/-- Apply circumfixal exponence to produce the surface form. -/
def CircumfixExponence.realize (c : CircumfixExponence) : String :=
  c.prefix_ ++ c.stem ++ c.suffix_

/-- A circumfix as a two-morph construction. [haspelmath-2020] (p. 123)
treats a circumfix not as one discontinuous morph but as a construction
containing a prefix and a suffix; this realizes that reading as the
prefix/suffix `Morph`s of `Morphology/Morph.lean` (the stem is not part
of the exponent). -/
def CircumfixExponence.toExponent (c : CircumfixExponence) : Exponent :=
  [Morph.pref c.prefix_, Morph.suff c.suffix_]

/-- A circumfix is discontinuous: its exponents are separated by the stem. -/
def CircumfixExponence.isDiscontinuous (_c : CircumfixExponence) : Bool := true

/-- The attachment side of a circumfix is `AttachmentSide.circumfix`. -/
def CircumfixExponence.attachmentSide (_c : CircumfixExponence) : AttachmentSide :=
  .circumfix

theorem circumfix_attachment (c : CircumfixExponence) :
    c.attachmentSide = .circumfix := rfl

theorem circumfix_discontinuous (c : CircumfixExponence) :
    c.isDiscontinuous = true := rfl

theorem circumfix_realize_concat (c : CircumfixExponence) :
    c.realize = c.prefix_ ++ c.stem ++ c.suffix_ := rfl

/-- German past participle ge-...-t. -/
def germanPastParticiple (stem : String) : CircumfixExponence where
  prefix_ := "ge-"
  suffix_ := "-t"
  stem := stem
  gloss := "PTCP"

theorem german_pp_example :
    (germanPastParticiple "mach").realize = "ge-mach-t" := rfl

end Morphology.Circumfix

-- ============================================================================
-- Morphological Word Structure
-- ============================================================================

namespace Morphology.WordStructure

open Morphology (MorphStatus AttachmentSide)
open Morphology.Circumfix (CircumfixExponence)

-- ============================================================================
-- §1: Morpheme
-- ============================================================================

/-- A morpheme: the minimal meaningful unit (Hayes §5.1).

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
  | .root m => m.surface
  | .prefixed afx base => afx.surface ++ base.surface
  | .suffixed base afx => base.surface ++ afx.surface
  | .infixed base afx pos =>
    let s := base.surface
    String.ofList (s.toList.take pos) ++ afx.surface ++ String.ofList (s.toList.drop pos)
  | .circumfixed pre base suf => pre.surface ++ base.surface ++ suf.surface
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
    ⟨pre.morph, pre.gloss, .inflAffix⟩ :: base.morphemes
      ++ [⟨suf.morph, suf.gloss, .inflAffix⟩]
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
    let offset := afx.surface.length
    offset :: base.boundaryPositions.map (· + offset)
  | .suffixed base afx =>
    let baseLen := base.surface.length
    base.boundaryPositions ++ [baseLen, baseLen + afx.surface.length]
  | .infixed base afx pos =>
    let afxLen := afx.surface.length
    let baseBounds := base.boundaryPositions
    let shifted := baseBounds.map (λ b => if b ≥ pos then b + afxLen else b)
    (shifted ++ [pos, pos + afxLen]).mergeSort (· ≤ ·) |>.eraseDups
  | .circumfixed pre base _suf =>
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
    some { prefix_ := pre.surface, suffix_ := suf.surface
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
      = some { prefix_ := pre.surface, suffix_ := suf.surface
             , stem := base.surface } := by
  simp only [MorphWord.toCircumfixExponence]

end Morphology.WordStructure
