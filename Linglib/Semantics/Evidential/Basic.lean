import Linglib.Semantics.Evidential.Defs
import Linglib.Semantics.Evidential.Source

/-!
# Evidential — derived properties
[aikhenvald-2004]

Derived predicates and the Aikhenvald-cell mapping that lets typological
classifications be DERIVED from declared inventories rather than hardcoded
per-language. Mirrors the `Determiner.Inventory.markingStrategy` pattern at
`Semantics/Definiteness/Determiner.lean`: typological classifications are theorems
about the declared inventory, not stipulations.

## Main declarations

* `Entry.Cell` — the cells of [aikhenvald-2004] Ch 2's paradigm
  space, distinct evidence-source categories a paradigm can carve out.
* `Entry.cell : Entry → Cell` — projection from a typed entry to its
  Aikhenvald cell. Direct entries map via `DirectSource` (visual,
  auditory, etc.), inferential entries via `InferentialBasis`
  (from-result, from-assumption), reportative entries via
  `ReportativeSource` (unidentified, identified).
-/

namespace Semantics.Evidential

/-- A cell in [aikhenvald-2004] Ch 2's paradigm space. Each `Entry`
    covers one cell; `AikhenvaldSystem.fromInventory` then classifies a
    paradigm by inspecting which cells are filled. -/
inductive Entry.Cell where
  /-- Generic firsthand, no sensory channel specified (A1's catch-all). -/
  | firsthand
  /-- Specifically visual evidence. -/
  | visual
  /-- Non-visual sensory (touch, smell, taste, generic non-visual). -/
  | nonvisualSensory
  /-- Specifically auditory (A5; Kashaya's distinctive split). -/
  | auditory
  /-- Inference from an observable result. -/
  | inferred
  /-- Inference from general knowledge or reasoning. -/
  | assumed
  /-- Hearsay from an unidentified source. -/
  | reported
  /-- Hearsay from a specifically identified source. -/
  | quotative
  /-- Everything but firsthand evidence under one term: inference, assumption and hearsay
  (the marked term of A1 and A2 systems). -/
  | nonfirsthand
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Project a typed `Entry` to its Aikhenvald paradigm cell. -/
def Entry.cell : Entry → Entry.Cell
  | .direct      ⟨_, _, .unspecified⟩      => .firsthand
  | .direct      ⟨_, _, .visual⟩           => .visual
  | .direct      ⟨_, _, .auditory⟩         => .auditory
  | .direct      ⟨_, _, .nonvisualSensory⟩ => .nonvisualSensory
  | .inferential ⟨_, _, .unspecified⟩      => .inferred
  | .inferential ⟨_, _, .fromResult⟩       => .inferred
  | .inferential ⟨_, _, .fromAssumption⟩   => .assumed
  | .reportative ⟨_, _, .unspecified⟩      => .reported
  | .reportative ⟨_, _, .unidentified⟩     => .reported
  | .reportative ⟨_, _, .identified⟩       => .quotative
  | .nonfirsthand _                        => .nonfirsthand

/-! ### Coarse source and perspective -/

/-- Collapse an Aikhenvald cell to its [willett-1988] coarse source; a
    non-firsthand term spans inference and hearsay and has none. -/
def Entry.Cell.toCoarseSource : Entry.Cell → Option CoarseSource
  | .firsthand | .visual | .nonvisualSensory | .auditory => some .direct
  | .inferred | .assumed => some .inference
  | .reported | .quotative => some .hearsay
  | .nonfirsthand => none

/-- The coarse source of an entry: the three coarse `Entry` kinds are exactly
    the [willett-1988] tripartition; a non-firsthand term has none. -/
def Entry.toCoarseSource : Entry → Option CoarseSource
  | .direct _       => some .direct
  | .reportative _  => some .hearsay
  | .inferential _  => some .inference
  | .nonfirsthand _ => none

/-- The taxonomy tower commutes: collapsing an entry's Aikhenvald cell
    gives its coarse source. -/
theorem Entry.cell_toCoarseSource (e : Entry) :
    e.cell.toCoarseSource = e.toCoarseSource := by
  cases e with
  | direct d => obtain ⟨_, _, s⟩ := d; cases s <;> rfl
  | reportative d => obtain ⟨_, _, s⟩ := d; cases s <;> rfl
  | inferential d => obtain ⟨_, _, s⟩ := d; cases s <;> rfl
  | nonfirsthand _ => rfl

/-- Inventory entries declare their coarse source. -/
instance : HasCoarseSource Entry where
  toCoarseSource := Entry.toCoarseSource

/-- The perspective of an entry: through the canonical source mapping, with a
    non-firsthand term retrospective like the inference and hearsay it spans. -/
instance : HasEvidentialPerspective Entry where
  toEvidentialPerspective
    | .nonfirsthand _ => some .retrospective
    | e => e.toCoarseSource.bind CoarseSource.toEvidentialPerspective

/-- Every inventory entry is nonfuture: every source is causally downstream
    of the described event (T ≤ A) under the canonical mapping. -/
theorem Entry.isNonfuture (e : Entry) : IsNonfuture e := by
  cases e with
  | direct _ => exact .inr rfl
  | reportative _ => exact .inl rfl
  | inferential _ => exact .inl rfl
  | nonfirsthand _ => exact .inl rfl

end Semantics.Evidential
