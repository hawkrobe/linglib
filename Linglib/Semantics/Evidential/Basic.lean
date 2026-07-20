import Linglib.Semantics.Evidential.Defs
import Linglib.Semantics.Evidential.Source

/-!
# Evidential — derived properties
[aikhenvald-2004]

Derived predicates and the Aikhenvald-cell mapping that lets typological
classifications be DERIVED from declared inventories rather than hardcoded
per-language. Mirrors the `Determiner.markingStrategy` pattern at
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

set_option autoImplicit false

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

/-! ### Coarse source and perspective -/

/-- Collapse an Aikhenvald cell to its [willett-1988] coarse source. -/
def Entry.Cell.toCoarseSource : Entry.Cell → CoarseSource
  | .firsthand | .visual | .nonvisualSensory | .auditory => .direct
  | .inferred | .assumed => .inference
  | .reported | .quotative => .hearsay

/-- The coarse source of an entry: the three `Entry` kinds are exactly the
    [willett-1988] tripartition. -/
def Entry.toCoarseSource : Entry → CoarseSource
  | .direct _      => .direct
  | .reportative _ => .hearsay
  | .inferential _ => .inference

/-- The taxonomy tower commutes: collapsing an entry's Aikhenvald cell
    gives its coarse source. -/
theorem Entry.cell_toCoarseSource (e : Entry) :
    e.cell.toCoarseSource = e.toCoarseSource := by
  cases e with
  | direct d => obtain ⟨_, _, s⟩ := d; cases s <;> rfl
  | reportative d => obtain ⟨_, _, s⟩ := d; cases s <;> rfl
  | inferential d => obtain ⟨_, _, s⟩ := d; cases s <;> rfl

/-- Inventory entries declare their coarse source; the evidential
    perspective derives via the canonical source mapping. -/
instance : HasCoarseSource Entry where
  toCoarseSource e := some e.toCoarseSource

/-- Every inventory entry is nonfuture: all three coarse sources are
    causally downstream of the described event (T ≤ A) under the
    canonical mapping. -/
theorem Entry.isNonfuture (e : Entry) : IsNonfuture e := by
  cases e with
  | direct _ => exact .inr rfl
  | reportative _ => exact .inl rfl
  | inferential _ => exact .inl rfl

end Semantics.Evidential
