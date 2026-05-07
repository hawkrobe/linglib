import Mathlib.Order.Basic
import Linglib.Tactics.OntSort

/-!
# Core/Scales/Defs.lean — basic types
@cite{kennedy-mcnally-2005} @cite{kennedy-2007} @cite{rotstein-winter-2004} @cite{rouillard-2026}

Foundational scale-classification types used across all gradability/degree
substrate. No framework-specific operators here (those live in
`Theories/Semantics/Gradability/`).

Contents:
- `Boundedness` enum + `hasMax`/`hasMin`/`isLicensed`
- `MereoTag` + `toBoundedness`
- `LicensingPipeline` typeclass + universal theorem
- `ScalePolarity` enum

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).
-/

namespace Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Scale Boundedness
-- ════════════════════════════════════════════════════

/-- Classification of scale boundedness.
    @cite{kennedy-mcnally-2005} eq (1) and @cite{kennedy-2007} §4.2 eq (59):
    four scale types based on which endpoints exist (independently
    discovered by @cite{rotstein-winter-2004}).
    @cite{rouillard-2026}: temporal domains have similar boundary structure
    (closed intervals have both bounds, open intervals lack them).

    This enum is the **lexical data tag** for classifying scales in fragment
    entries and phenomena files — a role mathlib's typeclass instances cannot
    play (you cannot store an `[OrderTop α]` instance in a record field).
    The actual order-theoretic properties of concrete scale types are
    encoded via Mathlib typeclasses (`OrderTop`, `OrderBot`, `NoMaxOrder`,
    `NoMinOrder`); the two encodings serve different roles and both are real.

    **Standard-type dimension.** @cite{kennedy-2007} §4.3 eq (66) (Interpretive
    Economy) DERIVES standard type (relative / min-absolute / max-absolute)
    from scale structure for `open_`, `lowerBounded`, and `upperBounded`. For
    `closed`, all three interpretations are licensed (see eq 67: *opaque*,
    *transparent*) — this enum doesn't capture that disambiguation. Fragment
    entries with `boundedness = .closed` may need a separate `standardType`
    slot if downstream theorems care about the distinction.

    **Open-bounded sub-distinction.** @cite{kennedy-2007} fn 28: open scales
    can be further distinguished by whether they approach a value (e.g. 0 for
    cost) but don't include it, vs. completely unbounded. Not captured here. -/
inductive Boundedness where
  | open_        -- no inherent bounds (Kennedy: tall; Rouillard: atelic VP)
  | lowerBounded -- minimum exists, no maximum (Kennedy: wet; Rouillard: N/A)
  | upperBounded -- maximum exists, no minimum (Kennedy: dry; Rouillard: N/A)
  | closed       -- both bounds exist (Kennedy: full; Rouillard: telic VP)
  deriving DecidableEq, Repr

/-- Does this scale have an inherent maximum? -/
def Boundedness.hasMax : Boundedness → Bool
  | .upperBounded | .closed => true
  | .open_ | .lowerBounded => false

/-- Does this scale have an inherent minimum? -/
def Boundedness.hasMin : Boundedness → Bool
  | .lowerBounded | .closed => true
  | .open_ | .upperBounded => false

/-- "Any endpoint exists" predicate: returns `true` whenever the scale
    has at least one bound (max or min). An open scale returns `false`.

    **NOT @cite{kennedy-2007}'s full licensing prediction.** Kennedy's actual
    prediction is the 4×2 modifier-class matrix in @cite{kennedy-2007}
    eq (61) (= @cite{kennedy-mcnally-2005} eq (15)): maximizers
    (*completely, perfectly*) require an UPPER endpoint; minimizers
    (*slightly, partially*) require a LOWER endpoint; proportional modifiers
    (*half*) require BOTH. A single Bool can't encode this — to be faithful,
    split into `licensesMaximizer`/`licensesMinimizer`/`licensesProportional`.

    The current Bool is sufficient for callers that only need to distinguish
    "open" from "any-endpoint-exists" (e.g. Interpretive Economy gating a
    relative vs. absolute interpretation, @cite{kennedy-2007} §4.3, or
    Rouillard's MIP, @cite{rouillard-2026}). For modifier-specific
    licensing, consumers must consult `hasMax`/`hasMin` directly. -/
def Boundedness.isLicensed : Boundedness → Bool
  | .closed | .lowerBounded | .upperBounded => true
  | .open_ => false

-- ════════════════════════════════════════════════════
-- § 1b. MereoTag + LicensingPipeline
-- ════════════════════════════════════════════════════

/-- Binary mereological classification: the shared abstraction underlying
    all four licensing frameworks (Kennedy, Rouillard, Krifka, Zwarts). -/
inductive MereoTag where
  | qua  -- quantized / bounded / telic / closed
  | cum  -- cumulative / unbounded / atelic / open
  deriving DecidableEq, Repr

def MereoTag.toBoundedness : MereoTag → Boundedness
  | .qua => .closed
  | .cum => .open_

/-- A licensing pipeline: any type whose elements can be classified into
    scale boundedness. Kennedy, Rouillard, Krifka, and Zwarts all
    instantiate this with different source types but the same target.

    Core instances (`Boundedness`, `MereoTag`) live here. Domain-specific
    instances (`Telicity`, `VendlerClass`, `PathShape`, `BoundaryType`)
    live in their respective theory/bridge files. -/
class LicensingPipeline (α : Type*) where
  toBoundedness : α → Boundedness

namespace LicensingPipeline

variable {α : Type*} [LicensingPipeline α]

def isLicensed (a : α) : Bool :=
  (toBoundedness a).isLicensed

instance : LicensingPipeline Boundedness where
  toBoundedness := id

instance : LicensingPipeline MereoTag where
  toBoundedness := MereoTag.toBoundedness

/-- The universal licensing theorem: any two pipeline inputs that map to
    the same Boundedness yield the same licensing prediction, regardless
    of which framework they come. -/
theorem universal {α β : Type*} [LicensingPipeline α] [LicensingPipeline β]
    (a : α) (b : β) (h : toBoundedness a = toBoundedness b) :
    isLicensed a = isLicensed b := by
  simp only [isLicensed, h]

end LicensingPipeline

-- ════════════════════════════════════════════════════
-- § 1d. Scale Polarity
-- ════════════════════════════════════════════════════

/-- Intrinsic polarity of a scale dimension.
    `positive`: the unmarked direction (tall, hot, confident).
    `negative`: the marked/inverted direction (short, cold, doubtful). -/
inductive ScalePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

end Core.Scale
