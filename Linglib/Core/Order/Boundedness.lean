import Mathlib.Order.Basic
import Mathlib.Order.WithBot
import Mathlib.Order.Nat
import Mathlib.Order.Max
import Mathlib.Order.BoundedOrder.Basic

/-!
# Scale boundedness and the licensing pipeline
[kennedy-mcnally-2005] [kennedy-2007] [rotstein-winter-2004] [rouillard-2026]

Foundational scale-classification types used across all gradability/degree
substrate. No framework-specific operators here (those live in
`Semantics/Gradability/`).

## Main declarations

- `Boundedness`: the four-way endpoint classification, with `HasMax` /
  `HasMin` / `IsLicensed` predicates.
- `MereoTag`, `EpistemicTag`: binary classifications mapping into
  `Boundedness`.
- `LicensingPipeline`: typeclass for types classifiable into `Boundedness`,
  with the `universal` agreement theorem.
- `ScalePolarity`.
-/

namespace Core.Order

/-! ### Scale boundedness -/

/-- Classification of scale boundedness.
    [kennedy-mcnally-2005] eq (1) and [kennedy-2007] §4.2 eq (59):
    four scale types based on which endpoints exist (independently
    discovered by [rotstein-winter-2004]).
    [rouillard-2026]: temporal domains have similar boundary structure
    (closed intervals have both bounds, open intervals lack them).

    This enum is the **lexical data tag** for classifying scales in fragment
    entries and phenomena files — a role mathlib's typeclass instances cannot
    play (you cannot store an `[OrderTop α]` instance in a record field).
    The actual order-theoretic properties of concrete scale types are
    encoded via Mathlib typeclasses (`OrderTop`, `OrderBot`, `NoMaxOrder`,
    `NoMinOrder`); the two encodings serve different roles and both are real.

    **Standard-type dimension.** [kennedy-2007] §4.3 eq (66) (Interpretive
    Economy) DERIVES standard type (relative / min-absolute / max-absolute)
    from scale structure for `open_`, `lowerBounded`, and `upperBounded`. For
    `closed`, all three interpretations are licensed (see eq 67: *opaque*,
    *transparent*) — this enum doesn't capture that disambiguation. Fragment
    entries with `boundedness = .closed` may need a separate `standardType`
    slot if downstream theorems care about the distinction.

    **Open-bounded sub-distinction.** [kennedy-2007] fn 28: open scales
    can be further distinguished by whether they approach a value (e.g. 0 for
    cost) but don't include it, vs. completely unbounded. Not captured here. -/
inductive Boundedness where
  | open_        -- no inherent bounds (Kennedy: tall; Rouillard: atelic VP)
  | lowerBounded -- minimum exists, no maximum (Kennedy: wet; Rouillard: N/A)
  | upperBounded -- maximum exists, no minimum (Kennedy: dry; Rouillard: N/A)
  | closed       -- both bounds exist (Kennedy: full; Rouillard: telic VP)
  deriving DecidableEq, Repr

/-- Does this scale have an inherent maximum? -/
def Boundedness.HasMax : Boundedness → Prop
  | .upperBounded | .closed => True
  | .open_ | .lowerBounded => False

instance : DecidablePred Boundedness.HasMax
  | .open_ => isFalse id
  | .lowerBounded => isFalse id
  | .upperBounded => isTrue trivial
  | .closed => isTrue trivial

/-- Does this scale have an inherent minimum? -/
def Boundedness.HasMin : Boundedness → Prop
  | .lowerBounded | .closed => True
  | .open_ | .upperBounded => False

instance : DecidablePred Boundedness.HasMin
  | .open_ => isFalse id
  | .lowerBounded => isTrue trivial
  | .upperBounded => isFalse id
  | .closed => isTrue trivial

/-- "Any endpoint exists": the scale has at least one bound (max or min);
    an open scale has none.

    **NOT [kennedy-2007]'s full licensing prediction.** Kennedy's actual
    prediction is the 4×2 modifier-class matrix in [kennedy-2007]
    eq (61) (= [kennedy-mcnally-2005] eq (15)): maximizers
    (*completely, perfectly*) require an UPPER endpoint; minimizers
    (*slightly, partially*) require a LOWER endpoint; proportional modifiers
    (*half*) require BOTH — for modifier-specific licensing, consult
    `HasMax`/`HasMin` directly. This predicate suffices for callers that
    only distinguish "open" from "any-endpoint-exists" (Interpretive
    Economy, [kennedy-2007] §4.3; Rouillard's MIP, [rouillard-2026]). -/
def Boundedness.IsLicensed : Boundedness → Prop
  | .closed | .lowerBounded | .upperBounded => True
  | .open_ => False

instance : DecidablePred Boundedness.IsLicensed
  | .open_ => isFalse id
  | .lowerBounded => isTrue trivial
  | .upperBounded => isTrue trivial
  | .closed => isTrue trivial

/-! ### MereoTag and the licensing pipeline -/

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

/-- A pipeline input is licensed iff its boundedness classification is. -/
def IsLicensed (a : α) : Prop :=
  (toBoundedness a).IsLicensed

instance : DecidablePred (IsLicensed (α := α)) := fun a =>
  inferInstanceAs (Decidable (toBoundedness a).IsLicensed)

instance : LicensingPipeline Boundedness where
  toBoundedness := id

instance : LicensingPipeline MereoTag where
  toBoundedness := MereoTag.toBoundedness

/-- The universal licensing theorem: any two pipeline inputs that map to
    the same Boundedness yield the same licensing prediction, regardless
    of which framework they come. -/
theorem universal {α β : Type*} [LicensingPipeline α] [LicensingPipeline β]
    (a : α) (b : β) (h : toBoundedness a = toBoundedness b) :
    IsLicensed a ↔ IsLicensed b := by
  unfold IsLicensed
  rw [h]

end LicensingPipeline

/-- Binary epistemic classification, parallel to `MereoTag`: finitely additive
    scales are closed (endpoint standards licensed), qualitative scales open. -/
inductive EpistemicTag where
  | finitelyAdditive
  | qualitative
  deriving DecidableEq, Repr

instance : LicensingPipeline EpistemicTag where
  toBoundedness
    | .finitelyAdditive => .closed
    | .qualitative => .open_

theorem epistemicFA_licensed :
    LicensingPipeline.IsLicensed EpistemicTag.finitelyAdditive := trivial

theorem epistemicQualitative_blocked :
    ¬ LicensingPipeline.IsLicensed EpistemicTag.qualitative := id

theorem five_frameworks_agree
    (m : MereoTag) (e : EpistemicTag)
    (h : LicensingPipeline.toBoundedness m = LicensingPipeline.toBoundedness e) :
    LicensingPipeline.IsLicensed m ↔ LicensingPipeline.IsLicensed e :=
  LicensingPipeline.universal m e h

theorem epistemicFA_iff_qua :
    LicensingPipeline.IsLicensed EpistemicTag.finitelyAdditive ↔
    LicensingPipeline.IsLicensed MereoTag.qua := Iff.rfl

theorem epistemicQualitative_iff_cum :
    LicensingPipeline.IsLicensed EpistemicTag.qualitative ↔
    LicensingPipeline.IsLicensed MereoTag.cum := Iff.rfl

/-! ### Scale polarity -/

/-- Intrinsic polarity of a scale dimension.
    `positive`: the unmarked direction (tall, hot, confident).
    `negative`: the marked/inverted direction (short, cold, doubtful). -/
inductive ScalePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr


/-! ### Degree carrier per scale shape

A computable order-proxy carrier for each boundedness shape — only the
`OrderTop`/`NoMaxOrder` mixin matters, not the carrier. The grounding is
proved once at the 4-case level; per-dimension views transport it
(`Features.ScalarDimension.degree`). -/

/-- Degree carrier per boundedness shape: a greatest element exists exactly
    when the scale `HasMax`. -/
abbrev Boundedness.degreeShape : Boundedness → Type
  | .open_ | .lowerBounded => ℕ
  | .upperBounded | .closed => WithTop ℕ

instance instLinearOrderDegreeShape (b : Boundedness) : LinearOrder b.degreeShape := by
  cases b <;> exact inferInstance

/-- A greatest degree exists exactly when the classification says `HasMax`. -/
theorem Boundedness.hasGreatest_degreeShape_iff (b : Boundedness) :
    (∃ m : b.degreeShape, IsTop m) ↔ b.HasMax := by
  cases b
  · exact iff_of_false (fun ⟨m, hm⟩ => not_isMax m hm.isMax) (by decide)
  · exact iff_of_false (fun ⟨m, hm⟩ => not_isMax m hm.isMax) (by decide)
  · exact iff_of_true ⟨⊤, isTop_top⟩ (by decide)
  · exact iff_of_true ⟨⊤, isTop_top⟩ (by decide)

end Core.Order
