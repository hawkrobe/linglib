import Mathlib.Order.UpperLower.Basic
import Linglib.Syntax.Minimalist.CyclicAgree

/-!
# Probe articulation: the segment order and its laws
[bejar-rezac-2009] [coon-keine-2021] [harley-ritter-2002]

The φ-feature geometry ([harley-ritter-2002]; [coon-keine-2021]'s
(11)) is a partial order on `CyclicAgree.Segment`: [π] is bottom and
[speaker]/[addressee] are the maximal leaves, with `s ≤ t` read as
"bearing `t` entails bearing `s`". Two laws of probe systems then
become order theory:

- **Articulation** ([bejar-rezac-2009]; [coon-keine-2021] (13)): a
  probe's segments are downward-closed along the geometry —
  `IsArticulated`, equivalent to mathlib's `IsLowerSet`
  (`isArticulated_iff_isLowerSet`). Goal specifications are also
  lower sets (`personSpec_isArticulated`): that is the geometric
  containment (author ⊂ participant ⊂ π) as order theory.
  [coon-keine-2021]'s fn. 22 flags probes with missing intermediate
  segments (their Me-First probe) as non-innocuous — here, they are
  exactly the non-lower-set probes. `Probe.Articulated` bundles the
  laws.
- **The probe-specification hierarchy** ([coon-keine-2021] (40)):
  `[uφ] → [uπ] → [uπ ▷ u#] → [uπ ▷ u# ▷ uΓ]`. `Probe.Stage` carries
  the hierarchy as a type: a number probe without a person probe is
  unrepresentable, which is how the account derives the missing
  "Number Case Constraint" (see `Studies/CoonKeine2021.lean`,
  `no_number_case_constraint`).

## Main declarations

- `Segment.below`, the `PartialOrder Segment` instance — the geometry.
- `IsArticulated` — downward-closure of a segment list; decidable.
- `Probe.Articulated` — segments + rootedness in [π] + closure.
- `Probe.Stage` — the (40) hierarchy, with `number_requires_person` /
  `gender_requires_number` as theorems.
-/

namespace Minimalist

open CyclicAgree (Segment)

/-! ### The segment order -/

instance : Fintype Segment :=
  ⟨⟨([.pi, .participant, .speaker, .addressee] : List Segment), by decide⟩,
   fun s => by cases s <;> decide⟩

/-- The downward closure of a single segment in the geometry
    ([coon-keine-2021] (11)): everything bearing this segment also
    bears these. -/
def CyclicAgree.Segment.below : Segment → List Segment
  | .pi => [.pi]
  | .participant => [.pi, .participant]
  | .speaker => [.pi, .participant, .speaker]
  | .addressee => [.pi, .participant, .addressee]

/-- The entailment order: `s ≤ t` iff bearing `t` entails bearing
    `s`. [π] is bottom; [speaker] and [addressee] are incomparable
    maximal leaves. -/
instance : PartialOrder Segment where
  le s t := s ∈ t.below
  le_refl s := by cases s <;> decide
  le_trans s t u hst htu := by
    revert hst htu; cases s <;> cases t <;> cases u <;> decide
  le_antisymm s t hst hts := by
    revert hst hts
    cases s <;> cases t <;> decide

instance : DecidableRel (α := Segment) (· ≤ ·) := fun s t =>
  inferInstanceAs (Decidable (s ∈ t.below))

instance : OrderBot Segment where
  bot := .pi
  bot_le s := by cases s <;> decide

/-! ### Articulation as downward closure -/

/-- A segment list is articulated iff it is downward-closed along
    the geometry ([bejar-rezac-2009]'s articulated probes;
    [coon-keine-2021] (13)). Goal specifications are articulated
    too — geometric containment and probe articulation are the same
    order-theoretic fact. -/
def IsArticulated (P : List Segment) : Prop :=
  ∀ s ∈ P, ∀ t, t ≤ s → t ∈ P

instance (P : List Segment) : Decidable (IsArticulated P) :=
  inferInstanceAs (Decidable (∀ s ∈ P, ∀ t, t ≤ s → t ∈ P))

/-- Articulation is mathlib's `IsLowerSet`, on the membership set. -/
theorem isArticulated_iff_isLowerSet (P : List Segment) :
    IsArticulated P ↔ IsLowerSet {s | s ∈ P} :=
  ⟨fun h _ _ hba ha => h _ ha _ hba, fun h s hs t hts => h hts hs⟩

/-- Person specifications are articulated, for both geometries: the
    [harley-ritter-2002] containment as a lower-set fact. -/
theorem personSpec_isArticulated (geom : CyclicAgree.Geometry) (p : Person) :
    IsArticulated (CyclicAgree.personSpec geom p) := by
  cases geom <;> cases p <;> decide

/-- [bejar-rezac-2009]'s named probes are all articulated. -/
theorem namedProbes_isArticulated :
    IsArticulated CyclicAgree.flatProbe ∧
    IsArticulated CyclicAgree.partialProbe ∧
    IsArticulated CyclicAgree.fullProbeStd ∧
    IsArticulated CyclicAgree.fullProbeAddr := by
  decide

/-- A bundled articulated probe: segments rooted in [uπ] (every
    probe of [coon-keine-2021]'s (13)/(39) contains [uPERS]) and
    downward-closed along the geometry. Probes with missing
    intermediate segments — [coon-keine-2021]'s Me-First (39c),
    flagged in their fn. 22 — fail `lower` and cannot be bundled. -/
structure Probe.Articulated where
  segments : Probe.Articulation
  rooted : Segment.pi ∈ segments
  lower : IsArticulated segments

/-- The family of search-level `Probe`s an articulated probe denotes,
    given a bearing relation for the goal type: one probe per
    segment ([bejar-rezac-2009]; [coon-keine-2021] (14)). An
    articulated probe is a *specification*; this is its canonical
    map into the `Probe` carrier — one-to-many, which is why the
    relationship is denotation, not extension. -/
def Probe.Articulated.toProbes {α : Type*} (P : Probe.Articulated)
    (bears : Segment → α → Bool) : List (Probe α) :=
  P.segments.map (fun s => .ofVis (bears s))

/-! ### The probe-specification hierarchy ([coon-keine-2021] (40)) -/

/-- The (40) hierarchy as a type:
    `[uφ] → [uπ] → [uπ ▷ u#] → [uπ ▷ u# ▷ uΓ]`. A φ-probe system is
    one of these four stages; unattested inventories — a number probe
    without a person probe, a gender probe without a number probe —
    are unrepresentable. The universal ordering (π probes before #,
    # before Γ) is carried by the stage itself. -/
inductive Probe.Stage where
  /-- A single unsplit [uφ] probe. -/
  | unsplit
  /-- A person probe only. -/
  | personOnly
  /-- Person and number probes, π ▷ #. -/
  | personNumber
  /-- Person, number, and gender probes, π ▷ # ▷ Γ. -/
  | personNumberGender
  deriving DecidableEq, Repr

/-- Does the stage have a dedicated person probe? -/
def Probe.Stage.hasPersonProbe : Probe.Stage → Bool
  | .unsplit => false
  | _ => true

/-- Does the stage have a number probe? -/
def Probe.Stage.hasNumberProbe : Probe.Stage → Bool
  | .personNumber | .personNumberGender => true
  | _ => false

/-- Does the stage have a gender probe? -/
def Probe.Stage.hasGenderProbe : Probe.Stage → Bool
  | .personNumberGender => true
  | _ => false

/-- (40), first law: a number probe entails a person probe. -/
theorem Probe.Stage.number_requires_person (st : Probe.Stage) :
    st.hasNumberProbe = true → st.hasPersonProbe = true := by
  cases st <;> decide

/-- (40), second law: a gender probe entails a number probe. -/
theorem Probe.Stage.gender_requires_number (st : Probe.Stage) :
    st.hasGenderProbe = true → st.hasNumberProbe = true := by
  cases st <;> decide

end Minimalist
