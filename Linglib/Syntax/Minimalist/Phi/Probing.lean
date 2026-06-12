import Linglib.Syntax.Agreement.Paradigm
import Linglib.Syntax.Minimalist.Phi.Geometry
import Linglib.Syntax.Minimalist.ObligatoryOperations

/-!
# Relativized probing over a goal sequence
[bejar-rezac-2003] [preminger-2014]

The derivational middle layer between DP-level probe visibility
(`probeVisible`, `Phi/Geometry.lean`) and PF-level outcomes
(`ProbeOutcome`, `ObligatoryOperations.lean`): a relativized probe
walks an ordered goal sequence, skips invisible goals, and returns
the first visible one. Licensing is being the goal found — from
which the Person Licensing Condition's effects derive: one search
licenses at most one goal (`allLicensed_iff`).

The search is stated for any goal type `α` with a `Bool` visibility
predicate; the φ-instantiation (`Agreement.Cell.visibleTo`, `PLC`)
specializes it to [bejar-rezac-2003]'s person probe. The same
search relativized to other features yields [halpert-2012]'s Zulu
augment probing — the cross-linguistic point of [preminger-2014]
Ch. 7. [bejar-rezac-2009]'s articulated probe is a *family* of
these searches, one per probe segment over the cyclically ordered
token list — see `CyclicAgree.eaIsLicensed_iff_segment_licensed`.
For probe *horizons* (what terminates search across domains, Keine)
see `Syntax/Minimalist/Probe.lean`; for conditional feature-acquiring
re-probing see `Syntax/Minimalist/Probing/DefectiveCircumvention.lean`.

## Main declarations

- `probeSearch` — first goal visible to the probe, in structural order.
- `searchOutcome` — the `ProbeOutcome` of an obligatory probing operation.
- `Licensed`, `AllLicensed` — licensing as being found by the search.
- `allLicensed_iff` — all visible goals licensed ↔ visible goals subsingleton.
- `PLC` — the Person Licensing Condition over φ-bearing goal tokens.
-/

namespace Minimalist

/-! ### Relativized search -/

section Search

variable {α : Type*}

/-- The goal a relativized probe finds in an ordered goal sequence:
    the first goal visible to it, skipping invisible ones
    ([bejar-rezac-2003] relativized probing). -/
def probeSearch (vis : α → Bool) (goals : List α) : Option α :=
  goals.find? vis

variable {vis : α → Bool} {goals : List α}

/-- A probe finds nothing iff no goal is visible to it. -/
@[simp]
theorem probeSearch_eq_none_iff :
    probeSearch vis goals = none ↔ ∀ a ∈ goals, vis a = false := by
  simp [probeSearch, List.find?_eq_none]

/-- The found goal is a member of the sequence. -/
theorem mem_of_probeSearch_eq_some {a : α}
    (h : probeSearch vis goals = some a) : a ∈ goals :=
  List.mem_of_find?_eq_some h

/-- The found goal is visible to the probe. -/
theorem visible_of_probeSearch_eq_some {a : α}
    (h : probeSearch vis goals = some a) : vis a = true :=
  List.find?_some h

end Search

/-! ### Probe outcomes ([preminger-2014] Ch. 5) -/

section Outcome

variable {α : Type*}

/-- The outcome of an obligatory probing operation over a goal
    sequence: `valued` iff the search finds a goal. -/
def searchOutcome (vis : α → Bool) (goals : List α) : ProbeOutcome :=
  if (probeSearch vis goals).isSome then .valued else .unvalued

variable {vis : α → Bool} {goals : List α}

/-- The probe is valued iff the search finds a goal. -/
theorem searchOutcome_eq_valued_iff_isSome :
    searchOutcome vis goals = .valued ↔ (probeSearch vis goals).isSome := by
  rw [searchOutcome]
  cases (probeSearch vis goals).isSome <;> decide

/-- The probe ends unvalued iff the search comes back empty. -/
theorem searchOutcome_eq_unvalued_iff_eq_none :
    searchOutcome vis goals = .unvalued ↔ probeSearch vis goals = none := by
  rw [searchOutcome]
  cases probeSearch vis goals <;>
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      if_false, if_true, reduceCtorEq]

/-- The probe is valued iff some goal is visible to it. -/
@[simp]
theorem searchOutcome_eq_valued_iff :
    searchOutcome vis goals = .valued ↔ ∃ a ∈ goals, vis a = true :=
  searchOutcome_eq_valued_iff_isSome.trans List.find?_isSome

/-- The probe ends unvalued iff no goal is visible to it. -/
@[simp]
theorem searchOutcome_eq_unvalued_iff :
    searchOutcome vis goals = .unvalued ↔ ∀ a ∈ goals, vis a = false := by
  rw [searchOutcome_eq_unvalued_iff_eq_none]
  exact probeSearch_eq_none_iff

end Outcome

/-! ### Licensing -/

section Licensing

variable {α : Type*}

/-- A goal is licensed by a probe iff the probe's single search
    reaches it ([bejar-rezac-2003]: licensing is an Agree relation
    with the probe). -/
def Licensed (vis : α → Bool) (goals : List α) (a : α) : Prop :=
  probeSearch vis goals = some a

instance [DecidableEq α] (vis : α → Bool) (goals : List α) (a : α) :
    Decidable (Licensed vis goals a) :=
  inferInstanceAs (Decidable (probeSearch vis goals = some a))

variable {vis : α → Bool} {goals : List α}

/-- One search licenses at most one goal. -/
theorem Licensed.unique {a b : α}
    (ha : Licensed vis goals a) (hb : Licensed vis goals b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- Every goal visible to the probe is licensed by it — the shape of
    a licensing condition over one probe's search. -/
def AllLicensed (vis : α → Bool) (goals : List α) : Prop :=
  ∀ a ∈ goals, vis a = true → Licensed vis goals a

instance [DecidableEq α] (vis : α → Bool) (goals : List α) :
    Decidable (AllLicensed vis goals) :=
  inferInstanceAs (Decidable (∀ a ∈ goals, vis a = true → Licensed vis goals a))

/-- All visible goals are licensed iff the visible goals are
    subsingleton: one search, one Agree relation, at most one
    licensee. The general fact behind person-restriction effects
    ([bejar-rezac-2003]'s PCC, [preminger-2014]'s AF restriction). -/
theorem allLicensed_iff :
    AllLicensed vis goals ↔
      ∀ a ∈ goals, ∀ b ∈ goals, vis a = true → vis b = true → a = b := by
  constructor
  · intro h a ha b hb hva hvb
    exact (h a ha hva).unique (h b hb hvb)
  · intro h a ha hva
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨a, ha, hva⟩)
    have hba := h b (mem_of_probeSearch_eq_some hb) a ha
      (visible_of_probeSearch_eq_some hb) hva
    exact hba ▸ hb

/-- `allLicensed_iff` in `Set.Subsingleton` form, for mathlib-API
    discoverability. -/
theorem allLicensed_iff_subsingleton :
    AllLicensed vis goals ↔ {a | a ∈ goals ∧ vis a = true}.Subsingleton := by
  rw [allLicensed_iff]
  exact ⟨fun h a ha b hb => h a ha.1 b hb.1 ha.2 hb.2,
         fun h a ha b hb hva hvb => h ⟨ha, hva⟩ ⟨hb, hvb⟩⟩

end Licensing

/-! ### φ-probes -/

/-- Visibility of a φ-cell to a relativized probe: the cell bears the
    feature the probe seeks (`probeVisible`, `Phi/Geometry.lean`). -/
def _root_.Agreement.Cell.visibleTo (c : Agreement.Cell) (t : ProbeTarget) : Bool :=
  probeVisible t c.toPerson c.isPlural

/-- The Person Licensing Condition ([bejar-rezac-2003];
    [preminger-2014] (40)/(75)): every [participant]-bearing goal
    token must be licensed by the person probe's search. Goal tokens
    have type `α` with a φ-cell projection, so two arguments with
    identical φ remain distinct licensees. -/
def PLC {α : Type*} (cellOf : α → Agreement.Cell) (goals : List α) : Prop :=
  AllLicensed (λ a => (cellOf a).visibleTo .participant) goals

instance {α : Type*} [DecidableEq α] (cellOf : α → Agreement.Cell) (goals : List α) :
    Decidable (PLC cellOf goals) :=
  inferInstanceAs (Decidable (AllLicensed _ goals))

end Minimalist
