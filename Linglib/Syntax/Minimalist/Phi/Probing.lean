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
specializes it to the participant-relativized person probe of
[preminger-2014]'s Kichean analysis. Relativization is Preminger's
addition (§4.2, recalling [rizzi-1990]): [bejar-rezac-2003]'s own
π-probe is *unrelativized* — the closest goal matches and can
absorb it without valuing (`probeAgree`; `Studies/BejarRezac2003.lean`)
— and the unrelativized, bare-minimality instance (`vis = ⊤`, goal
= `List.head?`) is also [halpert-2012]'s Zulu L⁰
(`Studies/Halpert2012.lean`, the cross-linguistic point of
[preminger-2014] Ch. 7). [bejar-rezac-2009]'s articulated probe is a *family* of
these searches, one per probe segment over the cyclically ordered
token list — see `CyclicAgree.eaIsLicensed_iff_segment_licensed`.
For probe *horizons* (what terminates search across domains, Keine)
see `Syntax/Minimalist/Probe.lean`; for conditional feature-acquiring
re-probing see `Syntax/Minimalist/Probing/DefectiveCircumvention.lean`.

## Main declarations

- `probeSearch` — first goal visible to the probe, in structural order.
- `probeAgree` — search then Agree: the found goal, if it passes the
  activity condition (match without valuation absorbs the probe).
- `searchOutcome` — the `ProbeOutcome` of an obligatory probing operation.
- `Licensed`, `AllLicensed needs vis` — every licensing-needy goal is
  found by the search; diagonal characterization `allLicensed_iff`
  (visible goals subsingleton), off-diagonal
  `allLicensed_const_true_iff` (every needy goal is the closest).
- `cascadeSearch` — ordered probe sequence: first probe with output wins
  (the single-slot morphological competition).
- `PLC` — the Person Licensing Condition over φ-bearing goal tokens.
-/

namespace Minimalist

variable {α : Type*}

/-! ### Relativized search -/

section Search

/-- The goal a probe finds in an ordered goal sequence: the first
    goal visible to it, skipping invisible ones (relativized probing,
    [preminger-2014] §4.2; an unrelativized probe — `vis = ⊤` — takes
    the closest goal outright). -/
def probeSearch (vis : α → Bool) (goals : List α) : Option α :=
  goals.find? vis

/-- Search then Agree: the goal the search finds, if it passes the
    activity condition `act` — the match vs. Agree distinction. The
    closest visible goal can absorb the probe without valuing it
    ([bejar-rezac-2003]'s inactive dative, `Studies/BejarRezac2003.lean`;
    [deal-2024]-style interaction vs. satisfaction,
    `Studies/Scott2023.lean`). -/
def probeAgree (vis act : α → Bool) (goals : List α) : Option α :=
  (probeSearch vis goals).filter act

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

/-- The probe Agrees with `a` iff the search finds `a` and `a` is
    active. -/
theorem probeAgree_eq_some_iff {act : α → Bool} {a : α} :
    probeAgree vis act goals = some a ↔
      probeSearch vis goals = some a ∧ act a = true := by
  cases h : probeSearch vis goals with
  | none => simp [probeAgree, h]
  | some b =>
    simp only [probeAgree, h, Option.filter_some, Option.ite_none_right_eq_some,
      Option.some.injEq]
    constructor
    · rintro ⟨hb, rfl⟩
      exact ⟨rfl, hb⟩
    · rintro ⟨hb, ha⟩
      exact ⟨hb ▸ ha, hb.symm ▸ rfl⟩

/-- An inactive closest goal absorbs the probe: match without Agree. -/
theorem probeAgree_eq_none_of_inactive {act : α → Bool} {a : α}
    (h : probeSearch vis goals = some a) (ha : act a = false) :
    probeAgree vis act goals = none := by
  simp [probeAgree, h, Option.filter_some, ha]

end Search

/-! ### Probe outcomes ([preminger-2014] Ch. 5) -/

section Outcome

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

/-- Licensing by an unrelativized probe (`vis = ⊤`) is being the
    structurally closest goal — bare minimality, [halpert-2012]'s
    indiscriminate L⁰. -/
theorem licensed_const_true_iff {a : α} :
    Licensed (fun _ => true) goals a ↔ goals.head? = some a := by
  unfold Licensed probeSearch
  cases goals <;>
    simp only [List.find?_nil, List.find?_cons_of_pos, List.head?_nil,
      List.head?_cons]

/-- Every goal that needs licensing is licensed by the probe's
    search. Which goals *need* licensing (`needs`) and which the
    probe *sees* (`vis`) come apart in general: [halpert-2012]'s Zulu
    L⁰ sees every goal (augmented nominals intervene) while only
    augmentless nominals need it. Feature-relativized probes are the
    diagonal `AllLicensed vis vis` — the probe sees exactly the needy
    ([bejar-rezac-2003]'s π⁰). -/
def AllLicensed (needs vis : α → Bool) (goals : List α) : Prop :=
  ∀ a ∈ goals, needs a = true → Licensed vis goals a

instance [DecidableEq α] (needs vis : α → Bool) (goals : List α) :
    Decidable (AllLicensed needs vis goals) :=
  inferInstanceAs (Decidable (∀ a ∈ goals, needs a = true → Licensed vis goals a))

/-- On the diagonal (probe relativized to exactly the needy), all
    needy goals are licensed iff the visible goals are subsingleton:
    one search, one Agree relation, at most one licensee — the fact
    behind [preminger-2014]'s AF person restriction. (The off-diagonal
    variant of the same one-licensee engine drives
    [bejar-rezac-2003]'s PCC — `Studies/BejarRezac2003.lean`.) -/
theorem allLicensed_iff :
    AllLicensed vis vis goals ↔
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
    AllLicensed vis vis goals ↔ {a | a ∈ goals ∧ vis a = true}.Subsingleton := by
  rw [allLicensed_iff]
  exact ⟨fun h a ha b hb => h a ha.1 b hb.1 ha.2 hb.2,
         fun h a ha b hb hva hvb => h ⟨ha, hva⟩ ⟨hb, hvb⟩⟩

/-- Off the diagonal, licensing by an unrelativized probe pins every
    needy goal to the head of the sequence — the highest-element
    condition ([halpert-2012]: an augmentless nominal must be the
    highest nominal in its vP). -/
theorem allLicensed_const_true_iff {needs : α → Bool} :
    AllLicensed needs (fun _ => true) goals ↔
      ∀ a ∈ goals, needs a = true → goals.head? = some a :=
  forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    licensed_const_true_iff

end Licensing

/-! ### Probe cascades -/

section Cascade

/-- The goal an ordered sequence of probes delivers: the first probe's
    finding, else the next's, and so on — `probeSearch` at the goal
    level composed with `List.findSome?` at the probe level. This is
    also the single-slot morphological competition: the first probe
    with output wins the slot ([preminger-2014] §4.4: π⁰'s clitic
    beats #⁰'s exponent beats nothing). -/
def cascadeSearch (probes : List (α → Bool)) (goals : List α) : Option α :=
  probes.findSome? (probeSearch · goals)

variable {probes : List (α → Bool)} {goals : List α}

/-- A cascade delivers nothing iff no goal is visible to any probe. -/
@[simp]
theorem cascadeSearch_eq_none_iff :
    cascadeSearch probes goals = none ↔
      ∀ p ∈ probes, ∀ a ∈ goals, p a = false := by
  simp [cascadeSearch, List.findSome?_eq_none_iff]

/-- Unfold one probe of the cascade. -/
theorem cascadeSearch_cons {p : α → Bool} :
    cascadeSearch (p :: probes) goals =
      (probeSearch p goals <|> cascadeSearch probes goals) := by
  rw [cascadeSearch, List.findSome?_cons]
  cases probeSearch p goals <;> rfl

/-- The cascade's goal is licensed by one of its probes. -/
theorem exists_licensed_of_cascadeSearch_eq_some {a : α}
    (h : cascadeSearch probes goals = some a) :
    ∃ p ∈ probes, Licensed p goals a :=
  List.exists_of_findSome?_eq_some h

/-- The cascade's goal is a member of the sequence. -/
theorem mem_of_cascadeSearch_eq_some {a : α}
    (h : cascadeSearch probes goals = some a) : a ∈ goals :=
  let ⟨_, _, hp⟩ := exists_licensed_of_cascadeSearch_eq_some h
  mem_of_probeSearch_eq_some hp

end Cascade

/-! ### φ-probes -/

/-- Visibility of a φ-cell to a relativized probe: the cell bears the
    feature the probe seeks (`probeVisible`, `Phi/Geometry.lean`). -/
def _root_.Agreement.Cell.visibleTo (c : Agreement.Cell) (t : ProbeTarget) : Bool :=
  probeVisible t c.toPerson c.isPlural

/-- The Person Licensing Condition ([bejar-rezac-2003];
    [preminger-2014] (40)/(75)): every [participant]-bearing goal
    token must be licensed by the person probe's search. Goal tokens
    have type `α` with a φ-cell projection, so two arguments with
    identical φ remain distinct licensees.

    This is [preminger-2014]'s single-cycle, search-only, diagonal
    rendering of the condition: it omits [bejar-rezac-2003]'s
    F-licensing route (a nominal's own φ-bearing P/dative/focus head
    counts as a licensing Agree relation) and multi-cycle repairs —
    for the paper's own condition see `BejarRezac2003.PLCOk`. -/
def PLC (cellOf : α → Agreement.Cell) (goals : List α) : Prop :=
  AllLicensed (λ a => (cellOf a).visibleTo .participant)
    (λ a => (cellOf a).visibleTo .participant) goals

instance [DecidableEq α] (cellOf : α → Agreement.Cell) (goals : List α) :
    Decidable (PLC cellOf goals) :=
  inferInstanceAs (Decidable (AllLicensed _ _ goals))

end Minimalist
