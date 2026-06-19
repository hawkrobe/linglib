import Mathlib.Data.Set.Subsingleton
import Mathlib.Data.List.Basic

/-!
# Probe: relativized search over a goal sequence
[bejar-rezac-2003] [preminger-2014]

The canonical, theory-agnostic relativized-*search* kernel. A `Probe α`
searches a goal sequence of arbitrary type `α`; probe *specifications*
(relativized targets, satisfaction conditions, horizon profiles,
articulated/dynamic probes) denote one of these by a `toProbe`-map
rather than re-implementing search (see **Probe specifications**). The
probe bundles what it *sees* (`vis` — interaction/halting: the search
stops at the first visible goal) and what it can *value* there (`act` —
activity: a visible but inactive goal absorbs the probe without valuing
it, [bejar-rezac-2003]'s inactive dative, [deal-2024]-style interaction
vs. satisfaction). Licensing is being the goal the search reaches — from
which the Person Licensing Condition's effects derive: one search
licenses at most one goal (`Probe.allLicensed_iff`).

Scope: this models a probe's *search* (locality, intervention,
satisfaction). Feature *transmission* — what a successful Agree copies,
shares, or values, and Multiple-Agree-style simultaneous valuation of
several goals — is a separate concern (`applyAgree`, `Agree.lean`) not
folded into `Probe`.

This file is the maximally-general core (`α` arbitrary); the φ-feature
*specialization* (`Agreement.Cell.visibleTo`, `Probe.Target.toProbe`,
`PLC`) lives in `Probe/Phi.lean`, the Deal satisfaction-condition spec
in `Probe/Satisfaction.lean`, and Keine's locality/horizon spec in
`Probe/Profile.lean`. There is no umbrella; import the leaf you need.

Relativization is [preminger-2014]'s addition (§4.2, recalling
[rizzi-1990]): the φ-instantiation (`Agreement.Cell.visibleTo`, `PLC`)
specializes `vis` to his participant-relativized person probe.
[bejar-rezac-2003]'s own π-probe is *unrelativized* — the closest goal
matches and can absorb it (`Studies/BejarRezac2003.lean`) — and the
unrelativized, bare-minimality probe (`Probe.indiscriminate`, goal =
`List.head?`) is [halpert-2012]'s Zulu L⁰ (`Studies/Halpert2012.lean`,
the cross-linguistic point of [preminger-2014] Ch. 7).
[bejar-rezac-2009]'s articulated probe is a *family* of these searches,
one per probe segment over the cyclically ordered token list — see
`CyclicAgree.eaIsLicensed_iff_segment_licensed`, and
`Phi/Articulation.lean` for the laws of articulation. For probe
*horizons* (what terminates search across domains, Keine) see
`Probe/Profile.lean`; for conditional feature-acquiring re-probing see
`Syntax/Minimalist/Probing/DefectiveCircumvention.lean`.

## Main declarations

- `Probe` — the bundled object: `vis` + `act`; `Probe.ofVis`,
  `Probe.indiscriminate` constructors.
- `Probe.search` — first visible goal, in structural order.
- `Probe.agree` — search then Agree: the found goal, if active.
- `Probe.outcome` — the `Probe.Outcome` of an obligatory probing
  operation.
- `Probe.Licensed`, `Probe.AllLicensed needs` — every licensing-needy
  goal is found by the search; diagonal characterization
  `Probe.allLicensed_iff` (visible goals subsingleton), indiscriminate
  characterization `Probe.indiscriminate_allLicensed_iff` (every needy
  goal is the closest).
- `Probe.cascade` — ordered probe sequence: first probe with output
  wins (the single-slot morphological competition).

## Probe specifications

Theory-side probe descriptions relate to `Probe` by *denotation*
(canonical `toProbe`-maps), not extension — the relationship is
one-to-many for articulated probes and state-indexed for dynamic
ones: `Probe.Target.toProbe` (`Probe/Phi.lean`),
`SatisfactionCond.toProbe` (`Probe/Satisfaction.lean`),
`Probe.Profile.toProbe` (`Probe/Profile.lean`),
`Probe.Articulated.toProbes` (`Phi/Articulation.lean`, the per-segment
family), `CyclicAgree.segProbe` (per segment and geometry), and
`Deal2024.ProbeState.probe` (the state-indexed family whose narrowing
law is `probe_vis_antitone`).

## TODO

- **Transmission axis.** `Probe` models *search*, not what a successful
  Agree copies/shares/values. A `Probe.agreeWith : Probe α → (α → V) →
  List α → Σ` (Σ = `Option V` / `List V` for [hiraiwa-2001] Multiple
  Agree / a shared-occurrence type for Frampton-Gutmann feature-sharing)
  would fold `applyAgree`, Multiple Agree, Agree-Link/Copy
  ([arregi-nevins-2012]), and case-by-Agree into one extension.
- **Upward Agree.** Search is downward (c-command, `search_eq_some_iff_closest`);
  add a direction parameter for Bjorkman & Zeijlstra (2019)-style upward Agree.
- **`Preorder (Probe α)`** by pointwise `vis`-refinement, so
  `outcome_valued_mono` / `Deal2024.probe_vis_antitone` become order facts.
- **`Articulated.toProbes` ↔ `cascade` bridge**: prove an articulated
  probe's behaviour is the cascade of its segment probes.
- **`HalpertHammerly2026.agreementClass`**: re-stipulated relativized
  search; should be two `Probe` searches with a `_eq_derived` theorem.
-/

namespace Minimalist

variable {α : Type*}

/-- A probe over goals of type `α`: what it sees (`vis` — a visible
    goal halts the search) and what it can value there (`act` — a
    visible but inactive goal absorbs the probe without valuing it).
    `act` defaults to always-active. -/
structure Probe (α : Type*) where
  vis : α → Bool
  act : α → Bool := fun _ => true

/-- The outcome of an obligatory probing operation: `valued` if the
    search found a goal, else `unvalued`. The PF/convergence
    interpretation (crash vs. default morphology) lives in
    `ObligatoryOperations.lean`. -/
inductive Probe.Outcome where
  | valued
  | unvalued
  deriving DecidableEq, Repr

namespace Probe

/-- A probe with a visibility condition and no activity restriction. -/
def ofVis (vis : α → Bool) : Probe α := { vis := vis }

/-- The indiscriminate probe: sees every goal, so bare minimality
    delivers the closest one ([halpert-2012]'s L⁰). -/
def indiscriminate : Probe α := ofVis fun _ => true

/-! ### Search -/

/-- The goal a probe finds in an ordered goal sequence: the first
    goal visible to it, skipping invisible ones. -/
def search (p : Probe α) (goals : List α) : Option α :=
  goals.find? p.vis

/-- Search then Agree: the found goal, if it passes the activity
    condition. A visible inactive goal absorbs the probe. -/
def agree (p : Probe α) (goals : List α) : Option α :=
  (p.search goals).filter p.act

variable {p : Probe α} {goals : List α}

/-- A probe finds nothing iff no goal is visible to it. -/
@[simp]
theorem search_eq_none_iff :
    p.search goals = none ↔ ∀ a ∈ goals, p.vis a = false := by
  simp [search, List.find?_eq_none]

/-- The found goal is a member of the sequence. -/
theorem mem_of_search_eq_some {a : α}
    (h : p.search goals = some a) : a ∈ goals :=
  List.mem_of_find?_eq_some h

/-- The found goal is visible to the probe. -/
theorem visible_of_search_eq_some {a : α}
    (h : p.search goals = some a) : p.vis a = true :=
  List.find?_some h

/-- Over a two-goal sequence whose lower goal's visibility entails
    the higher's, the search lands on the higher goal if anywhere —
    the kernel of "gluttony/competition only in inverse
    configurations" ([coon-keine-2021]) and of highest-only licensing
    ([halpert-2012]). -/
theorem search_pair_of_imp {a b : α}
    (h : p.vis b = true → p.vis a = true) :
    p.search [a, b] = if p.vis a = true then some a else none := by
  by_cases ha : p.vis a = true
  · rw [if_pos ha]
    show List.find? p.vis [a, b] = some a
    simp [List.find?, ha]
  · rw [if_neg ha]
    have hb : p.vis b = false := by
      cases hvb : p.vis b
      · rfl
      · exact absurd (h hvb) ha
    have ha' : p.vis a = false := by
      cases hva : p.vis a
      · rfl
      · exact absurd hva ha
    show List.find? p.vis [a, b] = none
    simp [List.find?, ha', hb]

/-- The probe Agrees with `a` iff the search finds `a` and `a` is
    active. -/
theorem agree_eq_some_iff {a : α} :
    p.agree goals = some a ↔
      p.search goals = some a ∧ p.act a = true := by
  cases h : p.search goals with
  | none => simp [agree, h]
  | some b =>
    simp only [agree, h, Option.filter_some, Option.ite_none_right_eq_some,
      Option.some.injEq]
    constructor
    · rintro ⟨hb, rfl⟩
      exact ⟨rfl, hb⟩
    · rintro ⟨hb, ha⟩
      exact ⟨hb ▸ ha, hb.symm ▸ rfl⟩

/-- An inactive closest goal absorbs the probe: match without Agree. -/
theorem agree_eq_none_of_inactive {a : α}
    (h : p.search goals = some a) (ha : p.act a = false) :
    p.agree goals = none := by
  simp [agree, h, Option.filter_some, ha]

@[simp] theorem search_nil : p.search [] = none := rfl

/-- Satisfaction refines interaction: what the probe Agrees with, it found. -/
theorem agree_le_search {a : α} (h : p.agree goals = some a) :
    p.search goals = some a :=
  (agree_eq_some_iff.mp h).1

/-- When every goal is active, Agree coincides with search — the `act`
    gate is degenerate for `ofVis`-built probes. -/
theorem agree_eq_search_of_act (h : ∀ a, p.act a = true) :
    p.agree goals = p.search goals := by
  rw [agree]
  cases p.search goals with
  | none => rfl
  | some a => rw [Option.filter_some, if_pos (h a)]

theorem agree_eq_none_iff :
    p.agree goals = none ↔ ¬ ∃ a, p.search goals = some a ∧ p.act a = true := by
  simp only [← Option.not_isSome_iff_eq_none, Option.isSome_iff_exists, agree_eq_some_iff]

/-- Locality as list search: the probe finds `a` iff `a` is visible and
    every earlier goal is invisible (no intervener). -/
theorem search_eq_some_iff_closest {a : α} :
    p.search goals = some a ↔
      p.vis a ∧ ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁, !p.vis b :=
  List.find?_eq_some_iff_append

/-! ### Outcomes ([preminger-2014] Ch. 5) -/

/-- The outcome of an obligatory probing operation over a goal
    sequence: `valued` iff the search finds a goal. -/
def outcome (p : Probe α) (goals : List α) : Probe.Outcome :=
  if (p.search goals).isSome then .valued else .unvalued

/-- The probe is valued iff the search finds a goal. -/
theorem outcome_eq_valued_iff_isSome :
    p.outcome goals = .valued ↔ (p.search goals).isSome := by
  rw [outcome]
  cases (p.search goals).isSome <;> decide

/-- The probe ends unvalued iff the search comes back empty. -/
theorem outcome_eq_unvalued_iff_eq_none :
    p.outcome goals = .unvalued ↔ p.search goals = none := by
  rw [outcome]
  cases p.search goals <;>
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      if_false, if_true, reduceCtorEq]

/-- The probe is valued iff some goal is visible to it. -/
@[simp]
theorem outcome_eq_valued_iff :
    p.outcome goals = .valued ↔ ∃ a ∈ goals, p.vis a = true :=
  outcome_eq_valued_iff_isSome.trans List.find?_isSome

/-- The probe ends unvalued iff no goal is visible to it. -/
@[simp]
theorem outcome_eq_unvalued_iff :
    p.outcome goals = .unvalued ↔ ∀ a ∈ goals, p.vis a = false := by
  rw [outcome_eq_unvalued_iff_eq_none]
  exact search_eq_none_iff

/-- Widening visibility can only keep a probe valued: if `p` is valued
    and `q` sees everything `p` sees (among `goals`), so is `q`. The
    substrate home of [deal-2024]-style narrowing (`Deal2024`'s
    `probe_vis_antitone` is the contrapositive on a probe family). -/
theorem outcome_valued_mono {q : Probe α}
    (h : ∀ a ∈ goals, p.vis a = true → q.vis a = true) :
    p.outcome goals = .valued → q.outcome goals = .valued := by
  simp only [outcome_eq_valued_iff]
  rintro ⟨a, ha, hva⟩
  exact ⟨a, ha, h a ha hva⟩

/-! ### Licensing -/

/-- A goal is licensed by a probe iff the probe's single search
    reaches it ([bejar-rezac-2003]: licensing is an Agree relation
    with the probe). -/
def Licensed (p : Probe α) (goals : List α) (a : α) : Prop :=
  p.search goals = some a

instance [DecidableEq α] (p : Probe α) (goals : List α) (a : α) :
    Decidable (p.Licensed goals a) :=
  inferInstanceAs (Decidable (p.search goals = some a))

/-- One search licenses at most one goal. -/
theorem Licensed.unique {a b : α}
    (ha : p.Licensed goals a) (hb : p.Licensed goals b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- Licensing is being the closest visible goal: no matching goal
    intervenes (`search_eq_some_iff_closest` in the licensing API). -/
theorem licensed_iff_closest {a : α} :
    p.Licensed goals a ↔
      p.vis a ∧ ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁, !p.vis b :=
  search_eq_some_iff_closest

/-- A licensed goal is a member of the sequence. -/
theorem Licensed.mem {a : α} (h : p.Licensed goals a) : a ∈ goals :=
  mem_of_search_eq_some h

/-- A licensed goal is visible to the probe. -/
theorem Licensed.vis {a : α} (h : p.Licensed goals a) : p.vis a = true :=
  visible_of_search_eq_some h

/-- Licensing by the indiscriminate probe is being the structurally
    closest goal — bare minimality, [halpert-2012]'s L⁰. -/
theorem indiscriminate_licensed_iff {a : α} :
    (indiscriminate : Probe α).Licensed goals a ↔ goals.head? = some a := by
  unfold Licensed search indiscriminate ofVis
  cases goals <;>
    simp only [List.find?_nil, List.find?_cons_of_pos, List.head?_nil,
      List.head?_cons]

/-- Every goal that needs licensing is licensed by the probe's
    search. Which goals *need* licensing (`needs`) and which the
    probe *sees* (`p.vis`) come apart in general: [halpert-2012]'s
    Zulu L⁰ sees every goal (augmented nominals intervene) while only
    augmentless nominals need it. Feature-relativized probes are the
    diagonal `p.AllLicensed p.vis` — the probe sees exactly the needy
    ([bejar-rezac-2003]'s π as relativized by [preminger-2014]). -/
def AllLicensed (p : Probe α) (needs : α → Bool) (goals : List α) : Prop :=
  ∀ a ∈ goals, needs a = true → p.Licensed goals a

instance [DecidableEq α] (p : Probe α) (needs : α → Bool) (goals : List α) :
    Decidable (p.AllLicensed needs goals) :=
  inferInstanceAs (Decidable (∀ a ∈ goals, needs a = true → p.Licensed goals a))

/-- On the diagonal (probe relativized to exactly the needy), all
    needy goals are licensed iff the visible goals are subsingleton:
    one search, one Agree relation, at most one licensee — the fact
    behind [preminger-2014]'s AF person restriction. (The
    off-diagonal variant of the same one-licensee engine drives
    [bejar-rezac-2003]'s PCC — `Studies/BejarRezac2003.lean`.) -/
theorem allLicensed_iff {vis : α → Bool} {goals : List α} :
    (ofVis vis).AllLicensed vis goals ↔
      ∀ a ∈ goals, ∀ b ∈ goals, vis a = true → vis b = true → a = b := by
  constructor
  · intro h a ha b hb hva hvb
    exact (h a ha hva).unique (h b hb hvb)
  · intro h a ha hva
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨a, ha, hva⟩)
    have hba := h b (mem_of_search_eq_some (p := ofVis vis) hb) a ha
      (visible_of_search_eq_some (p := ofVis vis) hb) hva
    exact hba ▸ hb

/-- `allLicensed_iff` in `Set.Subsingleton` form, for mathlib-API
    discoverability. -/
theorem allLicensed_iff_subsingleton {vis : α → Bool} {goals : List α} :
    (ofVis vis).AllLicensed vis goals ↔
      {a | a ∈ goals ∧ vis a = true}.Subsingleton := by
  rw [allLicensed_iff]
  exact ⟨fun h a ha b hb => h a ha.1 b hb.1 ha.2 hb.2,
         fun h a ha b hb hva hvb => h ⟨ha, hva⟩ ⟨hb, hvb⟩⟩

/-- Licensing by the indiscriminate probe pins every needy goal to
    the head of the sequence — the highest-element condition
    ([halpert-2012]: an augmentless nominal must be the highest
    nominal in its vP). -/
theorem indiscriminate_allLicensed_iff {needs : α → Bool} {goals : List α} :
    (indiscriminate : Probe α).AllLicensed needs goals ↔
      ∀ a ∈ goals, needs a = true → goals.head? = some a :=
  forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    indiscriminate_licensed_iff

/-! ### Cascades -/

/-- The goal an ordered sequence of probes delivers: the first
    probe's finding, else the next's, and so on — `Probe.search` at
    the goal level composed with `List.findSome?` at the probe level.
    This is also the single-slot morphological competition: the first
    probe with output wins the slot ([preminger-2014] §4.4: π⁰'s
    clitic beats #⁰'s exponent beats nothing). -/
def cascade (ps : List (Probe α)) (goals : List α) : Option α :=
  ps.findSome? (·.search goals)

variable {ps : List (Probe α)}

/-- A cascade delivers nothing iff no goal is visible to any probe. -/
@[simp]
theorem cascade_eq_none_iff :
    cascade ps goals = none ↔
      ∀ q ∈ ps, ∀ a ∈ goals, q.vis a = false := by
  simp [cascade, List.findSome?_eq_none_iff]

/-- Unfold one probe of the cascade. -/
theorem cascade_cons {q : Probe α} :
    cascade (q :: ps) goals = (q.search goals <|> cascade ps goals) := by
  rw [cascade, List.findSome?_cons]
  cases q.search goals <;> rfl

@[simp] theorem cascade_nil : cascade ([] : List (Probe α)) goals = none := rfl

@[simp] theorem cascade_singleton {q : Probe α} :
    cascade [q] goals = q.search goals := by
  rw [cascade_cons, cascade_nil]
  cases q.search goals <;> rfl

/-- `cascade` is a monoid map `(List (Probe α), ++) → (Option α, <|>)`:
    the single-slot competition runs the left probes, then the right. -/
theorem cascade_append {qs : List (Probe α)} :
    cascade (ps ++ qs) goals = (cascade ps goals <|> cascade qs goals) := by
  unfold cascade
  rw [List.findSome?_append]
  cases ps.findSome? (·.search goals) <;> rfl

/-- The cascade's goal is licensed by one of its probes. -/
theorem exists_licensed_of_cascade_eq_some {a : α}
    (h : cascade ps goals = some a) :
    ∃ q ∈ ps, q.Licensed goals a :=
  List.exists_of_findSome?_eq_some h

/-- The cascade's goal is a member of the sequence. -/
theorem mem_of_cascade_eq_some {a : α}
    (h : cascade ps goals = some a) : a ∈ goals :=
  let ⟨_, _, hq⟩ := exists_licensed_of_cascade_eq_some h
  mem_of_search_eq_some hq

end Probe

end Minimalist
