import Linglib.Core.Logic.Trivalent
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Aggregation of `Trivalent` Lists by Projection Type
[barwise-cooper-1981]

Universal vs existential aggregation as the `⊓`/`⊔` projections of the
∃ ⊣ Δ ⊣ ∀ adjunction, parameterized by `ProjectionType` (declared in
`Trivalent.lean`).

## § 1. Trivalent Aggregation

- `aggregate (d : ProjectionType) : List Trivalent → Trivalent` — fold by
  projection type. Conjunctive: `⊓`-fold from `⊤`. Disjunctive: `⊔`-fold
  from `⊥`.

## § 2. Prop-valued Quantifier Projection

The `Prop`-valued counterparts of `existsAny`/`forallAll` are just `∃`/`∀`
from Lean core. De Morgan duality uses `not_forall`/`not_exists` from
Mathlib.
-/

namespace Trivalent

/-- Aggregate a list according to projection type.
    Conjunctive (∀-like): `⊓`-fold from `⊤`.
    Disjunctive (∃-like): `⊔`-fold from `⊥`. -/
def aggregate (d : ProjectionType) (l : List Trivalent) : Trivalent :=
  match d with
  | .disjunctive => l.foldl (· ⊔ ·) ⊥
  | .conjunctive => l.foldl (· ⊓ ·) ⊤

/-- Existential (disjunctive) aggregation: true if ANY true. -/
def existsAny (l : List Trivalent) : Trivalent := aggregate .disjunctive l

/-- Universal (conjunctive) aggregation: true only if ALL true. -/
def forallAll (l : List Trivalent) : Trivalent := aggregate .conjunctive l

theorem foldl_sup_of_true (l : List Trivalent) : l.foldl (· ⊔ ·) Trivalent.true = .true := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, Trivalent.true_sup, ih]

theorem foldl_inf_of_false (l : List Trivalent) : l.foldl (· ⊓ ·) Trivalent.false = .false := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, Trivalent.false_inf, ih]

theorem foldl_sup_mem_true (l : List Trivalent) (acc : Trivalent) (h : Trivalent.true ∈ l) :
    l.foldl (· ⊔ ·) acc = .true := by
  induction l generalizing acc with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq =>
      subst heq
      simp only [Trivalent.sup_true, foldl_sup_of_true]
    | inr hmem =>
      exact ih (acc ⊔ hd) hmem

theorem foldl_inf_mem_false (l : List Trivalent) (acc : Trivalent) (h : Trivalent.false ∈ l) :
    l.foldl (· ⊓ ·) acc = .false := by
  induction l generalizing acc with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq =>
      subst heq
      simp only [Trivalent.inf_false, foldl_inf_of_false]
    | inr hmem =>
      exact ih (acc ⊓ hd) hmem

theorem existential_robust (l : List Trivalent) (h : l.any (· == .true)) :
    existsAny l = .true := by
  simp only [existsAny, aggregate, List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_eq⟩ := h
  cases x with
  | true => exact foldl_sup_mem_true l ⊥ hx_mem
  | false => exact absurd hx_eq (by decide)
  | indet => exact absurd hx_eq (by decide)

theorem universal_fragile (l : List Trivalent) (h : l.any (· == .false)) :
    forallAll l = .false := by
  simp only [forallAll, aggregate, List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_eq⟩ := h
  cases x with
  | false => exact foldl_inf_mem_false l ⊤ hx_mem
  | true => exact absurd hx_eq (by decide)
  | indet => exact absurd hx_eq (by decide)

def const {α : Type*} (t : Trivalent) : α → Trivalent := λ _ => t

def exists' {α : Type*} (P : α → Trivalent) (l : List α) : Trivalent :=
  existsAny (l.map P)

def forall' {α : Type*} (P : α → Trivalent) (l : List α) : Trivalent :=
  forallAll (l.map P)

-- ════════════════════════════════════════════════════
-- § 1.5  Aggregation Pushforward through Trivalent.ofBool
-- ════════════════════════════════════════════════════

/-! The aggregation operators defined in § 1 are `List.foldl` over the
    `Trivalent` lattice. Their behavior is determined by two algebraic
    facts:

    1. **Idempotency** (`sup_idem`, `inf_idem`): every element of a
       lattice is a fixed point of `⊔` and `⊓`. With initial accumulator
       `⊥` (resp. `⊤`), folding `⊔` (resp. `⊓`) over `List.replicate n
       .indet` gets absorbed by `.indet` after the first step (identity
       element transition).

    2. **Lattice homomorphism** (`Trivalent.ofBoolHom`): `ofBool` embeds
       `Bool` into the `{⊥, ⊤}` sublattice of `Trivalent`, preserving both
       `⊔` and `⊓`. Folding lattice operations over `bs.map ofBool`
       reduces to folding the corresponding Boolean operations
       (`||`/`&&`) over `bs` — which is always definite, so the
       aggregation result avoids `.indet`.

    These two facts are the algebraic basis for the architectural
    distinction in trivalent semantics for quantified counterfactuals
    ([ramotowska-marty-romoli-santorio-2025]) and deontic modality
    ([agha-jeretic-2022] §4.2): inputs containing `.indet`
    propagate it through aggregation regardless of duality type, while
    inputs lifted from `Bool` always commit to a definite truth value. -/

private theorem foldl_idem_const {α : Type*} (f : α → α → α) (a : α)
    (h : f a a = a) (n : Nat) :
    (List.replicate n a).foldl f a = a := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.foldl_cons, h, ih]

/-- Aggregation over `List.replicate n .indet` collapses to `.indet`
    regardless of duality type. The duality type is invisible: this is
    the algebraic reason "local-scope" trivalent semantics erases
    quantifier strength. -/
theorem aggregate_replicate_indet (d : ProjectionType) (n : Nat) (hn : n > 0) :
    aggregate d (List.replicate n Trivalent.indet) = .indet := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [aggregate, List.replicate_succ, List.foldl_cons]
    cases d with
    | conjunctive =>
      -- ⊤ ⊓ .indet = .indet, then inf_idem
      change (List.replicate k Trivalent.indet).foldl (· ⊓ ·) Trivalent.indet = Trivalent.indet
      exact foldl_idem_const (· ⊓ ·) Trivalent.indet (inf_idem _) k
    | disjunctive =>
      -- ⊥ ⊔ .indet = .indet, then sup_idem
      change (List.replicate k Trivalent.indet).foldl (· ⊔ ·) Trivalent.indet = Trivalent.indet
      exact foldl_idem_const (· ⊔ ·) Trivalent.indet (sup_idem _) k

/-- Sup-fold with `Trivalent.ofBool` accumulator commutes with `||`-fold
    via the lattice-homomorphism property of `ofBool`. -/
private theorem foldl_sup_ofBool_acc (bs : List Bool) (acc : Bool) :
    (bs.map Trivalent.ofBool).foldl (· ⊔ ·) (Trivalent.ofBool acc) =
    Trivalent.ofBool (bs.foldl (· || ·) acc) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons, Trivalent.ofBool_sup]
    exact ih (acc || b)

/-- Inf-fold with `Trivalent.ofBool` accumulator commutes with `&&`-fold. -/
private theorem foldl_inf_ofBool_acc (bs : List Bool) (acc : Bool) :
    (bs.map Trivalent.ofBool).foldl (· ⊓ ·) (Trivalent.ofBool acc) =
    Trivalent.ofBool (bs.foldl (· && ·) acc) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons, Trivalent.ofBool_inf]
    exact ih (acc && b)

/-- `List.foldl (· || ·) false = List.any id`. -/
private theorem foldl_or_false_eq_any (bs : List Bool) :
    bs.foldl (· || ·) Bool.false = bs.any id := by
  suffices ∀ acc, bs.foldl (· || ·) acc = (acc || bs.any id) from by
    simp only [this Bool.false, Bool.false_or]
  intro acc
  induction bs generalizing acc with
  | nil => simp only [List.foldl_nil, List.any_nil, Bool.or_false]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.any_cons, id, ih (acc || b), Bool.or_assoc]

/-- `List.foldl (· && ·) true = List.all id`. -/
private theorem foldl_and_true_eq_all (bs : List Bool) :
    bs.foldl (· && ·) Bool.true = bs.all id := by
  suffices ∀ acc, bs.foldl (· && ·) acc = (acc && bs.all id) from by
    simp only [this Bool.true, Bool.true_and]
  intro acc
  induction bs generalizing acc with
  | nil => simp only [List.foldl_nil, List.all_nil, Bool.and_true]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.all_cons, id, ih (acc && b), Bool.and_assoc]

/-- Existential aggregation through `Trivalent.ofBool` reduces to Boolean
    disjunction. Witness of the lattice-homomorphism property of
    `Trivalent.ofBoolHom` propagating through fold. -/
theorem aggregate_existential_map_ofBool (bs : List Bool) :
    aggregate .disjunctive (bs.map Trivalent.ofBool) = Trivalent.ofBool (bs.any id) := by
  show (bs.map Trivalent.ofBool).foldl (· ⊔ ·) ⊥ = Trivalent.ofBool (bs.any id)
  have h : (⊥ : Trivalent) = Trivalent.ofBool Bool.false := rfl
  rw [h, foldl_sup_ofBool_acc, foldl_or_false_eq_any]

/-- Universal aggregation through `Trivalent.ofBool` reduces to Boolean
    conjunction. -/
theorem aggregate_universal_map_ofBool (bs : List Bool) :
    aggregate .conjunctive (bs.map Trivalent.ofBool) = Trivalent.ofBool (bs.all id) := by
  show (bs.map Trivalent.ofBool).foldl (· ⊓ ·) ⊤ = Trivalent.ofBool (bs.all id)
  have h : (⊤ : Trivalent) = Trivalent.ofBool Bool.true := rfl
  rw [h, foldl_inf_ofBool_acc, foldl_and_true_eq_all]

/-- Aggregation through `Trivalent.ofBool` never produces `.indet` —
    Boolean inputs leave the gap-free sublattice `{⊥, ⊤}` invariant.
    The algebraic basis for "global-scope" trivalent semantics where
    the quantifier sees only Boolean values. -/
theorem aggregate_map_ofBool_ne_indet (d : ProjectionType) (bs : List Bool) :
    aggregate d (bs.map Trivalent.ofBool) ≠ .indet := by
  cases d with
  | disjunctive =>
    rw [aggregate_existential_map_ofBool]
    cases bs.any id <;> exact Trivalent.noConfusion
  | conjunctive =>
    rw [aggregate_universal_map_ofBool]
    cases bs.all id <;> exact Trivalent.noConfusion

/-- Mixed Boolean inputs (some true, some false) split the duality
    types: existential aggregation gives `.true`, universal gives
    `.false`. This IS the strength effect — algebraic reason
    selectional-architecture trivalent semantics predicts the
    quantifier-strength contrast on mixed scenarios. -/
theorem aggregate_map_ofBool_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    aggregate .disjunctive (bs.map Trivalent.ofBool) = .true ∧
    aggregate .conjunctive   (bs.map Trivalent.ofBool) = .false := by
  refine ⟨?_, ?_⟩
  · rw [aggregate_existential_map_ofBool, show bs.any id = Bool.true from h_some_true]; rfl
  · rw [aggregate_universal_map_ofBool]
    have h_not_all : bs.all id = Bool.false := by
      rw [Bool.eq_false_iff]
      intro h_all
      obtain ⟨x, hx_mem, hx_eq⟩ := List.any_eq_true.mp h_some_false
      have := List.all_eq_true.mp h_all x hx_mem
      cases x <;> simp_all [id]
    rw [h_not_all]; rfl

-- ════════════════════════════════════════════════════
-- § 1.6  Trivalent Classifier (`dist`): super-truth specialized
-- ════════════════════════════════════════════════════

/-! The `dist` operator is **finite-domain Boolean supervaluation**:
    given a Finset `s` and a Boolean predicate `P`, classify `(s, P)` as
    super-true (`P` holds at every element), super-false (`P` fails at
    every element of nonempty `s`), or indeterminate (mixed). This is the
    construction introduced by [van-fraassen-1966] (Definition 10,
    p. 487) for free logic with non-denoting names and named "super-truth"
    by [fine-1975] (§3, p. 273) when applied to vagueness via
    specification spaces.

    In linguistic semantics the same operation is [schwarzschild-1996]'s
    **DIST** operator for distributive plural predication (the source of
    the name `dist`); [kriz-2016] and [kriz-spector-2021]
    formalize the modern trivalent-homogeneity treatment.

    Reachable cases on a Finset `s : Finset α` and predicate `P : α → Prop`
    with `[DecidablePred P]`:
    | `∀ a ∈ s, P a` | `∃ a ∈ s, P a` | meaning              | `dist s P` |
    |----------------|----------------|----------------------|------------|
    | `true`         | `true`         | nonempty, all P      | `.true`    |
    | `true`         | `false`        | empty (vacuous)      | `.true`    |
    | `false`        | `true`         | mixed                | `.indet`   |
    | `false`        | `false`        | nonempty, no P       | `.false`   |
-/

/-- **Trivalent classifier (Fine super-truth, finite-Boolean specialization).**
    `dist s P` is `.true` if `P` holds at every element of `s` (vacuously
    on `∅`), `.false` if `P` fails at every element of nonempty `s`,
    `.indet` (mixed) otherwise. The supervaluation's universal/existential
    decision pair `(∀, ∃)` is the kernel; the if-chain classifies it into
    `Trivalent`. -/
def dist {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] : Trivalent :=
  if ∀ a ∈ s, P a then .true
  else if ∃ a ∈ s, P a then .indet
  else .false

/-- List variant of `dist` — direct definition over `∀`/`∃` on a List,
    no `[DecidableEq α]` required. Same trichotomy: `.true` on (vacuously
    or genuinely) all-`P`, `.false` on nonempty-but-no-`P`, `.indet` mixed.
    Agrees with `dist l.toFinset P` when `[DecidableEq α]` is available. -/
def distList {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] : Trivalent :=
  if ∀ a ∈ l, P a then .true
  else if ∃ a ∈ l, P a then .indet
  else .false

/-- `dist s P = .true` iff every element of `s` satisfies `P`. -/
theorem dist_eq_true_iff {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    dist s P = .true ↔ ∀ a ∈ s, P a := by
  unfold dist
  by_cases h : ∀ a ∈ s, P a
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · refine ⟨fun habs => ?_, fun habs => absurd habs h⟩
    rw [if_neg h] at habs
    split_ifs at habs

/-- `dist s P = .false` iff `s` is nonempty and no element satisfies `P`. -/
theorem dist_eq_false_iff {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    dist s P = .false ↔ s.Nonempty ∧ ∀ a ∈ s, ¬ P a := by
  unfold dist
  by_cases h1 : ∀ a ∈ s, P a
  · rw [if_pos h1]
    refine ⟨fun habs => ?_, ?_⟩
    · cases habs
    · rintro ⟨⟨a, ha⟩, hno⟩; exact (hno a ha (h1 a ha)).elim
  · rw [if_neg h1]
    by_cases h2 : ∃ a ∈ s, P a
    · rw [if_pos h2]
      refine ⟨fun habs => ?_, ?_⟩
      · cases habs
      · rintro ⟨_, hno⟩
        obtain ⟨a, ha, hPa⟩ := h2
        exact (hno a ha hPa).elim
    · rw [if_neg h2]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      refine ⟨?_, ?_⟩
      · -- s.Nonempty
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        apply h1
        intro a ha; rw [hne] at ha
        exact Finset.notMem_empty a ha |>.elim
      · -- ∀ a ∈ s, ¬ P a
        intro a ha hPa
        exact h2 ⟨a, ha, hPa⟩

/-- `dist s P = .indet` iff some elements of `s` satisfy `P` and some don't. -/
theorem dist_eq_indet_iff {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    dist s P = .indet ↔ (∃ a ∈ s, P a) ∧ (∃ a ∈ s, ¬ P a) := by
  unfold dist
  by_cases h1 : ∀ a ∈ s, P a
  · rw [if_pos h1]
    refine ⟨fun habs => ?_, ?_⟩
    · cases habs
    · rintro ⟨_, ⟨a, ha, hnP⟩⟩; exact (hnP (h1 a ha)).elim
  · rw [if_neg h1]
    by_cases h2 : ∃ a ∈ s, P a
    · rw [if_pos h2]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      refine ⟨h2, ?_⟩
      push Not at h1
      exact h1
    · rw [if_neg h2]
      refine ⟨fun habs => ?_, ?_⟩
      · cases habs
      · rintro ⟨⟨a, ha, hPa⟩, _⟩
        exact (h2 ⟨a, ha, hPa⟩).elim

/-- `dist` is `.true` on the empty Finset (vacuous super-truth). -/
@[simp] theorem dist_empty {α : Type*} (P : α → Prop) [DecidablePred P] :
    dist (∅ : Finset α) P = .true := by simp [dist]

/-- `dist` on a singleton: `.true` if `P a` holds, `.false` otherwise. -/
@[simp] theorem dist_singleton {α : Type*} [DecidableEq α] (a : α)
    (P : α → Prop) [DecidablePred P] :
    dist ({a} : Finset α) P = if P a then .true else .false := by
  simp only [dist, Finset.mem_singleton, forall_eq, exists_eq_left]
  by_cases h : P a
  · simp [h]
  · simp [h]

/-- `dist` is `.true` on the constantly-true predicate. -/
@[simp] theorem dist_const_true {α : Type*} (s : Finset α) :
    dist s (fun _ => True) = .true := by
  simp [dist]

/-- `distList` is `.true` on the empty list (vacuous super-truth). -/
@[simp] theorem distList_nil {α : Type*} (P : α → Prop) [DecidablePred P] :
    distList ([] : List α) P = .true := by simp [distList]

/-- `distList` on a singleton: `.true` if `P a` holds, `.false` otherwise. -/
@[simp] theorem distList_singleton {α : Type*} (a : α)
    (P : α → Prop) [DecidablePred P] :
    distList [a] P = if P a then .true else .false := by
  simp only [distList, List.mem_singleton, forall_eq, exists_eq_left]
  by_cases h : P a
  · simp [h]
  · simp [h]

/-- `distList` is `.true` on the constantly-true predicate. -/
@[simp] theorem distList_const_true {α : Type*} (l : List α) :
    distList l (fun _ => True) = .true := by
  simp [distList]

-- ════════════════════════════════════════════════════
-- § 2. Prop-valued Quantifier Projection
-- ════════════════════════════════════════════════════

/-! The `Trivalent` aggregation above (§ 1) is the decidable/three-valued
    version of quantifier projection. The classical `Prop`-valued
    counterparts are just `∃` and `∀` from Lean core — the left and
    right adjoints to the diagonal in the adjunction ∃ ⊣ Δ ⊣ ∀.

    Many parameterized semantic theories (comparison classes, precisifications,
    accessible worlds, variable assignments) project out a hidden index
    via one of these two operations:

    | Theory                 | Index I              | ∃-projection       | ∀-projection    | Mathlib hook                           |
    |------------------------|----------------------|--------------------|-----------------|----------------------------------------|
    | [klein-1980]      | comparison class C   | comparative (more) | at-least-as     | `measureDelineation_mono_in_class`     |
    | [fine-1975]       | precisification      | sub-truth          | super-truth     | `Preorder SpecSpace`, stability        |
    | [caie-2023]       | comp. context        | disjunctive update | —               | `disjunctiveUpdate_mono_interp`        |
    | [kratzer-1981]    | accessible world     | ◇ (possibility)    | □ (necessity)   | `GaloisConnection` (Proposition.lean)  |
    | [kamp-1975]       | completion           | strict comparative | at-least-as     | `Antitone` in S (via `kampPreorder`)   |

    The projections themselves are just `∃`/`∀`. De Morgan duality uses
    `not_forall` / `not_exists` from Lean core. The deeper Mathlib
    connections are on the **parameter spaces**: `Monotone`/`Antitone`
    for how the projections vary as the parameter space changes,
    `IsLeast`/`IsGreatest` for monotone collapse, and `GaloisConnection`
    for the extension/intension adjunction.

    See `Studies/Caie2023.lean` § 0 for the shared framework (monotone
    collapse via `IsLeast`/`IsGreatest` + `Antitone`, borderline region
    characterization, sequential update with pruning).
-/

end Trivalent
