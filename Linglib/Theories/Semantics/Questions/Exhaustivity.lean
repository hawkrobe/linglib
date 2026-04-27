import Linglib.Core.Question.Basic
import Linglib.Theories.Semantics.Questions.Resolution

/-!
# Exhaustivity — the weak / strong / Dayal / Xiang ladder
@cite{karttunen-1977} @cite{heim-1994} @cite{groenendijk-stokhof-1984} @cite{dayal-1996} @cite{george-2011} @cite{klinedinst-rothschild-2011} @cite{xiang-2022} @cite{fox-2018} @cite{theiler-etal-2018}

The canonical exhaustivity operators on `Core.Question W`. Different
authors over the past 50 years have proposed sibling operators that
extract "the answer to Q at the actual world w" with different strength
profiles. This file states them in one place, in mathlib-style
`Prop`+`Set` form (no `Bool`/`List` substrate).

## The ladder

Given `Q : Core.Question W` and a world `w : W`:

- **weakAnswer(Q, w)** (@cite{heim-1994}, @cite{karttunen-1977}): the
  intersection of all true alternatives at w. The natural "what σ must
  entail to count as truly answering Q."

- **strongAnswer(Q, w)** (@cite{groenendijk-stokhof-1984},
  @cite{heim-1994}): the set of worlds that agree with w on every
  alternative. Equivalent to `MentionAll` evaluated at w on partition
  questions.

- **dayalAns(Q, w)** (@cite{dayal-1996}): when defined, the unique
  strongest true alternative — the proposition `p ∈ alt Q` such that
  `w ∈ p` and `p ⊆ q` for every other true alternative `q`. Returns
  `Option (Set W)`; existence is **Dayal's Exhaustivity Presupposition**
  (`IsExhaustivelyResolvable`).

- **relExh(Q, w, M)** (@cite{xiang-2022} Def 91): exhaustivity
  relativized to a modal base `M : Set W`. The strongest true answer
  computed against the M-restricted alternatives.

- **intermediateExh** (@cite{george-2011}, @cite{klinedinst-rothschild-2011}):
  weak exhaustivity plus a no-false-positives clause. Stub.

- **foxExhaustifiedAnswer(Q, w)** (@cite{fox-2018}): the answer derived
  by applying the exhaustification operator Exh to alternatives. Stub.
-/

namespace Semantics.Questions.Exhaustivity

universe u
variable {W : Type u}

open Core.Question
open Semantics.Questions.Resolution

/-! ### Weak exhaustivity (Heim 1994 / Karttunen 1977) -/

/-- **Weak exhaustive answer**: the set of worlds that lie in every true
    alternative at w (`⋂ {p ∈ alt Q | w ∈ p}`). A state σ "weakly
    answers" Q at w iff σ ⊆ weakAnswer Q w. -/
def weakAnswer (Q : Core.Question W) (w : W) : Set W :=
  {v | ∀ p ∈ alt Q, w ∈ p → v ∈ p}

/-! ### Strong exhaustivity (Groenendijk-Stokhof 1984 / Heim 1994) -/

/-- **Strong exhaustive answer**: the set of worlds that decide every
    alternative the same way as w. -/
def strongAnswer (Q : Core.Question W) (w : W) : Set W :=
  {v | ∀ p ∈ alt Q, (w ∈ p ↔ v ∈ p)}

/-- A state σ is the **strong-exhaustive answer** at w iff σ equals
    `strongAnswer Q w`. -/
def IsStronglyExhaustiveAnswer (σ : Set W) (Q : Core.Question W) (w : W) : Prop :=
  σ = strongAnswer Q w

/-! ### Dayal's strongest-true answer (@cite{dayal-1996}) -/

/-- True alternatives at `w`: alternatives of `Q` that contain `w`. -/
def trueAlternatives (Q : Core.Question W) (w : W) : Set (Set W) :=
  {p ∈ alt Q | w ∈ p}

/-- A proposition `p` is the **strongest true answer** to `Q` at `w`
    iff `p ∈ alt Q`, `w ∈ p`, and `p ⊆ q` for every other true
    alternative `q`. (@cite{dayal-1996} Ans(Q) when defined.) -/
def IsStrongestTrueAnswer (Q : Core.Question W) (w : W) (p : Set W) : Prop :=
  p ∈ alt Q ∧ w ∈ p ∧ ∀ q ∈ alt Q, w ∈ q → p ⊆ q

/-- **Dayal's Exhaustivity Presupposition** (@cite{dayal-1996}):
    a strongest true answer exists at `w`. -/
def IsExhaustivelyResolvable (Q : Core.Question W) (w : W) : Prop :=
  ∃ p, IsStrongestTrueAnswer Q w p

/-- Dayal's answer (when EP holds): the unique strongest true
    alternative at `w`. -/
noncomputable def dayalAns (Q : Core.Question W) (w : W) : Option (Set W) :=
  open Classical in
  if h : IsExhaustivelyResolvable Q w then some (Classical.choose h) else none

/-- `dayalAns` returns `some` iff EP holds. -/
theorem dayalAns_isSome_iff_EP (Q : Core.Question W) (w : W) :
    (dayalAns Q w).isSome ↔ IsExhaustivelyResolvable Q w := by
  unfold dayalAns
  split
  · case _ h => simp [Option.isSome, h]
  · case _ h => simp [Option.isSome, h]

/-! ### Xiang's relativized exhaustivity (@cite{xiang-2022} Def 91) -/

/-- True alternatives **restricted to a modal base** `M`: alternatives
    of `Q` that contain `w` AND have non-empty intersection with `M`. -/
def trueAlternativesIn (Q : Core.Question W) (w : W) (M : Set W) : Set (Set W) :=
  {p ∈ alt Q | w ∈ p ∧ ∃ v ∈ M, v ∈ p}

/-- A proposition `p` is the **strongest true answer relative to modal
    base `M`** at `w`: `p ∈ alt Q`, `w ∈ p`, intersects `M`, and
    M-entails every other M-true alternative. -/
def IsStrongestRelTrueAnswer
    (Q : Core.Question W) (w : W) (M : Set W) (p : Set W) : Prop :=
  p ∈ alt Q ∧ w ∈ p ∧ (∃ v ∈ M, v ∈ p) ∧
  ∀ q ∈ alt Q, w ∈ q → (∃ v ∈ M, v ∈ q) → p ∩ M ⊆ q ∩ M

/-- **Xiang's relExh**: relativized exhaustivity at `w` against modal
    base `M` (@cite{xiang-2022} Def 91). -/
def relExh (Q : Core.Question W) (w : W) (M : Set W) : Prop :=
  ∃ p, IsStrongestRelTrueAnswer Q w M p

/-! ### Bridges -/

/-- A strong-exhaustive answer at `w` mention-all-answers `Q`. -/
theorem stronglyExhaustive_imp_mentionAll
    (σ : Set W) (Q : Core.Question W) (w : W)
    (h : IsStronglyExhaustiveAnswer σ Q w) :
    MentionAll σ Q := by
  intro p hp
  by_cases hw : w ∈ p
  · left
    intro v hv
    have : v ∈ strongAnswer Q w := h ▸ hv
    exact (this p hp).mp hw
  · right
    intro v hv
    have : v ∈ strongAnswer Q w := h ▸ hv
    exact (this p hp).not.mp hw

/-- The Dayal answer is by construction a strongest-true answer when it
    fires. -/
theorem dayalAns_spec (Q : Core.Question W) (w : W) (p : Set W)
    (h : dayalAns Q w = some p) :
    IsStrongestTrueAnswer Q w p := by
  unfold dayalAns at h
  split at h
  · case _ hep =>
    have heq : Classical.choose hep = p := by
      injection h
    rw [← heq]; exact Classical.choose_spec hep
  · case _ => simp at h

/-! ### Strong ⊆ Weak (the substrate exhaustivity ladder) -/

/-- The strong-exhaustive answer is contained in the weak-exhaustive
    answer: any state deciding every alternative the same way as `w`
    automatically lies inside every alternative true at `w`.
    @cite{heim-1994} §4 / @cite{george-2011} §2.6 substrate fact. -/
theorem strongAnswer_subset_weakAnswer (Q : Core.Question W) (w : W) :
    strongAnswer Q w ⊆ weakAnswer Q w := by
  intro v hv p hp hwp
  exact (hv p hp).mp hwp

/-! ### `strongAnswer` partition properties (@cite{fox-2018} §1.1)

`strongAnswer Q : W → Set W` partitions `W` into equivalence classes:
`v ∈ strongAnswer Q w` is the equivalence relation "agrees with `w`
on every alternative of `Q`". The image `Set.range (strongAnswer Q)`
is what @cite{fox-2018} eq (3) calls the **Logical Partition** of `Q`. -/

/-- Reflexivity: `w` decides every alternative the same way as itself. -/
@[simp] theorem strongAnswer_self_mem (Q : Core.Question W) (w : W) :
    w ∈ strongAnswer Q w := fun _ _ => Iff.rfl

/-- Symmetry of the underlying equivalence: `v ∈ strongAnswer Q w ↔
    w ∈ strongAnswer Q v`. -/
theorem mem_strongAnswer_symm (Q : Core.Question W) {w v : W} :
    v ∈ strongAnswer Q w ↔ w ∈ strongAnswer Q v := by
  unfold strongAnswer
  refine ⟨fun h p hp => (h p hp).symm, fun h p hp => (h p hp).symm⟩

/-- Transitivity: `u ∈ strongAnswer Q v` and `v ∈ strongAnswer Q w`
    implies `u ∈ strongAnswer Q w`. -/
theorem strongAnswer_trans (Q : Core.Question W) {w v u : W}
    (huv : u ∈ strongAnswer Q v) (hvw : v ∈ strongAnswer Q w) :
    u ∈ strongAnswer Q w := by
  intro p hp
  exact (hvw p hp).trans (huv p hp)

/-- Two strong-answer cells are either equal or disjoint — the
    equivalence-relation partition property. -/
theorem strongAnswer_eq_or_disjoint (Q : Core.Question W) (w v : W) :
    strongAnswer Q w = strongAnswer Q v ∨
      Disjoint (strongAnswer Q w) (strongAnswer Q v) := by
  by_cases h : ∃ u, u ∈ strongAnswer Q w ∧ u ∈ strongAnswer Q v
  · left
    obtain ⟨u, huw, huv⟩ := h
    ext x
    refine ⟨fun hx p hp => ?_, fun hx p hp => ?_⟩
    · -- x ∈ strongAnswer Q w; want v ∈ p ↔ x ∈ p
      have hu_w : w ∈ p ↔ u ∈ p := huw p hp
      have hu_v : v ∈ p ↔ u ∈ p := huv p hp
      have hx_w : w ∈ p ↔ x ∈ p := hx p hp
      exact hu_v.trans (hu_w.symm.trans hx_w)
    · -- x ∈ strongAnswer Q v; want w ∈ p ↔ x ∈ p
      have hu_w : w ∈ p ↔ u ∈ p := huw p hp
      have hu_v : v ∈ p ↔ u ∈ p := huv p hp
      have hx_v : v ∈ p ↔ x ∈ p := hx p hp
      exact hu_w.trans (hu_v.symm.trans hx_v)
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    ext u
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hu hu'
    exact h ⟨u, hu, hu'⟩

/-- The cells of the strong-answer partition cover `W`: every world
    is in some cell (its own). -/
@[simp] theorem iUnion_strongAnswer (Q : Core.Question W) :
    ⋃ w, strongAnswer Q w = Set.univ := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨v, strongAnswer_self_mem Q v⟩

/-- The Fox 2018 LogicalPartition characterization: any cell in
    `Set.range (strongAnswer Q)` is uniquely determined by any of its
    elements. -/
theorem mem_range_strongAnswer_iff (Q : Core.Question W) (C : Set W) :
    C ∈ Set.range (strongAnswer Q) ↔ ∃ w ∈ C, C = strongAnswer Q w := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, strongAnswer_self_mem Q w, rfl⟩
  · rintro ⟨w, _, rfl⟩
    exact ⟨w, rfl⟩

/-! ### Fox's exhaustification primitives (@cite{fox-2018})

@cite{fox-2018} derives Dayal's exhaustivity presupposition from the
demand that question denotations partition the Stalnakerian context-set
via point-wise exhaustification of Hamblin alternatives. Two
substrate-level primitives:

- `exhCell Q p` (eq 11): the set of worlds where `p` is the maximally
  informative true alternative — i.e., `{w | IsStrongestTrueAnswer Q w p}`.
- `exhaustifiedPartition Q` (eq 3): the equivalence-class image
  `Set.range (strongAnswer Q)`, the "Logical Partition" of Q.

The paper-specific apparatus (Cell Identification, Non-Vacuity, QPM)
lives in `Phenomena/Questions/Studies/Fox2018.lean`; here we expose
only the substrate primitives the paper consumes. -/

/-- @cite{fox-2018} (eq 11): the **Exh-cell** of proposition `p` in
    question `Q` — the set of worlds where `p` is the maximally
    informative true Hamblin alternative. Identifies a cell of the
    logical partition by the alt that "Exh-strengthens to it".
    Substrate identification: `{w | IsStrongestTrueAnswer Q w p}`. -/
def exhCell (Q : Core.Question W) (p : Set W) : Set W :=
  {w | IsStrongestTrueAnswer Q w p}

@[simp] theorem mem_exhCell {Q : Core.Question W} {p : Set W} {w : W} :
    w ∈ exhCell Q p ↔ IsStrongestTrueAnswer Q w p := Iff.rfl

/-- An Exh-cell membership entails the world is in the alternative. -/
theorem exhCell_subset (Q : Core.Question W) (p : Set W) :
    exhCell Q p ⊆ p :=
  fun _ h => h.2.1

/-- @cite{fox-2018} (eq 3): the **Logical Partition** of `Q` — the image
    of `strongAnswer`. Substrate-level: equivalence classes of `W` under
    "agreement on every alternative". A partition by
    `strongAnswer_eq_or_disjoint` and `iUnion_strongAnswer`. -/
def exhaustifiedPartition (Q : Core.Question W) : Set (Set W) :=
  Set.range (strongAnswer Q)

@[simp] theorem mem_exhaustifiedPartition {Q : Core.Question W} {C : Set W} :
    C ∈ exhaustifiedPartition Q ↔ ∃ w, C = strongAnswer Q w := by
  unfold exhaustifiedPartition
  simp only [Set.mem_range, eq_comm]

/-- The exhaustified partition cells are nonempty (each contains its
    representative world). -/
theorem exhaustifiedPartition_nonempty
    (Q : Core.Question W) {C : Set W} (h : C ∈ exhaustifiedPartition Q) :
    C.Nonempty := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w, strongAnswer_self_mem Q w⟩

/-- Two exhaustified-partition cells are equal or disjoint — direct
    consequence of `strongAnswer_eq_or_disjoint`. -/
theorem exhaustifiedPartition_eq_or_disjoint
    (Q : Core.Question W) {C₁ C₂ : Set W}
    (h₁ : C₁ ∈ exhaustifiedPartition Q) (h₂ : C₂ ∈ exhaustifiedPartition Q) :
    C₁ = C₂ ∨ Disjoint C₁ C₂ := by
  obtain ⟨w₁, rfl⟩ := h₁
  obtain ⟨w₂, rfl⟩ := h₂
  exact strongAnswer_eq_or_disjoint Q w₁ w₂

/-- The exhaustified partition covers `W` — every world is in its own
    cell. Direct consequence of `iUnion_strongAnswer`. -/
@[simp] theorem sUnion_exhaustifiedPartition (Q : Core.Question W) :
    ⋃₀ exhaustifiedPartition Q = Set.univ := by
  rw [exhaustifiedPartition, Set.sUnion_range]
  exact iUnion_strongAnswer Q

/-! ### Per-constructor characterizations -/

open Core.Question (mem_alt_polar_of_nontrivial alt_polar_of_nontrivial)

/-- True alternatives of `polar p` at `w`: just `{p}` if `w ∈ p`, else
    `{pᶜ}`. (For nontrivial polar.) -/
theorem trueAlternatives_polar_iff_of_nontrivial (p : Set W)
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) (w : W) (q : Set W) :
    q ∈ trueAlternatives (polar p) w ↔
      (w ∈ p ∧ q = p) ∨ (w ∉ p ∧ q = pᶜ) := by
  unfold trueAlternatives
  rw [Set.mem_sep_iff]
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact Or.inl ⟨hwq, rfl⟩
    · exact Or.inr ⟨hwq, rfl⟩
  · rintro (⟨hwp, hqp⟩ | ⟨hwp, hqpc⟩)
    · rw [hqp]
      exact ⟨(mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl), hwp⟩
    · rw [hqpc]
      exact ⟨(mem_alt_polar_of_nontrivial hne hnu pᶜ).mpr (Or.inr rfl), hwp⟩

/-- The weak (Heim/Karttunen) answer to `polar p` at a `p`-true world
    is `p` itself. (For nontrivial polar.) -/
theorem weakAnswer_polar_of_pos {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∈ p) :
    weakAnswer (polar p) w = p := by
  ext v
  unfold weakAnswer
  rw [Set.mem_setOf_eq]
  constructor
  · intro h
    rw [alt_polar_of_nontrivial hne hnu] at h
    exact h p (by simp) hwp
  · intro hv q hq hwq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact hv
    · exact (hwq hwp).elim

/-- The weak (Heim/Karttunen) answer to `polar p` at a `p`-false world
    is `pᶜ`. (For nontrivial polar.) -/
theorem weakAnswer_polar_of_neg {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∉ p) :
    weakAnswer (polar p) w = pᶜ := by
  ext v
  unfold weakAnswer
  rw [Set.mem_setOf_eq]
  constructor
  · intro h
    rw [alt_polar_of_nontrivial hne hnu] at h
    exact h pᶜ (by simp) hwp
  · intro hv q hq hwq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact (hwp hwq).elim
    · exact hv

/-- The strong (G&S) answer to `polar p` at a `p`-true world is
    `p` itself. (For nontrivial polar.) -/
theorem strongAnswer_polar_of_pos {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∈ p) :
    strongAnswer (polar p) w = p := by
  ext v
  unfold strongAnswer
  rw [Set.mem_setOf_eq]
  constructor
  · intro h
    have hp_mem : p ∈ alt (polar p) :=
      (mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl)
    exact (h p hp_mem).mp hwp
  · intro hvp q hq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact iff_of_true hwp hvp
    · simp only [Set.mem_compl_iff]
      exact iff_of_false (fun h => h hwp) (fun h => h hvp)

/-- The strong (G&S) answer to `polar p` at a `p`-false world is
    `pᶜ`. (For nontrivial polar.) -/
theorem strongAnswer_polar_of_neg {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∉ p) :
    strongAnswer (polar p) w = pᶜ := by
  ext v
  unfold strongAnswer
  rw [Set.mem_setOf_eq]
  constructor
  · intro h
    have hpc_mem : pᶜ ∈ alt (polar p) :=
      (mem_alt_polar_of_nontrivial hne hnu pᶜ).mpr (Or.inr rfl)
    exact (h pᶜ hpc_mem).mp hwp
  · intro hvpc q hq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact iff_of_false hwp hvpc
    · simp only [Set.mem_compl_iff]
      exact iff_of_true (fun h => hwp h) (fun h => hvpc h)

/-! ### `declarative` characterizations -/

/-- The weak answer to a declarative is the proposition itself.
    The single alt is `p`; if `w ∈ p` then `weakAnswer = p`. -/
theorem weakAnswer_declarative_of_pos {p : Set W}
    {w : W} (hwp : w ∈ p) :
    weakAnswer (declarative p) w = p := by
  ext v
  unfold weakAnswer
  rw [Set.mem_setOf_eq, Core.Question.alt_declarative]
  refine ⟨fun h => h p (Set.mem_singleton p) hwp, fun hvp q hq _ => ?_⟩
  rw [Set.mem_singleton_iff] at hq
  exact hq ▸ hvp

/-- The strong answer to a declarative at a `p`-true world is `p`. -/
theorem strongAnswer_declarative_of_pos {p : Set W}
    {w : W} (hwp : w ∈ p) :
    strongAnswer (declarative p) w = p := by
  ext v
  unfold strongAnswer
  rw [Set.mem_setOf_eq, Core.Question.alt_declarative]
  refine ⟨fun h => (h p (Set.mem_singleton p)).mp hwp, fun hvp q hq => ?_⟩
  rw [Set.mem_singleton_iff] at hq
  exact hq ▸ iff_of_true hwp hvp

/-! ### `dayalAns` characterizations -/

/-- For a non-trivial polar question, the **existential presupposition**
    is always satisfied: at any world, exactly one of `p`, `pᶜ` is true,
    and the singleton trivially has a maximum. -/
theorem isExhaustivelyResolvable_polar_of_nontrivial {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) (w : W) :
    IsExhaustivelyResolvable (polar p) w := by
  by_cases hwp : w ∈ p
  · refine ⟨p, ?_, hwp, ?_⟩
    · exact (mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl)
    · intro q hq hwq
      rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
      · exact Set.Subset.refl _
      · exact (hwq hwp).elim
  · refine ⟨pᶜ, ?_, hwp, ?_⟩
    · exact (mem_alt_polar_of_nontrivial hne hnu pᶜ).mpr (Or.inr rfl)
    · intro q hq hwq
      rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
      · exact (hwp hwq).elim
      · exact Set.Subset.refl _

/-- The strongest true answer to `polar p` at a `p`-true world is `p`
    itself. -/
theorem isStrongestTrueAnswer_polar_of_pos {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∈ p) :
    IsStrongestTrueAnswer (polar p) w p := by
  refine ⟨?_, hwp, ?_⟩
  · exact (mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl)
  · intro q hq hwq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact Set.Subset.refl _
    · exact (hwq hwp).elim

/-- The strongest true answer to `polar p` at a `p`-false world is
    `pᶜ`. -/
theorem isStrongestTrueAnswer_polar_of_neg {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∉ p) :
    IsStrongestTrueAnswer (polar p) w pᶜ := by
  refine ⟨?_, hwp, ?_⟩
  · exact (mem_alt_polar_of_nontrivial hne hnu pᶜ).mpr (Or.inr rfl)
  · intro q hq hwq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact (hwp hwq).elim
    · exact Set.Subset.refl _

/-! ### Decidability for polar EP

For nontrivial polar questions, `IsExhaustivelyResolvable` is **always
true** (`isExhaustivelyResolvable_polar_of_nontrivial`), so the
`Decidable` instance is `isTrue`. This is the substrate fact that
underlies @cite{dayal-1996}'s observation that polar EP is
unproblematic — the EP only becomes contentful for wh-questions. -/

instance IsExhaustivelyResolvable.decidable_polar {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) (w : W) :
    Decidable (IsExhaustivelyResolvable (polar p) w) :=
  isTrue (isExhaustivelyResolvable_polar_of_nontrivial hne hnu w)

end Semantics.Questions.Exhaustivity
