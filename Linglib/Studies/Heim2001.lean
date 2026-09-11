import Linglib.Data.Examples.Heim2001
import Linglib.Semantics.Degree.Quantifier
import Linglib.Syntax.Minimalist.Movement.HeimKennedy
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases

/-!
# Heim (2001): Degree Operators and Scope

This file formalizes [heim-2001], the question of how far a degree phrase moves at LF, put to
the max semantics of the comparative, (5) and (6): *-er than t* applies to a degree predicate
and says that its greatest degree exceeds *t*. Over a monotone adjective the degree predicate a
quantified subject yields is the set of degrees at which the quantifier holds of the entities
reaching them (`degreeSet`), so the high-DegP LF (10b) asserts that its maximum exceeds the
standard (`HighDegP`) and the low-DegP LF (10a) that the quantifier holds of the entities
exceeding the standard (`LowDegP`). Section 2.1 shows the two coincide for every monotone
increasing quantifier over individuals or worlds, (8) to (16), whenever the maxima are defined,
fn. 6: the high LF entails the low one (`lowDegP_of_highDegP`), and the converse holds on a finite
domain (`highDegP_of_lowDegP`), the shortest or tallest girl attaining the maximum. Under a
monotone decreasing operator the degree set is an upper set and has no maximum, (17) to (19), so
the high LF is a presupposition failure (`not_isGreatest_degreeSet_of_antitone`); under *exactly
two* the maximum exists but is that of *at least two*, (20)
(`isGreatest_atLeast_of_isGreatest_exactly`). Section 2.2 finds the cases where the LFs differ:
with an *exactly*-differential or *less* the high LF of a universal subject is true and the
sentence false when the shortest girl meets the standard and the others exceed it, (22) and
(24) (`exactly_high_not_low`, `less_high_not_low`), which the constraint (27), Kennedy's
generalization, excludes (`kennedy_generalization`). Section 2.3 finds intensional verbs
ambiguous, (28) to (32), except epistemic *might* and the neg-raising verbs, (33) and (34)
(`rows`); for the latter the maximum redefined as the greatest lower bound of the degrees at
which the predicate is false, (35), which agrees with (6) in the bivalent case (`isGLB_compl_Iic`),
makes the high LF equivalent to the low one, (36) (`negRaising_collapse`). Section 3.2's entry
for *-est*, (59), uses its complement twice and is the absolute superlative
(`est_iff_absoluteSuperlative`).

## Implementation notes

* A quantifier is a predicate on sets of entities, monotone increasing or decreasing; a
  quantifier over worlds is the same object over a type of worlds, which is how the intensional
  cases (15), (16), (28) to (31) fall under the theorems.
* The maximum of (6) is `IsGreatest`, so a high-DegP truth condition carries its definedness
  presupposition as an existence conjunct; the paper's undefined maxima are the negations of
  those conjuncts.
* Section 2.4's de re and de dicto than-clauses, (37) to (42), are recorded as rows; the
  diagnosis is [von-stechow-1984]'s and is formalized in `Studies/VonStechow1984.lean`.

## References

* [heim-2001]
* [von-stechow-1984]
* [heim-1999]
-/

namespace Heim2001

open Set Degree Minimalist Data.Examples

variable {Entity D : Type*} [LinearOrder D]

/-! ### The two LFs of a quantified comparative -/

/-- The degree predicate of a quantifier `Q` over a monotone adjective with measure `μ`: the
degrees `d` such that `Q` holds of the entities reaching `d`, the set of (10b) and (12b). -/
def degreeSet (Q : Set Entity → Prop) (μ : Entity → D) : Set D := {d | Q {x | d ≤ μ x}}

/-- The low-DegP LF, (10a): the quantifier holds of the entities exceeding the standard. -/
def LowDegP (Q : Set Entity → Prop) (μ : Entity → D) (t : D) : Prop := Q {x | t < μ x}

/-- The high-DegP LF, (10b): the maximum of the degree set is defined and exceeds the standard. -/
def HighDegP (Q : Set Entity → Prop) (μ : Entity → D) (t : D) : Prop :=
  ∃ m, IsGreatest (degreeSet Q μ) m ∧ t < m

/-- The degree set of a monotone increasing quantifier is a lower set. -/
theorem degreeSet_mem_of_le {Q : Set Entity → Prop} (hQ : Monotone Q) {μ : Entity → D}
    {d d' : D} (hd : d ∈ degreeSet Q μ) (h : d' ≤ d) : d' ∈ degreeSet Q μ :=
  hQ (λ _ hx => le_trans h hx) hd

/-- Section 2.1: the high LF entails the low one for every monotone increasing quantifier. -/
theorem lowDegP_of_highDegP {Q : Set Entity → Prop} (hQ : Monotone Q) {μ : Entity → D} {t : D}
    (h : HighDegP Q μ t) : LowDegP Q μ t := by
  obtain ⟨m, hm, htm⟩ := h
  exact hQ (λ _ hx => lt_of_lt_of_le htm hx) hm.1

/-- Section 2.1, fn. 6: the low LF entails the high one when the maxima are defined, as on a
finite domain, where the shortest girl of (10) and the tallest girl of (12) attain them. -/
theorem highDegP_of_lowDegP [Finite Entity] {Q : Set Entity → Prop} (hQ : Monotone Q)
    (hQ₀ : ¬ Q ∅) {μ : Entity → D} {t : D} (h : LowDegP Q μ t) : HighDegP Q μ t := by
  classical
  -- every degree in the set is bounded by a measured degree in the set
  have step : ∀ d ∈ degreeSet Q μ, ∃ x, d ≤ μ x ∧ μ x ∈ degreeSet Q μ := by
    intro d hd
    have hne : ∃ x, d ≤ μ x := by
      by_contra hno
      exact hQ₀ (by
        have hd' : Q {x | d ≤ μ x} := hd
        rwa [eq_empty_of_forall_notMem (s := {x | d ≤ μ x}) λ x hx => hno ⟨x, hx⟩] at hd')
    have : Nonempty {x // d ≤ μ x} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min (λ x : {x // d ≤ μ x} => μ x.1)
    refine ⟨x₀, hx₀, ?_⟩
    have : {x | μ x₀ ≤ μ x} = {x | d ≤ μ x} := by
      ext x
      exact ⟨λ hx => le_trans hx₀ hx, λ hx => hmin ⟨x, hx⟩⟩
    show Q {x | μ x₀ ≤ μ x}
    rw [this]
    exact hd
  -- the low LF puts the least exceeding measure into the degree set
  have hne : ∃ x, t < μ x := by
    by_contra hno
    exact hQ₀ (by
      have h' : Q {x | t < μ x} := h
      rwa [eq_empty_of_forall_notMem (s := {x | t < μ x}) λ x hx => hno ⟨x, hx⟩] at h')
  have : Nonempty {x // t < μ x} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min (λ x : {x // t < μ x} => μ x.1)
  have hd₀ : μ x₀ ∈ degreeSet Q μ := hQ (λ x hx => hmin ⟨x, hx⟩) h
  -- the greatest measured degree in the set is its maximum
  have : Nonempty {x // μ x ∈ degreeSet Q μ} := ⟨⟨x₀, hd₀⟩⟩
  obtain ⟨⟨m, hm⟩, hmax⟩ := Finite.exists_max (λ x : {x // μ x ∈ degreeSet Q μ} => μ x.1)
  refine ⟨μ m, ⟨hm, λ d hd => ?_⟩, lt_of_lt_of_le hx₀ (hmax ⟨x₀, hd₀⟩)⟩
  obtain ⟨y, hdy, hy⟩ := step d hd
  exact le_trans hdy (hmax ⟨y, hy⟩)

/-- The universal subject of (8) and the necessity operator of (15a) as quantifiers. -/
def forallOver (R : Set Entity) : Set Entity → Prop := λ S => R ⊆ S

/-- The existential subject of (11) and the possibility operator of (15b). -/
def existsOver (R : Set Entity) : Set Entity → Prop := λ S => (R ∩ S).Nonempty

theorem forallOver_monotone (R : Set Entity) : Monotone (forallOver R) :=
  λ _ _ h hR => hR.trans h

theorem existsOver_monotone (R : Set Entity) : Monotone (existsOver R) :=
  λ _ _ h ⟨x, hx⟩ => ⟨x, hx.1, h hx.2⟩

/-- (10): on a finite domain with a nonempty restrictor, the two LFs of *every girl is taller
than 4 feet* coincide. -/
theorem forall_collapse [Finite Entity] {R : Set Entity} (hR : R.Nonempty) (μ : Entity → D)
    (t : D) : LowDegP (forallOver R) μ t ↔ HighDegP (forallOver R) μ t :=
  ⟨highDegP_of_lowDegP (forallOver_monotone R) (λ h => hR.ne_empty (subset_empty_iff.1 h)),
    lowDegP_of_highDegP (forallOver_monotone R)⟩

/-- (12): likewise for *some girl*. -/
theorem exists_collapse [Finite Entity] (R : Set Entity) (μ : Entity → D) (t : D) :
    LowDegP (existsOver R) μ t ↔ HighDegP (existsOver R) μ t :=
  ⟨highDegP_of_lowDegP (existsOver_monotone R) (λ ⟨_, _, h⟩ => h),
    lowDegP_of_highDegP (existsOver_monotone R)⟩

/-! ### Monotone decreasing and non-monotone operators -/

/-- Under a monotone decreasing operator the degree set is an upper set, so on a scale without a
top it has no maximum: the high LFs (17c), (18c) and (19c) are presupposition failures. -/
theorem not_isGreatest_degreeSet_of_antitone [NoMaxOrder D] {Q : Set Entity → Prop}
    (hQ : Antitone Q) (μ : Entity → D) : ¬ ∃ m, IsGreatest (degreeSet Q μ) m := by
  rintro ⟨m, hm, hub⟩
  obtain ⟨m', hmm'⟩ := exists_gt m
  have : m' ∈ degreeSet Q μ := hQ (λ _ hx => le_trans hmm'.le hx) hm
  exact absurd (hub this) (not_le.2 hmm')

/-- Negation, (17c): the degrees to which Mary is not tall. -/
theorem negation_high_undefined [NoMaxOrder D] (μ : Entity → D) (a : Entity) :
    ¬ ∃ m, IsGreatest (degreeSet (λ S => a ∉ S) μ) m :=
  not_isGreatest_degreeSet_of_antitone (Q := λ S => a ∉ S) (λ _ _ h hT hS => hT (h hS)) μ

/-- *Exactly n* of the entities. -/
def exactly (n : ℕ) : Set Entity → Prop := λ S => S.ncard = n

/-- *At least n* of the entities. -/
def atLeast (n : ℕ) : Set Entity → Prop := λ S => n ≤ S.ncard

/-- (20): the maximal degree to which exactly two girls are tall, when defined, is the maximal
degree to which at least two girls are tall, so the high LF (20c) means *at least two*. -/
theorem isGreatest_atLeast_of_isGreatest_exactly [Finite Entity] {n : ℕ} {μ : Entity → D}
    {m : D} (h : IsGreatest (degreeSet (exactly n) μ) m) :
    IsGreatest (degreeSet (atLeast n) μ) m := by
  refine ⟨h.1.ge, λ d hd => ?_⟩
  by_contra hdm
  have hdm' : m < d := not_le.1 hdm
  have hsub : {x | d ≤ μ x} ⊆ {x | m ≤ μ x} := λ x hx => le_trans hdm'.le hx
  have hcard : {x | d ≤ μ x}.ncard ≤ {x | m ≤ μ x}.ncard := ncard_le_ncard hsub (toFinite _)
  have hm : {x | m ≤ μ x}.ncard = n := h.1
  have hd' : d ∈ degreeSet (exactly n) μ := le_antisymm (hm ▸ hcard) hd
  exact absurd (h.2 hd') hdm

/-! ### Exactly-differentials and less: the scope-sensitive cases -/

/-- (22b): every girl is exactly the standard's height. -/
def LowExactly (R : Set Entity) (μ : Entity → D) (t : D) : Prop := ∀ x ∈ R, μ x = t

/-- (22c): the maximal degree to which every girl is tall is the standard. -/
def HighExactly (R : Set Entity) (μ : Entity → D) (t : D) : Prop :=
  IsGreatest (degreeSet (forallOver R) μ) t

/-- (24b): every girl is less tall than the standard. -/
def LowLess (R : Set Entity) (μ : Entity → D) (t : D) : Prop := ∀ x ∈ R, μ x < t

/-- (24c): the maximal degree to which every girl is tall is below the standard. -/
def HighLess (R : Set Entity) (μ : Entity → D) (t : D) : Prop :=
  ∃ m, IsGreatest (degreeSet (forallOver R) μ) m ∧ m < t

/-- Two girls, one exactly the standard's height in inches and one taller. -/
private def heights : Fin 2 → ℕ
  | 0 => 49
  | 1 => 50

private theorem isGreatest_heights : IsGreatest (degreeSet (forallOver univ) heights) 49 :=
  ⟨λ x _ => by fin_cases x <;> simp [heights],
    λ d hd => by simpa [heights] using (hd (mem_univ 0) : d ≤ heights 0)⟩

/-- (22): the high LF is true and the low LF false when the shortest girl is exactly 4'1'' and
another is taller, so *every girl is exactly 1'' taller than that* is false there and (22c) is no
reading of it. -/
theorem exactly_high_not_low :
    HighExactly univ heights 49 ∧ ¬ LowExactly univ heights 49 :=
  ⟨isGreatest_heights, λ h => by have := h 1 (mem_univ _); simp [heights] at this⟩

/-- (24): the high LF of *every girl is less tall than that* says only that the shortest girl is,
and is true where the sentence is false. -/
theorem less_high_not_low : HighLess univ heights 50 ∧ ¬ LowLess univ heights 50 :=
  ⟨⟨49, isGreatest_heights, by decide⟩, λ h => absurd (h 1 (mem_univ _)) (by simp [heights])⟩

/-- Kennedy's generalization, (27): the scope of a quantificational DP that contains the trace of
a DegP contains the DegP, the Heim–Kennedy constraint of the substrate; the LF it excludes is the
one where the DP's scope contains the trace but not the DegP, (22c). -/
theorem kennedy_generalization {Node : Type*} {C : Set (Node × Node)} {q δ t : Node} :
    ¬ IsHeimKennedy C q δ t ↔ (q, t) ∈ C ∧ (q, δ) ∉ C :=
  not_isHeimKennedy_iff

/-! ### Intensional verbs -/

/-- The intensional verbs of Section 2.3: deontic and possibility verbs allow the high-DegP
reading, epistemic *might* and the neg-raising verbs do not, (33) and (34). -/
inductive IntensionalClass
  | deontic
  | possibility
  | epistemic
  | negRaising
  deriving DecidableEq, Repr

/-- A row of Section 2.3: the verb, its class, and whether the high-DegP reading is attested. -/
structure Row where
  verb : String
  cls : IntensionalClass
  highDegP : Bool

/-- The class named in a row's features. -/
def IntensionalClass.parse : String → Option IntensionalClass
  | "deontic" => some .deontic
  | "possibility" => some .possibility
  | "epistemic" => some .epistemic
  | "negRaising" => some .negRaising
  | _ => none

/-- The Section 2.3 row of an example, if it classifies its verb. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let verb ← e.feature? "verb"
  let cls ← (e.feature? "class").bind IntensionalClass.parse
  let hd ← e.feature? "highDegP"
  some ⟨verb, cls, hd = "yes"⟩

/-- The verbs of (28) to (34). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The maximum of (35): the greatest lower bound of the degrees at which the predicate is false.
In the bivalent case, on a dense scale, it is the maximum of (6): the greatest element of a
principal lower set is the greatest lower bound of its complement. -/
theorem isGLB_compl_Iic [DenselyOrdered D] (m : D) : IsGLB (Iic m)ᶜ m := by
  rw [compl_Iic]
  exact isGLB_Ioi

/-- (36): the desires determinate outside a middle zone, *I want the paper to be d-long* is
false exactly above every desired length, so the high LF, that the greatest lower bound of those
lengths, the maximal tolerated length, is below the standard, is equivalent to the low LF, that
every desired length is. -/
theorem negRaising_collapse {W : Type*} [Finite W] [Nonempty W] [DenselyOrdered D] (ℓ : W → D)
    (t : D) : (∀ w, ℓ w < t) ↔ ∃ m, IsGLB {d | ∀ w, ℓ w < d} m ∧ m < t := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max ℓ
  have hset : {d | ∀ w, ℓ w < d} = Ioi (ℓ w₀) := by
    ext d
    exact ⟨λ h => h w₀, λ h w => lt_of_le_of_lt (hw₀ w) h⟩
  rw [hset]
  constructor
  · intro h
    exact ⟨ℓ w₀, isGLB_Ioi, h w₀⟩
  · rintro ⟨m, hm, hmt⟩ w
    rw [hm.unique isGLB_Ioi] at hmt
    exact lt_of_le_of_lt (hw₀ w) hmt

/-! ### The superlative -/

/-- (59a): *-est* uses its complement twice, once for the subject and once for the others; over a
monotone adjective and a comparison class with someone else in it, it is the absolute
superlative. -/
theorem est_iff_absoluteSuperlative [Finite Entity] (μ : Entity → D) (C : Set Entity) (x : Entity)
    (hx : x ∈ C) (hC : ∃ y ∈ C, y ≠ x) :
    (∃ m, IsGreatest {d | ∃ y ∈ C, y ≠ x ∧ d ≤ μ y} m ∧ m < μ x) ↔ absoluteSuperlative μ C x := by
  classical
  have : Nonempty {y // y ∈ C ∧ y ≠ x} := let ⟨y, hy, hyx⟩ := hC; ⟨⟨y, hy, hyx⟩⟩
  obtain ⟨⟨y₀, hy₀⟩, hmax⟩ := Finite.exists_max (λ y : {y // y ∈ C ∧ y ≠ x} => μ y.1)
  have hset : IsGreatest {d | ∃ y ∈ C, y ≠ x ∧ d ≤ μ y} (μ y₀) :=
    ⟨⟨y₀, hy₀.1, hy₀.2, le_rfl⟩, λ d ⟨y, hy, hyx, hd⟩ => le_trans hd (hmax ⟨y, hy, hyx⟩)⟩
  constructor
  · rintro ⟨m, hm, hmx⟩
    rw [hm.unique hset] at hmx
    exact ⟨hx, λ y hy hyx => lt_of_le_of_lt (hmax ⟨y, hy, hyx⟩) hmx⟩
  · intro h
    exact ⟨μ y₀, hset, h.2 y₀ hy₀.1 hy₀.2⟩

end Heim2001
