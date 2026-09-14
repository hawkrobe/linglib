import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Semantics.Quantification.Numerals.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Solt & Waldon (2019): Numerals under Negation

This file formalizes the felicity constraint on numerical assertions of [solt-waldon-2019].
A bare numeral in the scope of negation, *she doesn't have 40 sheep*, is infelicitous as an
answer to *how many sheep does Lisa have?* yet acceptable once the value is under
discussion, as the denial after *does Lisa have 40 sheep?*; negated *more than 40* is
acceptable in both contexts, negated *between 40 and 50* in neither. The paper's account
takes the question under discussion to be a partition ([groenendijk-stokhof-1984],
[roberts-1996]). A how-many question partitions the worlds by a count, so the number line
orders its cells, and the constraint requires the content of an assertion containing a
numerical expression to be the union of a convex set of cells, convexity in the sense of
[gardenfors-2004] carried from lexical meanings to discourse. On the exact reading of the
numeral ([kennedy-2015]), *not 40* is the union of every cell but one, a disjoint region;
*40*, *between 40 and 50*, *more than 40* and *not more than 40* are convex. A polar
question has two cells, whose every subset is convex, so the denial is felicitous. At the
top of a bounded scale the negated endpoint is convex, which is why *not 100% certain* is
acceptable where *not 95% certain* is not.

`Felicitous f φ` states the constraint for a question that sorts the worlds by an ordered
value `f`, the how-many question by the count and the polar question by the indicator; a
felicitous assertion is one the question decides (`Felicitous.decides`), and for a polar
question the converse holds (`felicitous_of_polar`). `not_felicitous_compl` is the general
form of the infelicity: negating a bounded range leaves a disjoint region whenever the
count reaches below, into, and above it. The lower-bounded reading of the numeral would
negate to a convex region (`felicitous_not_atLeast`), but the paper argues it is unavailable
in comment position, where a numeral answers the exact value the question asks for.

## Implementation notes

The corpus study and the two acceptability experiments are reported in prose. The corpus
finds negated bare numerals in denials of assertions, in contexts where the value was
mentioned or implied, and in negations of a minimum significant value with the
lower-bounded reading. Experiment 1 finds negated bare numerals rated between licensed and
unlicensed polarity items, far better when the value was mentioned or implied than when it
was not inferable, and better than *about n* throughout. Experiment 2 finds bare numerals
under negation quite unacceptable as answers to a how-many question and almost fully
restored by prior mention, unlike *any* and *some*, whose unlicensed uses prior mention
does not improve, and unlike the positive polarity items *about n* and *at least n*, which
prior mention improves less; *more than n* is acceptable under negation in both contexts,
*between m and n* in neither. Modified numerals other than *between* are polarity-sensitive
for reasons beyond convexity, which the paper leaves open.

## References

* [solt-waldon-2019]
* [groenendijk-stokhof-1984]
* [roberts-1996]
* [gardenfors-2004]
* [kennedy-2015]
-/

namespace SoltWaldon2019

open Set Numerals

variable {W ι : Type*} [Preorder ι]

/-! ### The felicity constraint -/

/-- The felicity constraint on numerical assertions, relative to the question that sorts
the worlds by the ordered value `f`: the content is the union of a convex set of cells. -/
def Felicitous (f : W → ι) (φ : Set W) : Prop :=
  ∃ I : Set ι, I.OrdConnected ∧ φ = f ⁻¹' I

/-- A felicitous assertion is a union of cells: the question decides it. -/
theorem Felicitous.decides {f : W → ι} {φ : Set W} (h : Felicitous f φ) :
    (Setoid.ker f).Decides φ := by
  obtain ⟨I, -, rfl⟩ := h
  exact Setoid.decides_iff.2 λ w v hwv => by simp [Setoid.ker_def.1 hwv]

/-- Every subset of a two-cell question is convex. -/
theorem ordConnected_prop (I : Set Prop) : I.OrdConnected := by
  refine ⟨λ x hx y hy z ⟨hxz, hzy⟩ => ?_⟩
  by_cases hz : z
  · exact (propext ⟨λ _ => hzy hz, λ _ => hz⟩ : z = y) ▸ hy
  · exact (propext ⟨λ h => absurd h hz, λ h => absurd (hxz h) hz⟩ : z = x) ▸ hx

/-- Under a polar question every decided proposition is felicitous, the denial *no, she
doesn't have 40 sheep* among them. -/
theorem felicitous_of_polar {p φ : Set W} (h : (Setoid.polar p).Decides φ) :
    Felicitous (· ∈ p) φ := by
  refine ⟨(· ∈ p) '' φ, ordConnected_prop _, ?_⟩
  ext w
  constructor
  · exact λ hw => ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, hvw⟩
    exact (Setoid.decides_iff.1 h v w (Setoid.polar_iff.2 (eq_iff_iff.1 hvw))).1 hv

/-! ### The how-many question -/

variable (count : W → ℕ)

/-- The assertion that the count satisfies a numerical meaning: the union of the how-many
question's cells over the values satisfying it. -/
def assert (r : ℕ → Prop) : Set W := count ⁻¹' {n | r n}

theorem compl_assert (r : ℕ → Prop) : (assert count r)ᶜ = assert count (λ n => ¬ r n) := rfl

/-- A numerical meaning that is a convex set of values makes a felicitous assertion. -/
theorem felicitous_of_ordConnected {r : ℕ → Prop} (h : OrdConnected {n | r n}) :
    Felicitous count (assert count r) :=
  ⟨_, h, rfl⟩

/-- *She has 40 sheep* on the exact reading: a single cell. -/
theorem felicitous_bare (m : ℕ) : Felicitous count (assert count (bareMeaning m)) :=
  felicitous_of_ordConnected count
    (by simp only [bareMeaning_def, ofPred_eq_eq_singleton]; exact ordConnected_singleton)

/-- *She has between 40 and 50 sheep*. -/
theorem felicitous_between (m k : ℕ) : Felicitous count (assert count (· ∈ Icc m k)) :=
  felicitous_of_ordConnected count (by show OrdConnected (Icc m k); exact inferInstance)

/-- *She has more than 40 sheep*. -/
theorem felicitous_moreThan (m : ℕ) : Felicitous count (assert count (moreThanMeaning m)) :=
  felicitous_of_ordConnected count
    (by simp only [moreThanMeaning_def]; exact (inferInstance : OrdConnected (Ioi m)))

/-- *She doesn't have more than 40 sheep*: the negation of a lower-bounded meaning is
convex, so it answers the how-many question. -/
theorem felicitous_not_moreThan (m : ℕ) :
    Felicitous count (assert count (λ n => ¬ moreThanMeaning m n)) :=
  felicitous_of_ordConnected count
    (by simp only [moreThanMeaning_def, not_lt]; exact (inferInstance : OrdConnected (Iic m)))

/-- The negation of the lower-bounded reading is convex too; the paper takes that reading
to be unavailable where the numeral answers a how-many question. -/
theorem felicitous_not_atLeast (m : ℕ) :
    Felicitous count (assert count (λ n => ¬ atLeastMeaning m n)) :=
  felicitous_of_ordConnected count
    (by simp only [atLeastMeaning_def, not_le]; exact (inferInstance : OrdConnected (Iio m)))

/-- Negating a bounded range leaves a disjoint region: with worlds whose counts lie below,
inside, and above the range, the negated assertion is not the union of a convex set of
cells. -/
theorem not_felicitous_compl {r : ℕ → Prop} {a b c : W} (ha : ¬ r (count a)) (hb : r (count b))
    (hc : ¬ r (count c)) (hab : count a ≤ count b) (hbc : count b ≤ count c) :
    ¬ Felicitous count (assert count (λ n => ¬ r n)) := by
  rintro ⟨I, hI, hφ⟩
  have mem : ∀ w, w ∈ assert count (λ n => ¬ r n) ↔ count w ∈ I := λ w => by rw [hφ]; rfl
  exact (mem b).2 (hI.out ((mem a).1 ha) ((mem c).1 hc) ⟨hab, hbc⟩) hb

/-- *She doesn't have 40 sheep* on the exact reading, as an answer to the how-many
question: infelicitous whenever the count can fall below, at, and above 40. -/
theorem not_felicitous_not_bare {m : ℕ} {a b c : W} (ha : count a < m) (hb : count b = m)
    (hc : m < count c) :
    ¬ Felicitous count (assert count (λ n => ¬ bareMeaning m n)) :=
  not_felicitous_compl count (r := bareMeaning m) (a := a) (b := b) (c := c) (by simp; omega)
    (by simp [hb]) (by simp; omega) (by omega) (by omega)

/-- *She doesn't have between 40 and 50 sheep*: infelicitous for the same reason. -/
theorem not_felicitous_not_between {m k : ℕ} {a b c : W} (ha : count a < m)
    (hb : count b ∈ Icc m k) (hc : k < count c) :
    ¬ Felicitous count (assert count (λ n => n ∉ Icc m k)) :=
  not_felicitous_compl count (r := (· ∈ Icc m k)) (a := a) (b := b) (c := c) (by simp; omega)
    (by simpa using hb) (by simp; omega) (by rw [mem_Icc] at hb; omega)
    (by rw [mem_Icc] at hb; omega)

/-- At the top of a bounded scale the negated endpoint is convex, the region below it:
*it's not 100% certain* answers *how likely is it?* where *it's not 95% certain* does not. -/
theorem felicitous_not_bare_of_max {m : ℕ} (hmax : ∀ w, count w ≤ m) :
    Felicitous count (assert count (λ n => ¬ bareMeaning m n)) := by
  refine ⟨Iio m, inferInstance, ?_⟩
  ext w
  have := hmax w
  simp only [assert, mem_preimage, mem_ofPred_eq, bareMeaning_def, mem_Iio]
  omega

/-- The rescue by context: once the question is whether Lisa has exactly 40 sheep, the
negative answer is a cell of the question and so felicitous. -/
theorem felicitous_denial (m : ℕ) :
    Felicitous (· ∈ assert count (bareMeaning m)) (assert count (bareMeaning m))ᶜ :=
  felicitous_of_polar Setoid.polar_decides.compl

end SoltWaldon2019
