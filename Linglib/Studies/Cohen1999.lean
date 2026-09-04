import Linglib.Semantics.Quantification.Counting

/-!
# Cohen (1999): Think Generic!

Cohen's inductivist semantics makes a generic sentence a probability judgment: gen(ψ, φ) is
true iff the conditional probability of the scope, given the restrictor and the disjunction
of a set of alternatives to the scope, exceeds one half (definition 1, p. 37). "Mammals
bear live young" is evaluated over the mammals that procreate in some way, so no majority
among all mammals is required, and Thomason's "People have a hard time finding CMU" is
evaluated over the people who sought it. Generics are further ambiguous between this
absolute reading and a relative one whose threshold is the average probability of the scope
over the alternatives; the relative reading verifies "Bulgarians are good weightlifters"
and, since its threshold depends on individuals outside the restrictor, it is not
conservative (definition 3, pp. 55–56). The probability is a relative frequency in the
limit, which imposes two constraints. The reference class may not be explicitly bounded
(§4.4.2), and it must be homogeneous: unrestricted homogeneity is degenerate, since
partitioning by the scope itself separates any mixed reference class (definition 4 and
Salmon's argument, pp. 81–82), so the final truth conditions demand the majority within
every inhabited cell of every salient partition of the restrictor (definition 5, p. 83).
"Mammals are female" then fails under the sex partition however many mammals are female
(§4.4.6). Frequency adverbs apply other thresholds to the same conditional probability —
always 1, never 0, sometimes non-zero, usually the same one half as gen — and respect only
the temporal partition, which is why "Primary school teachers are usually female" is true
while the bare generic is not (definition 10, p. 128; §6.2.3).

We state the three definitions over finite models, derive the degeneracy of unrestricted
homogeneity, the conservativity of the absolute reading and a non-conservativity witness
for the relative one, the recovery of the relativized classical quantifiers at the
frequency-adverb thresholds, and the paper's key examples.

## Implementation notes

Page and definition numbers follow the CSLI edition, a light revision of the 1996
dissertation that renames its independent and dependent readings absolute and relative.
The alternative set enters the truth conditions only through its extensional disjunction
and the relative threshold, so it is carried as a single predicate. A conditional
probability with an empty reference class is undefined in the paper (p. 37, §5.6) and is
the junk value `0` of `Quantification.prevalenceOn` here; theorems carry the non-emptiness
hypothesis, and a salient cell with an empty reference class imposes no condition.

## TODO

* The unboundedness constraint (§4.4.2) and lawlikeness (§4.4.3) restrict which sentences
  express generics at all — a matter of reference classes conceivable as unlimited, with no
  content over a fixed finite model — and are not stated.
* Chapter 5's calculus of alternatives (absolute determinables, focus, the connectives) and
  chapter 7's default reasoning are not formalized; the alternative set is taken as given,
  as in §3.2.

## References

* [A. Cohen, *Think Generic! The Meaning and Use of Generic Sentences* (1999)][cohen-1999a]
* [W. C. Salmon, *Objectively Homogeneous Reference Classes* (1977)][salmon-1977]
* [R. Thomason, *Theories of Nonmonotonicity and Natural Language Generics*
  (1988)][thomason-1988]
* [G. N. Carlson, *Reference to Kinds in English* (1977)][carlson-1977]
-/

namespace Cohen1999

open Quantification

variable {α : Type*} (domain : Finset α) (ψ alt φ : α → Prop)
variable [DecidablePred ψ] [DecidablePred alt] [DecidablePred φ]

/-- Cohen's generic quantifier on its absolute reading (definition 1, p. 37): the
conditional probability of the scope `φ`, given the restrictor `ψ` and the disjunction
`alt` of the alternatives to the scope, exceeds one half. -/
def gen : Prop :=
  1 / 2 < prevalenceOn domain (fun x => ψ x ∧ alt x) φ

instance : Decidable (gen domain ψ alt φ) := by unfold gen; infer_instance

/-- The relative reading (definition 3, p. 56): the restrictor raises the probability of
the scope above its average over the alternatives. -/
def genRelative : Prop :=
  prevalenceOn domain alt φ < prevalenceOn domain (fun x => ψ x ∧ alt x) φ

instance : Decidable (genRelative domain ψ alt φ) := by unfold genRelative; infer_instance

/-- The final truth conditions (definition 5, p. 83): the absolute threshold within every
salient cell whose reference class is inhabited. -/
def genSalient {ι : Type*} (cells : ι → α → Prop) [∀ i, DecidablePred (cells i)] : Prop :=
  ∀ i, 0 < countOn domain (fun x => (ψ x ∧ cells i x) ∧ alt x) →
    gen domain (fun x => ψ x ∧ cells i x) alt φ

/-- A frequency adverb applies its lexical requirement to the same conditional probability
(definition 10, p. 128); gen carries the requirement `(1 / 2 < ·)`, synonymous with
usually. -/
def freq (R : ℚ → Prop) : Prop :=
  R (prevalenceOn domain (fun x => ψ x ∧ alt x) φ)

/-- Unrestricted homogeneity (definition 4, p. 81, after Salmon): every inhabited
sub-reference class preserves the conditional probability of the scope. -/
def Homogeneous : Prop :=
  ∀ (part : α → Prop) [DecidablePred part],
    0 < countOn domain (fun x => ψ x ∧ part x) →
    prevalenceOn domain (fun x => ψ x ∧ part x) φ = prevalenceOn domain ψ φ

/-! ### The absolute reading and the majority quantifier -/

/-- The absolute reading in division-free, kernel-decidable form. -/
theorem gen_iff_thresholdGt (hR : 0 < countOn domain (fun x => ψ x ∧ alt x)) :
    gen domain ψ alt φ ↔ thresholdGtOn domain (fun x => ψ x ∧ alt x) φ 1 2 := by
  rw [gen, thresholdGtOn_iff_prevalenceOn _ _ _ 1 2 (by norm_num) hR]
  norm_num

/-- Over an inhabited reference class the absolute reading is the majority quantifier on
the restricted domain. -/
theorem gen_iff_mostOn (hR : 0 < countOn domain (fun x => ψ x ∧ alt x)) :
    gen domain ψ alt φ ↔ mostOn domain (fun x => ψ x ∧ alt x) φ :=
  (gen_iff_thresholdGt domain ψ alt φ hR).trans (thresholdGtOn_one_two_iff_mostOn _ _ _)

/-- gen is the adverb usually (definition 10, p. 128; p. 131). -/
theorem gen_iff_freq : gen domain ψ alt φ ↔ freq domain ψ alt φ (1 / 2 < ·) :=
  Iff.rfl

/-- The absolute reading is conservative: intersecting the scope with the restrictor
changes nothing (p. 54, after Wilkinson). -/
theorem gen_conservativity :
    gen domain ψ alt (fun x => ψ x ∧ φ x) ↔ gen domain ψ alt φ := by
  unfold gen prevalenceOn
  rw [countOn_congr (P := fun x => (ψ x ∧ alt x) ∧ ψ x ∧ φ x)
    (Q := fun x => (ψ x ∧ alt x) ∧ φ x) fun x _ => by tauto]

/-! ### The generalized-quantifier interface

Over the whole carrier with trivial alternatives the absolute reading is the majority
generalized quantifier, hence proportional: its truth depends only on the two cell counts.
The relativized readings are exactly what departs from this. -/

/-- With trivial alternatives over the whole carrier, gen is `most`. -/
theorem gen_univ_eq_most_sem {β : Type*} [Fintype β] (R S : β → Prop)
    [DecidablePred R] [DecidablePred S] (hR : 0 < countOn Finset.univ R) :
    gen Finset.univ R (fun _ => True) S ↔ Quantification.most_sem R S := by
  have hR' : 0 < countOn Finset.univ (fun x => R x ∧ True) := by
    rwa [countOn_congr (P := fun x => R x ∧ True) (Q := R) fun x _ => by simp]
  rw [gen_iff_mostOn _ _ _ _ hR', ← Quantification.mostOn_univ]
  unfold mostOn
  rw [countOn_congr (P := fun x => (R x ∧ True) ∧ S x) (Q := fun x => R x ∧ S x)
      fun x _ => by tauto,
    countOn_congr (P := fun x => (R x ∧ True) ∧ ¬ S x) (Q := fun x => R x ∧ ¬ S x)
      fun x _ => by tauto]

open Classical in
/-- With trivial alternatives over the whole carrier, gen is proportional
([peters-westerstahl-2006]) — a property of this operator that the genericity literature's
counterexamples to majority accounts target. -/
theorem gen_proportional {β : Type*} [Fintype β] :
    Proportional (fun R S : β → Prop => gen Finset.univ R (fun _ => True) S) := by
  intro R₁ S₁ R₂ S₂ tt₁ tf₁ tt₂ tf₂ h1 h2 hcross
  show gen Finset.univ R₁ _ S₁ ↔ gen Finset.univ R₂ _ S₂
  have hR1 : 0 < countOn Finset.univ R₁ := by
    show 0 < count (fun x => R₁ x); rw [count_decompose R₁ S₁]; exact h1
  have hR2 : 0 < countOn Finset.univ R₂ := by
    show 0 < count (fun x => R₂ x); rw [count_decompose R₂ S₂]; exact h2
  rw [gen_univ_eq_most_sem R₁ S₁ hR1, gen_univ_eq_most_sem R₂ S₂ hR2,
    ← Quantification.mostOn_univ, ← Quantification.mostOn_univ]
  exact mostOn_univ_proportional R₁ S₁ R₂ S₂ h1 h2 hcross

/-! ### Homogeneity is degenerate unrestricted (definition 4, p. 82) -/

/-- Salmon's two trivial cases are the only homogeneous reference classes: partitioning by
the scope itself separates any mixed one (p. 82). Hence definition 5 restricts the
partitions to the salient ones. -/
theorem homogeneous_iff (hR : 0 < countOn domain ψ) :
    Homogeneous domain ψ φ ↔ noOn domain ψ φ ∨ everyOn domain ψ φ := by
  constructor
  · intro h
    by_cases hno : noOn domain ψ φ
    · exact Or.inl hno
    · refine Or.inr ?_
      obtain ⟨x, hx, hψx, hφx⟩ : ∃ x ∈ domain, ψ x ∧ φ x := by
        by_contra hc
        exact hno fun y hy hψ hφ => hc ⟨y, hy, hψ, hφ⟩
      have hpos : 0 < countOn domain (fun y => ψ y ∧ φ y) :=
        countOn_pos_iff.mpr ⟨x, hx, hψx, hφx⟩
      have h1 : prevalenceOn domain (fun y => ψ y ∧ φ y) φ = 1 :=
        (prevalenceOn_eq_one_iff hpos).mpr fun y _ hy => hy.2
      exact (prevalenceOn_eq_one_iff hR).mp ((h φ hpos).symm.trans h1)
  · rintro (hno | hall) part _ hpart
    · rw [(prevalenceOn_eq_zero_iff hpart).mpr fun y hy hRy => hno y hy hRy.1,
        (prevalenceOn_eq_zero_iff hR).mpr hno]
    · rw [(prevalenceOn_eq_one_iff hpart).mpr fun y hy hRy => hall y hy hRy.1,
        (prevalenceOn_eq_one_iff hR).mpr hall]

/-! ### Frequency adverbs (definition 10, p. 128)

At the extreme thresholds the relativized classical quantifiers reappear; sometimes is the
existential, so a generic over an empty reference class entails nothing (§5.6). -/

/-- always: probability 1 is the relativized universal. -/
theorem freq_eq_one_iff (hR : 0 < countOn domain (fun x => ψ x ∧ alt x)) :
    freq domain ψ alt φ (· = 1) ↔ everyOn domain (fun x => ψ x ∧ alt x) φ :=
  prevalenceOn_eq_one_iff hR

/-- never: probability 0 is the relativized `no`. -/
theorem freq_eq_zero_iff (hR : 0 < countOn domain (fun x => ψ x ∧ alt x)) :
    freq domain ψ alt φ (· = 0) ↔ noOn domain (fun x => ψ x ∧ alt x) φ :=
  prevalenceOn_eq_zero_iff hR

/-- sometimes: positive probability is the relativized existential. -/
theorem freq_pos_iff (hR : 0 < countOn domain (fun x => ψ x ∧ alt x)) :
    freq domain ψ alt φ (0 < ·) ↔ someOn domain (fun x => ψ x ∧ alt x) φ :=
  prevalenceOn_pos_iff hR

/-! ### People have a hard time finding CMU (§3.2.1, after Thomason)

Twenty people, five of whom sought the university: four found it with difficulty, one with
ease. The alternatives — the levels of difficulty of the search — restrict the reference
class to the seekers, so the generic holds with no majority among people. -/

abbrev soughtCMU : Fin 20 → Prop := (·.val < 5)
abbrev hardTime : Fin 20 → Prop := (·.val < 4)

theorem cmu_gen : gen Finset.univ (fun _ => True) soughtCMU hardTime := by
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

theorem cmu_no_majority : ¬ gen Finset.univ (fun _ => True) (fun _ => True) hardTime := by
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

/-! ### Mammals bear live young; mammals are not female (§3.2.1 p. 33, §4.4.6 p. 91)

Twenty mammals, eight of which procreate: six bear live young, two lay eggs. Eleven are
female, among them every procreator. Relativized to the forms of procreation, the first
generic is true though bearers are a minority of all mammals, and the male cell of the sex
partition is empty of procreators, so definition 5 agrees. The second clears definition 1
on the female majority alone but fails definition 5, since the male cell is inhabited and
contains no female — the paper's resolution of the contrast with different alternatives and
the sex partition. By definition 10 the same threshold read as the adverb usually ignores
the non-temporal partition (§6.2.3), so "usually female" stays true. -/

abbrev procreates : Fin 20 → Prop := (·.val < 8)
abbrev bearsLive : Fin 20 → Prop := (·.val < 6)
abbrev female : Fin 20 → Prop := (·.val < 11)

/-- The sex partition: the females and the males. -/
abbrev sexCell : Bool → Fin 20 → Prop := fun b x => if b then female x else ¬ female x

theorem bearsLive_gen : gen Finset.univ (fun _ => True) procreates bearsLive := by
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

theorem bearsLive_no_majority :
    ¬ gen Finset.univ (fun _ => True) (fun _ => True) bearsLive := by
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

theorem bearsLive_genSalient :
    genSalient Finset.univ (fun _ => True) procreates bearsLive sexCell := by
  intro i hi
  cases i
  · exact absurd hi (by decide)
  · rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
    decide

theorem female_gen : gen Finset.univ (fun _ => True) (fun _ => True) female := by
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

theorem female_not_genSalient :
    ¬ genSalient Finset.univ (fun _ => True) (fun _ => True) female sexCell := by
  intro h
  have h1 := h false (by decide)
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)] at h1
  exact absurd h1 (by decide)

/-! ### Relative readings (§3.4.3–3.4.4, pp. 54–56)

Twenty people, fifteen of them weightlifters: the five Bulgarians all lift, two of them
well; one of the ten other lifters is good. A Bulgarian lifter is likelier than an
arbitrary one to be good, though no majority of Bulgarian lifters is. In the soccer
variant, where the lousy players concentrate outside Brazil, the relative reading correctly
rejects "Brazilians are lousy soccer players" yet accepts the sentence with its scope
intersected with the restrictor, whose average is lower — so the reading is not
conservative. -/

abbrev bulgarian : Fin 20 → Prop := (·.val < 5)
abbrev lifter : Fin 20 → Prop := (·.val < 15)
abbrev goodLifter : Fin 20 → Prop := fun x => x.val < 2 ∨ x.val = 5

theorem bulgarians_relative : genRelative Finset.univ bulgarian lifter goodLifter := by
  decide +kernel

theorem bulgarians_not_absolute : ¬ gen Finset.univ bulgarian lifter goodLifter := by
  rw [gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

abbrev brazilian : Fin 20 → Prop := (·.val < 5)
abbrev soccerPlayer : Fin 20 → Prop := (·.val < 15)
abbrev lousy : Fin 20 → Prop := fun x => x.val = 0 ∨ (5 ≤ x.val ∧ x.val < 13)

theorem brazilians_relative_rejected :
    ¬ genRelative Finset.univ brazilian soccerPlayer lousy := by
  decide +kernel

/-- The relative reading is not conservative (p. 55): intersecting the scope with the
restrictor flips the verdict. -/
theorem genRelative_not_conservative :
    ¬ (genRelative Finset.univ brazilian soccerPlayer (fun x => brazilian x ∧ lousy x) ↔
        genRelative Finset.univ brazilian soccerPlayer lousy) := by
  decide +kernel

end Cohen1999
