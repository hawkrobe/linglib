module

public import Linglib.Studies.MitrovicSauerland2016
public import Linglib.Data.Experiments.BillEtAl2025
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bill, Gonzalez, Driemel, Makharoblidze and Pintér (2025): Is DP conjunction always complex?

Bill and colleagues test Mitrović and Sauerland's decomposition of noun-phrase conjunction on
children's comprehension of the three conjunctive expressions of Georgian and Hungarian: a J
particle alone, a μ particle on each conjunct, and both. On the decomposition the three share one
structure and differ in which of its heads they pronounce, so with van Hout's Transparency
Principle the fully pronounced J-μ expressions should be the easiest; on the rival structures of
Szabolcsi and of Haslinger and colleagues, J expressions are the simplest. Georgian children
instead replayed J-μ sentences more often than J or μ sentences, and Hungarian children showed no
difference, so neither account meets the conditions the paper sets for a successful one.

## Main definitions

* `Account`: an assignment of underlying heads to the strategies, with `Account.universal`
  (Mitrović and Sauerland) and `Account.bareJ` (the rival structures).
* `Account.covert`, `Account.complexity`: the heads a strategy leaves unpronounced, and all of
  its heads.
* `Easier`: the order a measure of difficulty predicts.
* `observedHarder`, `Desiderata`: the order the paper observes and its conditions on a measure.
* `BasicTrue`, `Accurate`, `errorKind`: the truth conditions, the accuracy and the kind of error of
  an end state of the act-out task.

## Main results

* `transparency_prediction`: the decomposition with the Transparency Principle predicts J-μ
  easiest.
* `bareJ_prediction`, `bareJ_muOnly_opaque`: the rival predicts J easier than J-μ, and μ more
  opaque than J-μ.
* `desiderata_iff`: a measure meets the paper's conditions exactly when the order it predicts is
  the observed one, which none of `Account.universal.covert`, `Account.bareJ.complexity` and
  `Account.bareJ.covert` does.
* `basicTrue_iff_conjunction`: the decomposition computes the truth conditions of the test
  sentences.

## Implementation notes

The printed results are the tables of `Data.Experiments.BillEtAl2025`; the study states the
paper's reading of them, `observedHarder`, and does not recompute significance. The type-shifter
of Fig. 2 is not counted as a head: no language pronounces it, and it would add the same constant
to every count. The rival structures are the paper's simplification in Fig. 1, since neither
Szabolcsi's nor Haslinger and colleagues' analysis is formalized.

## References

* [bill-etal-2025]
* [mitrovic-sauerland-2014]
* [mitrovic-sauerland-2016]
* [van-hout-1998]
* [szabolcsi-2015]
* [haslinger-etal-2019]
* [clark-2017]
-/

@[expose] public section

namespace BillEtAl2025

open MitrovicSauerland2016

/-- Both test languages attest all three strategies, the precondition of the test, (1) and
(2). -/
theorem both_have_all_three :
    hasAllThreeStrategies georgian ∧ hasAllThreeStrategies hungarian := by
  decide

/-! ### Accounts and their measures -/

/-- An account assigns each strategy the heads of its underlying structure, among which are the
heads it pronounces (Fig. 1). -/
structure Account where
  /-- The heads of the structure underlying a strategy. -/
  underlying : ConjunctionStrategy → Finset Head
  pronounced_subset : ∀ s, s.pronounced ⊆ underlying s

namespace Account

/-- Mitrović and Sauerland give every strategy the whole structure, Fig. 1b and Fig. 2. -/
def universal : Account := ⟨fun _ ↦ Finset.univ, fun _ ↦ Finset.subset_univ _⟩

/-- The rival structures give J expressions J alone, Fig. 1a, and μ and J-μ expressions the
whole structure, Fig. 1b. -/
def bareJ : Account where
  underlying
    | .jOnly => {.j}
    | .muOnly | .jMu => Finset.univ
  pronounced_subset s := by cases s <;> decide

/-- The complexity of a strategy is the number of heads in its structure. -/
def complexity (a : Account) (s : ConjunctionStrategy) : ℕ := (a.underlying s).card

/-- The covert pieces of a strategy are the heads of its structure it leaves unpronounced, the
Transparency Principle's measure of difficulty, (3). -/
def covert (a : Account) (s : ConjunctionStrategy) : ℕ := (a.underlying s \ s.pronounced).card

theorem card_pronounced_add_covert (a : Account) (s : ConjunctionStrategy) :
    s.pronounced.card + a.covert s = a.complexity s := by
  simpa [covert, complexity, add_comm] using
    Finset.card_sdiff_add_card_eq_card (a.pronounced_subset s)

theorem universal_covert (s : ConjunctionStrategy) :
    universal.covert s = Fintype.card Head - s.pronounced.card := by
  simp [covert, universal, Finset.card_univ_sdiff]

end Account

/-- A measure of difficulty predicts `s` easier than `t` when it is smaller on `s`. -/
def Easier (c : ConjunctionStrategy → ℕ) : ConjunctionStrategy → ConjunctionStrategy → Prop :=
  InvImage (· < ·) c

instance (c : ConjunctionStrategy → ℕ) : DecidableRel (Easier c) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ < _))

/-! ### The predictions -/

/-- The decomposition with the Transparency Principle predicts J-μ, which pronounces every head,
easier than either other strategy, (4). -/
theorem transparency_prediction (s : ConjunctionStrategy) (h : s ≠ .jMu) :
    Easier Account.universal.covert .jMu s := by
  cases s <;> first | exact absurd rfl h | decide

/-- If the more complex is the harder, the rival predicts J expressions easier than J-μ
expressions (§4). -/
theorem bareJ_prediction : Easier Account.bareJ.complexity .jOnly .jMu := by decide

/-- The rival gives μ and J-μ expressions one structure (§4). -/
theorem bareJ_underlying_muOnly :
    Account.bareJ.underlying .muOnly = Account.bareJ.underlying .jMu := rfl

/-- On the rival structures μ expressions are the more opaque of μ and J-μ (§4). -/
theorem bareJ_muOnly_opaque : Easier Account.bareJ.covert .jMu .muOnly := by decide

/-! ### The finding -/

/-- Georgian children replayed J-μ sentences more often than J and than μ sentences, and J and μ
sentences did not differ (Table 3, §3.1.2 and §4), so J-μ is harder than both. -/
def observedHarder : ConjunctionStrategy → ConjunctionStrategy → Prop
  | .jMu, .jOnly | .jMu, .muOnly => True
  | _, _ => False

/-- The observed differences run against the decomposition's prediction (§4). -/
theorem observedHarder_contradicts_transparency (s t : ConjunctionStrategy)
    (h : observedHarder s t) : Easier Account.universal.covert s t := by
  cases s <;> cases t <;> simp [observedHarder] at h <;> decide

/-- A measure meets conditions (i) and (ii) of §4 when J-μ is more complex than J and than μ,
and J and μ are equally complex. -/
def Desiderata (c : ConjunctionStrategy → ℕ) : Prop :=
  c .jOnly < c .jMu ∧ c .muOnly < c .jMu ∧ c .jOnly = c .muOnly

instance (c : ConjunctionStrategy → ℕ) : Decidable (Desiderata c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The conditions say that the order a measure predicts is the observed one. -/
theorem desiderata_iff (c : ConjunctionStrategy → ℕ) :
    Desiderata c ↔ ∀ s t, Easier c s t ↔ observedHarder t s := by
  constructor
  · rintro ⟨h1, h2, h3⟩ s t
    cases s <;> cases t <;> simp [Easier, InvImage, observedHarder] <;> omega
  · intro h
    refine ⟨(h _ _).2 trivial, (h _ _).2 trivial, ?_⟩
    have := h .jOnly .muOnly; have := h .muOnly .jOnly
    simp [Easier, InvImage, observedHarder] at *
    omega

theorem universal_covert_not_desiderata : ¬ Desiderata Account.universal.covert := by decide

theorem bareJ_complexity_not_desiderata : ¬ Desiderata Account.bareJ.complexity := by decide

theorem bareJ_covert_not_desiderata : ¬ Desiderata Account.bareJ.covert := by decide

/-- Condition (iii) of §4 asks for Hungarian μ to be less complex than Georgian μ, and the paper's
morphological route is that Georgian *-c* is a bound clitic where Hungarian *is* is free
([clark-2017]). -/
theorem mu_kind_differs :
    (georgian.exponent (.mu 0)).map (·.kind) = some (.bound .after .clitic) ∧
      (hungarian.exponent (.mu 0)).map (·.kind) = some .free := by
  decide

/-! ### The act-out task -/

/-- A trial shows three objects, of which the test sentence mentions two (§2.2). -/
abbrev Object := Fin 3

/-- An end state of a trial is the set of objects on the table. -/
abbrev EndState := Finset Object

/-- The test sentence mentions the first two objects. -/
def mentioned : Finset Object := {0, 1}

/-- An end state meets the basic truth conditions of the test sentence when each mentioned object
is on the table (§3.1.2). -/
def BasicTrue (st : EndState) : Prop := mentioned ⊆ st

/-- An end state is accurate when it matches the exhaustified sentence, with the mentioned
objects and nothing else on the table (§2.3). -/
def Accurate (st : EndState) : Prop := st = mentioned

instance : DecidablePred BasicTrue := fun st ↦ inferInstanceAs (Decidable (_ ⊆ st))

instance : DecidablePred Accurate := fun st ↦ inferInstanceAs (Decidable (st = _))

theorem accurate_imp_basicTrue {st : EndState} (h : Accurate st) : BasicTrue st :=
  h ▸ Finset.Subset.refl _

theorem not_basicTrue_singleton : ¬ BasicTrue {0} := by decide

/-- The decomposition, a conjunctive J over the μ phrases of the shifted conjuncts, computes the
basic truth conditions of *is on the table* (Fig. 2). -/
theorem basicTrue_iff_conjunction {j : Coordinator} (hj : j.role = .conjunctive)
    (st : EndState) : j.denote {mu (shift (0 : Object)), mu (shift 1)} (· ∈ st) ↔ BasicTrue st := by
  rw [conjunction_apply hj]; simp [BasicTrue, mentioned, Finset.insert_subset_iff]

/-- An inaccurate end state either has an unmentioned object on the table, or else exactly one of
the mentioned objects, or else neither (footnote 12). -/
def errorKind (st : EndState) : ErrorKind :=
  if ∃ o ∈ st, o ∉ mentioned then .unmentioned
  else if (st ∩ mentioned).card = 1 then .oneMentioned
  else .neitherMentioned

/-- Each kind of error of footnote 12 is the kind of some end state. -/
theorem errorKind_surjective : Function.Surjective errorKind := by
  intro k; cases k
  · exact ⟨{2}, by decide⟩
  · exact ⟨{0}, by decide⟩
  · exact ⟨∅, by decide⟩

/-- The error counts of footnote 12 add up to the children's errors. -/
example : ∑ k, (childErrorKinds k).count = childErrors := by decide

/-- The printed percentages of footnote 12 round the counts. -/
example : ∀ k, (childErrorKinds k).percent.RoundsPercent (childErrorKinds k).count childErrors := by
  decide

end BillEtAl2025
