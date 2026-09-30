module

public import Linglib.Studies.Schlenker2009
public import Linglib.Data.Experiments.ChemlaSchlenker2012

/-!
# Chemla & Schlenker (2012): Incremental vs. symmetric accounts of presupposition projection

This file formalizes the paper's predictions and its experimental results. The paper takes a
trivalent theory in which a sentence is presuppositionally acceptable when its supervaluation is
defined at every world of the context (its (9), the symmetric condition, `SuperS` of
[schlenker-2009]'s appendix), and an incremental condition that also completes the sentence after
each trigger by every good final without triggers (its (10), `SuperI`). The Incremental Theory
lets (10) alone govern projection; the Strict Symmetric Theory lets (9) alone govern it; the Mixed
Theory prefers (10) but lets a presupposition satisfied only by (9) through at a cost.

The experiments test sentences with the anaphoric trigger *too* in *if*-, *or*- and
*unless*-sentences, with the clause that can satisfy the presupposition before the trigger
(canonical order) or after it (inverse order) ((48)–(49), `target`). In the canonical order both
conditions predict the conditional presupposition `if p, q` ((13a)–(15a), `superI_canonical`,
`superS_canonical`). In the inverse order the incremental condition predicts the unconditional
presupposition `q` (`superI_inverse`), while the symmetric condition still predicts `if p, q`
((13b)–(15b), `superS_inverse`).

The results are `Data/Experiments/ChemlaSchlenker2012`. The conditional inference is endorsed more
than the unconditional one for every tested sentence (Tables 4 and 7,
`experiment1_conditional_gt_unconditional`, `experiment4_conditional_gt_unconditional`), including
the inverse order, where the Incremental Theory predicts the unconditional presupposition and so an
unconditional inference (`superI_inverse_subset`) and the symmetric condition does not
(`exists_superS_inverse_not_subset`). And every target sentence of Experiment 2 is rated above the
control that forces local accommodation with *too* (Table 5, `experiment2_targets_gt_control`), so
the inverse order is not unacceptable.

## Implementation notes

* Conditionals are material implications and *unless F, G* is *if not F, G*, as the paper assumes
  (§1.4).
* The properties of *too* that the paper's argument uses to separate the Incremental from the Mixed
  Theory's predictions for inferences (§2.2, §2.3) are not formalized, and neither is the Mixed
  Theory's cost, so the fit of the theories to the ratings is not stated here.

## References

* [chemla-schlenker-2012]
* [schlenker-2009]
-/

@[expose] public section

namespace ChemlaSchlenker2012

open Presupposition Schlenker2009

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### The predictions of §1.4 -/

/-- §1.4: *unless F, G* means *if not F, G*. -/
def unlessThen (F G : Formula Atom) : Formula Atom := .bin .cond (.not F) G

/-- (48)–(49), p. 200: the target sentence of a construction in an order, with the clause `p` that
can satisfy the presupposition `q` of the trigger `qq'`. -/
def target (p q q' : Atom) : Construction → Order → Formula Atom
  | .ifSentence, .canonical => .bin .cond (.atom p) (.trigger q q')
  | .ifSentence, .inverse => .bin .cond (.not (.trigger q q')) (.not (.atom p))
  | .orSentence, .canonical => .bin .disj (.not (.atom p)) (.trigger q q')
  | .orSentence, .inverse => .bin .disj (.trigger q q') (.not (.atom p))
  | .unlessSentence, .canonical => unlessThen (.not (.atom p)) (.trigger q q')
  | .unlessSentence, .inverse => unlessThen (.trigger q q') (.not (.atom p))

variable {p q q' : Atom} {C : Set W}

private theorem superI_iff_forall {F : Formula Atom} :
    SuperI I C F ↔ ∀ w ∈ C, (F.filter I).presup w :=
  (superI_iff I C F).trans Iff.rfl

private theorem superS_iff_forall {F : Formula Atom} (hF : (F.occurrences.map Prod.snd).Nodup) :
    SuperS I C F ↔ ∀ w ∈ C, (F.strong I).presup w :=
  forall₂_congr fun _ _ ↦ superDefined_iff_of_nodup I hF

/-- (13a)–(15a), p. 185: in the canonical order the incremental condition predicts the
conditional presupposition `if p, q`. -/
theorem superI_canonical (k : Construction) :
    SuperI I C (target p q q' k .canonical) ↔ C ⊆ {w | w ∈ I p → w ∈ I q} := by
  rw [superI_iff_forall]
  refine forall₂_congr fun w _ ↦ ?_
  cases k <;> simp [target, unlessThen, Formula.filter, Connective.filter, PartialProp.impFilter,
    PartialProp.orFilter, PartialProp.neg]

/-- (13a)–(15a), p. 185: in the canonical order the symmetric condition predicts the
conditional presupposition `if p, q`. -/
theorem superS_canonical (k : Construction) :
    SuperS I C (target p q q' k .canonical) ↔ C ⊆ {w | w ∈ I p → w ∈ I q} := by
  cases k <;> rw [superS_iff_forall I (by simp [target, unlessThen, Formula.occurrences])] <;>
    refine forall₂_congr fun w _ ↦ ?_ <;>
    simp [target, unlessThen, Formula.strong, Connective.strong, PartialProp.orStrong,
      PartialProp.neg] <;> tauto

/-- (13b)–(15b), p. 185: in the inverse order the incremental condition predicts the unconditional
presupposition `q`. -/
theorem superI_inverse (k : Construction) :
    SuperI I C (target p q q' k .inverse) ↔ C ⊆ I q := by
  rw [superI_iff_forall]
  refine forall₂_congr fun w _ ↦ ?_
  cases k <;> simp [target, unlessThen, Formula.filter, Connective.filter, PartialProp.impFilter,
    PartialProp.orFilter, PartialProp.neg]

/-- (13b)–(15b), p. 185: in the inverse order the symmetric condition still predicts the
conditional presupposition `if p, q`. -/
theorem superS_inverse (k : Construction) :
    SuperS I C (target p q q' k .inverse) ↔ C ⊆ {w | w ∈ I p → w ∈ I q} := by
  cases k <;> rw [superS_iff_forall I (by simp [target, unlessThen, Formula.occurrences])] <;>
    refine forall₂_congr fun w _ ↦ ?_ <;>
    simp [target, unlessThen, Formula.strong, Connective.strong, PartialProp.orStrong,
      PartialProp.neg] <;> tauto

/-- §2.3.2: in the inverse order, any context that the Incremental Theory accepts entails the
unconditional presupposition. -/
theorem superI_inverse_subset (k : Construction) (h : SuperI I C (target p q q' k .inverse)) :
    C ⊆ I q :=
  (superI_inverse I k).1 h

/-- The symmetric condition accepts the inverse order in a context that does not entail the
unconditional presupposition, one with a world where `p` and `q` both fail. -/
theorem exists_superS_inverse_not_subset (k : Construction) {w : W} (hp : w ∉ I p)
    (hq : w ∉ I q) : SuperS I {w} (target p q q' k .inverse) ∧ ¬ {w} ⊆ I q := by
  refine ⟨(superS_inverse I k).2 fun v hv hpv ↦ ?_, fun h ↦ hq (h rfl)⟩
  rw [Set.mem_singleton_iff] at hv
  exact absurd (hv ▸ hpv) hp

/-! ### The results -/

/-- Table 4, p. 206: in Experiment 1, for every tested sentence, the conditional inference is
endorsed more than the unconditional one. -/
theorem experiment1_conditional_gt_unconditional :
    ∀ r ∈ experiment1Inferences, r.inference = .conditional →
      ∃ r' ∈ experiment1Inferences, r'.construction = r.construction ∧ r'.order = r.order ∧
        r'.inference = .unconditional ∧ r'.mean.toRat < r.mean.toRat := by
  decide +kernel

/-- Table 7, p. 212: in Experiment 4, for every tested sentence, the conditional inference is
endorsed more than the unconditional one. -/
theorem experiment4_conditional_gt_unconditional :
    ∀ r ∈ experiment4Inferences, r.inference = .conditional →
      ∃ r' ∈ experiment4Inferences, r'.construction = r.construction ∧ r'.order = r.order ∧
        r'.inference = .unconditional ∧ r'.mean.toRat < r.mean.toRat := by
  decide +kernel

/-- Table 5, p. 209: every target sentence of Experiment 2 is rated above the control sentence
that forces local accommodation with *too*. -/
theorem experiment2_targets_gt_control :
    ∀ r ∈ experiment2Targets,
      (experiment2Controls .localAccommodationToo).mean.toRat < r.mean.toRat := by
  decide +kernel

end ChemlaSchlenker2012
