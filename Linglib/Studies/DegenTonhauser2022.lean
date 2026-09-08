import Linglib.Studies.DegenTonhauser2021
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Degen and Tonhauser (2022): Are there factive predicates?

This file formalizes the argument of [degen-tonhauser-2022] that neither standard definition
of a factive predicate identifies a coherent class among the twenty clause-embedding
predicates of [degen-tonhauser-2021]: that the content of the clausal complement is
presupposed, (3a), after [kiparsky-kiparsky-1970], or presupposed and entailed, (3b), after
[gazdar-1979]. The predicates carry the traditional classification (13) into canonically
factive, nonveridical and veridical nonfactive, and optionally factive. Definition (3a)
expects the complements of the canonically factive predicates to project categorically more
than the rest, which over a finite set of predicates is the existence of a threshold putting
exactly that class on top; the certainty ratings of experiments 1a and 1b refute it, the
optionally factive *inform* outrating the canonically factive *reveal* under both tasks, so
no nonarbitrary line can be drawn. Under definition (3b) every complement is projective, so
the class is the set of entailed complements, and that set is empty or heterogeneous in
projection: the gradient inference diagnostic of experiment 2a finds only *be right* and
*prove* entailed, and they project below every canonically factive predicate; the
categorical diagnostic of experiment 2b adds *know*, *see*, *discover* and *confirm*; and
the contradictoriness diagnostic of experiments 3a and 3b finds no entailed complement at
all. The paper concludes that projection and entailment do not jointly identify a class of
factive predicates, and so that the explanandum of projection analyses in the tradition of
[heim-1983] and [van-der-sandt-1992] is not delimited by such a class, while noting, as its
third objection, that gradient ratings alone cannot rule out a binary category on which
predicates are lexically ambiguous and listeners uncertain about the entry used. The
Fragment's presupposition triggers among the twenty predicates are exactly the canonically
factive ones.

## Implementation notes

The by-predicate means are computed from the authors' data at
github.com/judith-tonhauser/projective-probability, rounded to two decimals: the mean
certainty ratings of experiment 1a, Figure 2, from 266 participants, with the main-clause
controls at 0.11; the proportions of 'yes' certainty responses of experiment 1b, Figure 4,
from 436 participants, with the controls at 0.00; and the mean inference ratings of
experiment 2a, Figure 9, from 259 participants, with the entailing controls at 0.96 and the
non-entailing at 0.03. The entailed sets are the paper's model results, the predicates whose
credible interval against the entailing controls contained zero.

## References

* [degen-tonhauser-2022]
* [degen-tonhauser-2021]
* [kiparsky-kiparsky-1970]
* [gazdar-1979]
* [heim-1983]
* [van-der-sandt-1992]
-/

namespace DegenTonhauser2022

open DegenTonhauser2021

/-! ### The traditional classification -/

/-- The traditional classification of the twenty predicates, (13), by whether the complement
content is taken to be presupposed and whether it is taken to be entailed. -/
inductive Factivity where
  /-- Presupposed: *be annoyed*, *discover*, *know*, *reveal*, *see*. -/
  | canonicallyFactive
  /-- Neither presupposed nor entailed: *pretend*, *say*, *suggest*, *think*. -/
  | nonveridicalNonfactive
  /-- Entailed but not presupposed: *be right*, *demonstrate*. -/
  | veridicalNonfactive
  /-- Presupposed only sometimes: *acknowledge*, *admit*, *announce*, *confess*, *confirm*,
  *establish*, *hear*, *inform*, *prove*. -/
  | optionallyFactive
  deriving DecidableEq, Repr

/-- The classification (13). -/
def factivity : Predicate → Factivity
  | .beAnnoyed | .discover | .know | .reveal | .see => .canonicallyFactive
  | .pretend | .say | .suggest | .think => .nonveridicalNonfactive
  | .beRight | .demonstrate => .veridicalNonfactive
  | .acknowledge | .admit | .announce | .confess | .confirm
  | .establish | .hear | .inform | .prove => .optionallyFactive

/-- The Fragment's presupposition triggers among the twenty predicates are exactly the
canonically factive ones, those whose complement the classification takes to be
presupposed. -/
theorem isPresupTrigger_iff (p : Predicate) :
    (toPredicateCore p).isPresupTrigger = true ↔ factivity p = .canonicallyFactive := by
  cases p <;> decide

/-! ### A categorical distinction as separation -/

section Separation

variable {α β : Type*} [LinearOrder β] {cls : α → Prop} {rating : α → β} {p q : α}

/-- A class is separated by a rating when every member outrates every non-member. -/
def Separates (cls : α → Prop) (rating : α → β) : Prop :=
  ∀ ⦃p q⦄, cls p → ¬cls q → rating q < rating p

/-- A non-member rating at least as high as a member defeats separation. -/
theorem not_separates (hp : cls p) (hq : ¬cls q) (hpq : rating p ≤ rating q) :
    ¬ Separates cls rating :=
  λ h => absurd (h hp hq) (not_lt.mpr hpq)

/-- A class is separated by a rating iff some threshold puts exactly the class above it, the
threshold being the top non-member rating. -/
theorem separates_iff_exists_threshold [Fintype α] [DecidablePred cls] (h : ∃ q, ¬cls q) :
    Separates cls rating ↔ ∃ t, ∀ p, cls p ↔ t < rating p := by
  obtain ⟨q₀, hq₀⟩ := h
  have hs : (Finset.univ.filter λ q => ¬cls q).Nonempty := ⟨q₀, by simp [hq₀]⟩
  constructor
  · intro hsep
    refine ⟨(Finset.univ.filter λ q => ¬cls q).sup' hs rating,
      λ p => ⟨λ hp => ?_, λ hlt => ?_⟩⟩
    · exact (Finset.sup'_lt_iff hs).mpr λ b hb => hsep hp (by simpa using hb)
    · by_contra hp
      exact absurd hlt (not_lt.mpr (Finset.le_sup' rating (by simpa using hp)))
  · rintro ⟨t, ht⟩ p q hp hq
    exact (not_lt.mp λ hlt => hq ((ht q).mpr hlt)).trans_lt ((ht p).mp hp)

end Separation

/-! ### The ratings -/

/-- A predicate's means: the certainty rating of experiment 1a, the proportion of 'yes'
certainty responses of experiment 1b, and the inference rating of experiment 2a. -/
structure Ratings where
  certainty1a : ℚ
  certainty1b : ℚ
  inference2a : ℚ
  deriving DecidableEq, Repr

/-- The by-predicate means of experiments 1a, 1b and 2a. -/
def ratings : Predicate → Ratings
  | .acknowledge => ⟨0.72, 0.78, 0.90⟩
  | .admit => ⟨0.66, 0.67, 0.91⟩
  | .announce => ⟨0.58, 0.57, 0.81⟩
  | .beAnnoyed => ⟨0.88, 0.92, 0.92⟩
  | .beRight => ⟨0.18, 0.03, 0.96⟩
  | .confess => ⟨0.64, 0.58, 0.89⟩
  | .confirm => ⟨0.34, 0.16, 0.94⟩
  | .demonstrate => ⟨0.49, 0.31, 0.85⟩
  | .discover => ⟨0.78, 0.84, 0.94⟩
  | .establish => ⟨0.36, 0.19, 0.90⟩
  | .hear => ⟨0.75, 0.81, 0.50⟩
  | .inform => ⟨0.81, 0.90, 0.83⟩
  | .know => ⟨0.86, 0.93, 0.93⟩
  | .pretend => ⟨0.15, 0.07, 0.12⟩
  | .prove => ⟨0.30, 0.13, 0.96⟩
  | .reveal => ⟨0.70, 0.69, 0.90⟩
  | .say => ⟨0.24, 0.07, 0.68⟩
  | .see => ⟨0.81, 0.86, 0.95⟩
  | .suggest => ⟨0.22, 0.07, 0.34⟩
  | .think => ⟨0.20, 0.04, 0.32⟩

/-- Every complement projects: each predicate's certainty rating exceeds the main-clause
controls' 0.11 in experiment 1a. -/
theorem all_projective (p : Predicate) : 0.11 < (ratings p).certainty1a := by
  cases p <;> norm_num [ratings]

/-! ### Definition (3a): no categorical projection distinction -/

/-- Neither task's certainty ratings separate the canonically factive class: under both the
optionally factive *inform* outrates the canonically factive *reveal*. -/
theorem not_separates_certainty :
    ¬ Separates (factivity · = .canonicallyFactive) (λ p => (ratings p).certainty1a) ∧
      ¬ Separates (factivity · = .canonicallyFactive) (λ p => (ratings p).certainty1b) :=
  ⟨not_separates (p := .reveal) (q := .inform) rfl (by decide) (by norm_num [ratings]),
    not_separates (p := .reveal) (q := .inform) rfl (by decide) (by norm_num [ratings])⟩

/-- No threshold on either task's ratings recovers the class: no nonarbitrary line can be
drawn. -/
theorem not_exists_threshold_certainty :
    (¬ ∃ t, ∀ p, factivity p = .canonicallyFactive ↔ t < (ratings p).certainty1a) ∧
      ¬ ∃ t, ∀ p, factivity p = .canonicallyFactive ↔ t < (ratings p).certainty1b :=
  ⟨λ h => not_separates_certainty.1
      ((separates_iff_exists_threshold ⟨.inform, by decide⟩).2 h),
    λ h => not_separates_certainty.2
      ((separates_iff_exists_threshold ⟨.inform, by decide⟩).2 h)⟩

/-! ### Definition (3b): entailment against projection -/

/-- The entailment diagnostics: the inference diagnostic with gradient (2a) and categorical
(2b) responses, and the contradictoriness diagnostic (3a, 3b). -/
inductive Diagnostic where
  | inference2a
  | inference2b
  | contradictoriness
  deriving DecidableEq, Repr

/-- The predicates whose complements rated with the entailed controls under a diagnostic:
since every complement projects, the class definition (3b) identifies. -/
def entailed : Diagnostic → Finset Predicate
  | .inference2a => {.beRight, .prove}
  | .inference2b => {.beRight, .prove, .know, .see, .discover, .confirm}
  | .contradictoriness => ∅

/-- The class definition (3b) identifies is empty or heterogeneous in projection: on the
contradictoriness diagnostic nothing is entailed, and on either inference diagnostic the
entailed *be right* projects below the nonveridical nonfactive *say*. -/
theorem entailed_empty_or_not_separates (d : Diagnostic) :
    entailed d = ∅ ∨ ¬ Separates (· ∈ entailed d) (λ p => (ratings p).certainty1a) := by
  cases d
  iterate 2
    exact .inr (not_separates (p := .beRight) (q := .say) (by decide) (by decide)
      (by norm_num [ratings]))
  exact .inl rfl

/-- The best contenders under (3b) are among the least projective: *be right* and *prove*,
the entailed complements of experiment 2a, project below every canonically factive
predicate. -/
theorem entailed_inference2a_below_canonicallyFactive (p : Predicate)
    (hp : factivity p = .canonicallyFactive) :
    ∀ q ∈ entailed .inference2a, (ratings q).certainty1a < (ratings p).certainty1a := by
  cases p <;> first
    | exact absurd hp (by decide)
    | (simp only [entailed, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
       norm_num [ratings])

end DegenTonhauser2022
