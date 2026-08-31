import Linglib.Features.Givenness
import Linglib.Semantics.Focus.Marking
import Linglib.Semantics.Focus.ExtractionClash

/-!
# Cartner et al. 2026: subject islands do not reduce to discourse function

This file formalizes the argument of [cartner-et-al-2026] against information-structural accounts
of the subject island. On the Focus Background Constraint of [abeille-et-al-2020] a subject island
is a clash between a focused filler and a backgrounded extraction domain, so the effect should
appear where the filler is focused and not otherwise: in wh-questions but not in relative clauses
or topicalization, whose fillers are given. Three factorial acceptability experiments
([sprouse-2007], [sprouse-et-al-2012]) find the effect in all three constructions and at
comparable magnitude, which no reading of the constraint accommodates — the revised, gradient
formulation of [winckel-et-al-2025] makes the same prediction on these materials, where filler and
governor carry binary focus marks.

The design holds the extraction domain constant and varies the filler, so it bears only on
accounts that read the filler. An account whose prediction is a function of the domain alone —
direct backgroundedness ([cuneo-goldberg-2023]), or a structural constraint on the configuration —
predicts the same verdict in every construction and is untouched by the result, as the paper notes
(§8).

## Main definitions

* `FGDConstruction`, `fillerFocus`, `subjectGivenness` — the three constructions and the two
  information-structural axes the design manipulates and holds fixed
* `fbcPredictsIsland`, `fbcRevisedPredictsIsland` — the two formulations of the constraint

## Main results

* `both_fbcs_same_predictions` — the revised constraint predicts what the original does here
* `fbc_predicts_construction_dependence` — the constraint makes the effect turn on construction
* `fbc_falsified`, `fbcRevised_falsified` — an effect in relative clauses refutes either
* `domain_only_predicts_invariance` — an account reading only the domain predicts invariance, so
  the experiments leave it standing

## References

* [cartner-et-al-2026]
* [abeille-et-al-2020]
* [winckel-et-al-2025]
* [cuneo-goldberg-2023]
* [sprouse-2007]
* [sprouse-et-al-2012]
-/

namespace CartnerEtAl2026

open Features (BinaryGivenness)
open Focus (Mark)
open Focus.ExtractionClash (extractionISClash)

/-! ### Filler-gap constructions and their information structure -/

/-- The three filler-gap constructions the experiments compare. They share the movement
mechanism and differ in the information-structural status of the filler. -/
inductive FGDConstruction where
  | whQuestion
  | relativeClause
  | topicalization
  deriving DecidableEq, Repr

/-- Focus marking of the filler: a wh-phrase is focused, while a relative-clause head is
presupposed and a topic is discourse-old ([abeille-et-al-2020] §2, [winckel-et-al-2025]). -/
def fillerFocus : FGDConstruction → Mark
  | .whQuestion => .focused
  | .relativeClause | .topicalization => .nonFocused

/-- Givenness of the extraction domain. Subjects are backgrounded in all three constructions,
which is what the design holds constant. -/
def subjectGivenness : FGDConstruction → BinaryGivenness
  | _ => .given

/-- The extraction domain is uniform across the three constructions, so any difference between
them is a difference in the filler. -/
theorem subjectGivenness_uniform (c c' : FGDConstruction) :
    subjectGivenness c = subjectGivenness c' := rfl

/-- The filler is not: only the wh-question's is focused. This is the variable the constraint
claims should modulate the island effect. -/
theorem fillerFocus_varies :
    fillerFocus .whQuestion ≠ fillerFocus .relativeClause ∧
      fillerFocus .whQuestion ≠ fillerFocus .topicalization := by
  constructor <;> simp [fillerFocus]

/-! ### The Focus Background Constraint -/

/-- The constraint of [abeille-et-al-2020]: a focused element should not be part of a backgrounded
constituent, so extraction of a focused filler from a backgrounded domain clashes. This is
`extractionISClash`, which the substrate shares with [erteschik-shir-1973]'s Dominance Condition. -/
def fbcPredictsIsland (c : FGDConstruction) : Prop :=
  extractionISClash (fillerFocus c) (subjectGivenness c)

instance (c : FGDConstruction) : Decidable (fbcPredictsIsland c) :=
  inferInstanceAs (Decidable (extractionISClash _ _))

/-- Focus marking of the subject, the governor of the extraction site. The materials hold it
non-focused throughout while varying the filler. -/
def subjectFocus : FGDConstruction → Mark
  | _ => .nonFocused

/-- The revised constraint of [winckel-et-al-2025]: an extracted element should not be more
focused than its non-local governor. They state it gradiently, but with filler and governor both
carrying a binary `Mark` it reduces to the filler being focused where the governor is not. -/
def fbcRevisedViolation (filler governor : Mark) : Prop :=
  filler = .focused ∧ governor = .nonFocused

instance (a b : Mark) : Decidable (fbcRevisedViolation a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The revised constraint's prediction for a construction. -/
def fbcRevisedPredictsIsland (c : FGDConstruction) : Prop :=
  fbcRevisedViolation (fillerFocus c) (subjectFocus c)

instance (c : FGDConstruction) : Decidable (fbcRevisedPredictsIsland c) :=
  inferInstanceAs (Decidable (fbcRevisedViolation _ _))

/-- On these materials the two formulations are indistinguishable. -/
theorem both_fbcs_same_predictions (c : FGDConstruction) :
    fbcPredictsIsland c ↔ fbcRevisedPredictsIsland c := by
  cases c <;> decide

/-- Either constraint makes the island effect turn on the construction: present in wh-questions,
absent in relative clauses and topicalization. -/
theorem fbc_predicts_construction_dependence :
    fbcPredictsIsland .whQuestion ∧ ¬ fbcPredictsIsland .relativeClause ∧
      ¬ fbcPredictsIsland .topicalization := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### What the experiments show

All three experiments find a super-additive penalty for sub-extraction from a subject, and the
cross-constructional analysis puts the three penalties at comparable magnitude with overlapping
95% HPDIs (§7). Taking `Island` to be the effect's distribution over constructions, the finding is
that it holds of a construction whose filler is not focused. -/

/-- An island effect in relative clauses refutes the Focus Background Constraint, which ties the
effect to a focused filler. -/
theorem fbc_falsified (Island : FGDConstruction → Prop)
    (hfbc : ∀ c, Island c ↔ fbcPredictsIsland c) (h : Island .relativeClause) : False :=
  fbc_predicts_construction_dependence.2.1 ((hfbc _).1 h)

/-- And refutes the revised constraint, which predicts the same thing here. -/
theorem fbcRevised_falsified (Island : FGDConstruction → Prop)
    (hfbc : ∀ c, Island c ↔ fbcRevisedPredictsIsland c) (h : Island .relativeClause) : False :=
  fbc_predicts_construction_dependence.2.1
    ((both_fbcs_same_predictions _).2 ((hfbc _).1 h))

/-- The limit of the result. An account whose prediction reads only the extraction domain gives
the same verdict in every construction, since the design holds the domain fixed — so
construction-invariant effects are what it predicts, and the experiments do not bear on it. -/
theorem domain_only_predicts_invariance (P : BinaryGivenness → Prop) (c c' : FGDConstruction) :
    P (subjectGivenness c) ↔ P (subjectGivenness c') := Iff.rfl

end CartnerEtAl2026
