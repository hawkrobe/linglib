module

public import Linglib.Semantics.Focus.Marking

/-!
# Cartner et al. 2026: subject islands do not reduce to discourse function

This file formalizes the argument of [cartner-et-al-2026] against information-structural accounts
of the subject island. On the Focus Background Constraint of [abeille-et-al-2020] a subject island
is a clash between a focused filler and a backgrounded extraction domain, so the effect should
appear where the filler is focused and not otherwise: in wh-questions but not in relative clauses
or topicalization, whose fillers are not focused. Three factorial acceptability experiments
([sprouse-2007], [sprouse-et-al-2012]) find the effect in all three constructions and at
comparable magnitude, which no reading of the constraint accommodates. The revised, gradient
formulation of [winckel-et-al-2025], on which an extracted element should not be more focused
than its governor, makes the same prediction: both formulations place the filler and the
extraction domain on one scale, a backgrounded constituent being an unfocused one, so both
statuses are a `Focus.Mark`, and on binary marks the revision is the original constraint
(`fbcViolation_iff_lt`).

The design holds the extraction domain constant and varies the filler, so it bears only on
accounts that read the filler. An account whose prediction is a function of the domain alone —
direct backgroundedness ([cuneo-goldberg-2023]), or a structural constraint on the configuration —
predicts the same verdict in every construction and is untouched by the result, as the paper notes
(§8).

## Main definitions

* `FGDConstruction`, `fillerFocus`, `subjectFocus` — the three constructions, the filler's focus,
  which the design manipulates, and the subject's, which it holds fixed
* `FBCViolation`, `FBCPredictsIsland`, `FBCRevisedPredictsIsland` — the two formulations of
  the constraint

## Main results

* `fbcViolation_iff_lt` — on binary marks the revised constraint is the original one
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

@[expose] public section

namespace CartnerEtAl2026

open Focus (Mark)

/-! ### Filler-gap constructions and their information structure -/

/-- The three filler-gap constructions the experiments compare. They share the movement
mechanism and differ in the information-structural status of the filler. -/
inductive FGDConstruction where
  | whQuestion
  | relativeClause
  | topicalization
  deriving DecidableEq, Repr

/-- Focus marking of the filler: a wh-phrase is focused, a topicalized constituent is already
backgrounded in the discourse (§2), and relativization assigns its head no focus
([abeille-et-al-2020]). -/
def fillerFocus : FGDConstruction → Mark
  | .whQuestion => .focused
  | .relativeClause | .topicalization => .nonFocused

/-- Focus marking of the subject, the constituent containing the gap. Subjects are backgrounded,
that is unfocused, in all three constructions, which is what the design holds constant. -/
def subjectFocus : FGDConstruction → Mark
  | _ => .nonFocused

/-- The extraction domain is uniform across the three constructions, so any difference between
them is a difference in the filler. -/
theorem subjectFocus_uniform (c c' : FGDConstruction) : subjectFocus c = subjectFocus c' := rfl

/-- The filler is not: only the wh-question's is focused. This is the variable the constraint
claims should modulate the island effect. -/
theorem fillerFocus_varies :
    fillerFocus .whQuestion ≠ fillerFocus .relativeClause ∧
      fillerFocus .whQuestion ≠ fillerFocus .topicalization := by
  decide

/-! ### The Focus Background Constraint -/

/-- The Focus Background Constraint of [abeille-et-al-2020]: a focused element should not be part
of an unfocused, backgrounded constituent, so a focused filler extracted from an unfocused domain
violates it. -/
def FBCViolation (filler domain : Mark) : Prop :=
  filler = .focused ∧ domain = .nonFocused

instance : DecidableRel FBCViolation := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The revised constraint of [winckel-et-al-2025], that an extracted element should not be more
focused than its non-local governor, is the original one on binary marks. -/
theorem fbcViolation_iff_lt (filler domain : Mark) : FBCViolation filler domain ↔ domain < filler :=
  and_comm.trans Mark.lt_iff.symm

/-- The constraint's prediction for a construction. -/
def FBCPredictsIsland (c : FGDConstruction) : Prop :=
  FBCViolation (fillerFocus c) (subjectFocus c)

instance : DecidablePred FBCPredictsIsland :=
  fun _ ↦ inferInstanceAs (Decidable (FBCViolation _ _))

/-- The revised constraint's prediction for a construction: the filler is more focused than the
subject containing its gap. -/
def FBCRevisedPredictsIsland (c : FGDConstruction) : Prop :=
  subjectFocus c < fillerFocus c

instance : DecidablePred FBCRevisedPredictsIsland :=
  fun _ ↦ inferInstanceAs (Decidable (_ < _))

/-- On these materials the two formulations are indistinguishable. -/
theorem both_fbcs_same_predictions (c : FGDConstruction) :
    FBCPredictsIsland c ↔ FBCRevisedPredictsIsland c :=
  fbcViolation_iff_lt _ _

/-- Either constraint makes the island effect turn on the construction: present in wh-questions,
absent in relative clauses and topicalization. -/
theorem fbc_predicts_construction_dependence :
    FBCPredictsIsland .whQuestion ∧ ¬ FBCPredictsIsland .relativeClause ∧
      ¬ FBCPredictsIsland .topicalization := by
  decide

/-! ### What the experiments show

All three experiments find a super-additive penalty for sub-extraction from a subject, and the
cross-constructional analysis puts the three penalties at comparable magnitude with overlapping
95% HPDIs (§7). Taking `Island` to be the effect's distribution over constructions, the finding is
that it holds of a construction whose filler is not focused. -/

/-- An island effect in relative clauses refutes the Focus Background Constraint, which ties the
effect to a focused filler. -/
theorem fbc_falsified (Island : FGDConstruction → Prop)
    (hfbc : ∀ c, Island c ↔ FBCPredictsIsland c) (h : Island .relativeClause) : False :=
  fbc_predicts_construction_dependence.2.1 ((hfbc _).1 h)

/-- And refutes the revised constraint, which predicts the same thing here. -/
theorem fbcRevised_falsified (Island : FGDConstruction → Prop)
    (hfbc : ∀ c, Island c ↔ FBCRevisedPredictsIsland c) (h : Island .relativeClause) : False :=
  fbc_predicts_construction_dependence.2.1
    ((both_fbcs_same_predictions _).2 ((hfbc _).1 h))

/-- The limit of the result. An account whose prediction reads only the extraction domain gives
the same verdict in every construction, since the design holds the domain fixed — so
construction-invariant effects are what it predicts, and the experiments do not bear on it. -/
theorem domain_only_predicts_invariance (P : Mark → Prop) (c c' : FGDConstruction) :
    P (subjectFocus c) ↔ P (subjectFocus c') := Iff.rfl

end CartnerEtAl2026
