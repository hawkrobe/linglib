module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.Counting

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations

Ladusaw's licensing condition says that a negative polarity item is acceptable only in the scope of
a downward-entailing expression, one that reverses entailment among its arguments, so that the
affective environments of the earlier literature are characterized rather than listed. Every
environment credited to the dissertation denotes a downward-entailing operator
(`cited_environments_de`), questions do not (`question_not_de`), and a downward-entailing
environment licenses the weak polarity items (`ladusaw_generalization`). The determiners behind
three of these environments are downward entailing in exactly the argument where they license:
*no* in its scope and its restrictor, *few* in its scope, and *every* in its restrictor but not its
scope (`determiner_monotonicity`).

## Implementation notes

* Ladusaw reads a conditional antecedent as the antecedent of a material conditional, which is
  downward entailing (`materialAntecedent`); the library's `LicensingContext.conditionalAntecedent`
  is von Fintel's counterfactual, downward entailing only modulo its presupposition.
* The dissertation's scan in the library has no text layer; `environments` is the list the library
  credits to it. The anti-additive licensers and the strong polarity items postdate the
  dissertation, and questions license weak items by another route, so the converse of the
  generalization is not stated.

## References

* [ladusaw-1979]
-/

@[expose] public section

namespace Ladusaw1979

open PolarityItem NaturalLogic Quantifier Quantifier.GQ LicensingContext Licenser

/-- An environment is downward entailing when the operator it denotes reverses entailment. -/
def IsDownwardEntailing (c : LicensingContext) : Prop := c.licenser.Holds .anti

/-- A conditional's consequent, over worlds. -/
structure Consequent where
  /-- The worlds. -/
  W : Type
  /-- The consequent. -/
  q : Set W

/-- The antecedent of a material conditional, Ladusaw's reading of conditional antecedents. -/
def materialAntecedent : LicensingContext :=
  ⟨.classical ⟨Consequent, fun p ↦ Set p.W, fun p ↦ Set p.W, fun p P ↦ Pᶜ ∪ p.q⟩,
    some .conditional⟩

theorem isDownwardEntailing_materialAntecedent : IsDownwardEntailing materialAntecedent :=
  fun _ ↦ Signature.holdsFor_anti_iff.mpr fun _ _ h ↦ Set.union_subset_union_left _
    (Set.compl_subset_compl.mpr h)

-- UNVERIFIED: the list is the library's record, not checked against the dissertation.
/-- The licensing environments credited to the dissertation are negation, negative quantifiers,
*without*, the restrictor of a universal, *few*, *at most*, the antecedent of a conditional,
*before*, *too … to*, and the clausal comparative. -/
def environments : List LicensingContext :=
  [.negation, .nobody, .withoutClause, .universalRestrictor, .few, .atMost, materialAntecedent,
    .beforeClause, .tooTo, .clausalComparative]

/-- Every environment credited to the dissertation is downward entailing. -/
theorem cited_environments_de : ∀ c ∈ environments, IsDownwardEntailing c := by
  simp only [environments, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨holds_negation .weak, (holds_nobody_iff (s := .weak)).2 (by decide),
    (holds_withoutClause_iff (s := .weak)).2 (by decide),
    (holds_universalRestrictor_iff (s := .weak)).2 (by decide), holds_few_iff.2 le_rfl,
    holds_atMost_iff.2 le_rfl, isDownwardEntailing_materialAntecedent,
    (holds_beforeClause_iff (s := .weak)).2 (by decide),
    (holds_tooTo_iff (s := .weak)).2 (by decide),
    (holds_clausalComparative_iff (s := .weak)).2 (by decide)⟩

/-- Questions are not downward entailing. -/
theorem question_not_de : ¬ IsDownwardEntailing .question := id

/-- A downward-entailing environment licenses the weak polarity items, the dissertation's
generalization, which the library takes as its definition of licensing by strengthening. -/
theorem ladusaw_generalization (c : LicensingContext) (hc : IsDownwardEntailing c)
    (e : PolarityItem) (he : e.licensor = some .weak) : c.Licenses e :=
  .inl ⟨.weak, he, isStrawsonDE_of_holds_anti hc⟩

variable {α : Type*}

/-- *no* reverses entailment in both arguments, *few* in its scope, and *every* in its restrictor
but not its scope, which is where each licenses a polarity item. -/
theorem determiner_monotonicity [Fintype α] [Nonempty α] :
    ScopeAntitone (no : GQ α) ∧ RestrictorAntitone (no : GQ α) ∧ ScopeAntitone (few : GQ α) ∧
      RestrictorAntitone (every : GQ α) ∧ ¬ ScopeAntitone (every : GQ α) :=
  ⟨scopeAntitone_no, restrictorAntitone_no, scopeAntitone_few, restrictorAntitone_every,
    not_scopeAntitone_every⟩

end Ladusaw1979
