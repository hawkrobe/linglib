module

public import Linglib.Semantics.Conditionals.Counterfactual

/-!
# Stalnaker (1981): A Defense of Conditional Excluded Middle

This file formalizes [stalnaker-1981]'s defense of the selection-function analysis of
conditionals against [lewis-1973]'s comparative-similarity analysis. The two differ by the limit
assumption, that every possible antecedent has closest worlds, and the uniqueness assumption,
that it has at most one; in the logic of conditionals the first is the consequence condition
and the second is conditional excluded middle, which is equivalent to the distribution of a
conditional over a disjunctive consequent (`cem_iff_distribution`). Uniqueness is neutralized
by supervaluation: the selection functions in use correspond to orderings with ties, and a
conditional is true when every completion makes it true, so conditional excluded middle stays
valid while [quine-1950]'s two counterfactuals about Bizet and Verdi come out neither true nor
false rather than, as for Lewis, both false (`bizet_italian_indet`, `bizet_verdi_cem`,
`bizet_cem_fails_universal`); distribution likewise separates the analyses
(`distribution_needs_uniqueness`, `distribution_fails_bizetverdi`). Because Lewis's antecedents
are necessity operators, his analysis predicts a scope ambiguity between a quantifier inside
and outside a counterfactual, as with the woman President Carter would have appointed to the
Supreme Court; selection predicts none, the two scopes coinciding (`selection_scope`), and
indeterminacy rather than ambiguity explains why no particular woman would have been appointed
(`court_no_particular_woman`).

The limit assumption cannot be neutralized in the same way, and dropping it has bizarre
consequences: for [lewis-1973]'s line a little less than an inch long, Lewis's analysis makes
*if the line had been more than one inch long, it would not have been x inches long* true for
every length x, so that there is no length the line might have had, and the consequence
condition fails. Nothing turns on lengths: the same holds of any antecedent without closest
worlds (`lewisWould_ne`, `not_lewisMight_eq`, `not_consequence_lewisWould`). Finally,
Lewis's *might* as the dual of *would* collapses into *would* under conditional excluded
middle; reading *might* instead as a possibility operator over the whole conditional keeps
Lewis's formulation, *if A, might B* true exactly when *if A, would not-B* is not true, for a
possible antecedent (`selectionalMight_iff`), and separates *might* from *would* through
indeterminacy (`might_would_asymmetry`).

## Implementation notes

The conditional logic of the first section is abstract: a conditional operator on
propositions with right weakening, agglomeration and a valid tautological consequent, the
finite form of the consequence condition. The limit assumption is stated for an arbitrary
similarity ordering and antecedent without closest worlds, the situation of the line example,
rather than on a model of lengths. The selection-similarity
correspondence of the paper's opening, the Moore-paradoxical status of denying a *would* while
affirming a *might*, and the Kennedy example are not formalized.

## References

* [stalnaker-1981]
* [lewis-1973]
* [quine-1950]
* [van-fraassen-1966]
-/

@[expose] public section


namespace Stalnaker1981

open Conditional
open Conditional.Counterfactual

/-! ### Conditional excluded middle and distribution -/

section ConditionalLogic

variable {W : Type*} (cond : Set W → Set W → Set W)

/-- The finite consequence condition: a conditional operator weakens its consequent,
agglomerates consequents, and has every tautological consequent. -/
structure ConsequenceCondition : Prop where
  mono : ∀ A B C, B ⊆ C → cond A B ⊆ cond A C
  agg : ∀ A B C, cond A B ∩ cond A C ⊆ cond A (B ∩ C)
  taut : ∀ A, cond A Set.univ = Set.univ

/-- Conditional excluded middle: a conditional or its opposite holds everywhere. -/
def CEM : Prop := ∀ A B, cond A B ∪ cond A Bᶜ = Set.univ

/-- Distribution: a conditional with a disjunctive consequent yields one with a disjunct. -/
def Distribution : Prop := ∀ A B C, cond A (B ∪ C) ⊆ cond A B ∪ cond A C

/-- Under the consequence condition, conditional excluded middle and distribution are
equivalent. -/
theorem cem_iff_distribution (h : ConsequenceCondition cond) :
    CEM cond ↔ Distribution cond := by
  constructor
  · intro hcem A B C w hw
    rcases (Set.eq_univ_iff_forall.1 (hcem A B) w) with hB | hB
    · exact Or.inl hB
    · refine Or.inr (h.mono A (Bᶜ ∩ (B ∪ C)) C ?_ (h.agg A _ _ ⟨hB, hw⟩))
      rintro x ⟨hx, hxB | hxC⟩
      · exact absurd hxB hx
      · exact hxC
  · intro hdist A B
    refine Set.eq_univ_of_forall fun w ↦ hdist A B Bᶜ ?_
    rw [Set.union_compl_self, h.taut]
    trivial

end ConditionalLogic

/-! ### Selection: excluded middle and scope -/

section Selection

variable {W : Type*} (s : SelectionFunction W)

/-- A determinate selection function validates conditional excluded middle. -/
theorem selection_cem (A B : Set W) (w : W) :
    w ∈ selectionConditional s A B ∨ w ∈ selectionConditional s A Bᶜ :=
  selectionConditional_cem s

/-- Under selection, a quantifier inside the consequent and one outside the conditional
coincide for a possible antecedent: there is no scope ambiguity. -/
theorem selection_scope {ι : Type*} {A : Set W} (hA : A.Nonempty) (F : ι → Set W) (w : W) :
    w ∈ selectionConditional s A (⋃ x, F x) ↔ ∃ x, w ∈ selectionConditional s A (F x) := by
  simp only [mem_selectionConditional_of_nonempty s hA, Set.mem_iUnion]

end Selection

/-! ### Bizet and Verdi -/

section BizetVerdi

/-- The worlds of the Bizet–Verdi example: the actual world, and the two closest worlds in
which the composers are compatriots. -/
inductive BVWorld
  | actual | bothItalian | bothFrench
  deriving Repr, DecidableEq, Fintype

/-- The similarity ordering: the actual world is closest to itself, and the two compatriot
worlds tie. -/
def bvSim : SimilarityOrdering BVWorld := .ofBool
  (fun | .actual, .actual, _ => true
       | .actual, .bothItalian, .bothFrench => true
       | .actual, .bothFrench, .bothItalian => true
       | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)

/-- Bizet and Verdi are compatriots. -/
abbrev compatriots : Set BVWorld := {.bothItalian, .bothFrench}

/-- Bizet is Italian. -/
abbrev bizetItalian : Set BVWorld := {.bothItalian}

/-- Verdi is French. -/
abbrev verdiFrench : Set BVWorld := {.bothFrench}

/-- *If Bizet and Verdi had been compatriots, Bizet would have been Italian* is neither true
nor false: the closest compatriot worlds disagree. -/
theorem bizet_italian_indet :
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .indet := by decide

/-- *If Bizet and Verdi had been compatriots, Verdi would have been French* is neither true
nor false. -/
theorem verdi_french_indet :
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .indet := by decide

/-- Conditional excluded middle holds for the example under supervaluation: the disjunction of
the conditional and its opposite is not false. -/
theorem bizet_verdi_cem :
    selectionalCounterfactual bvSim compatriots bizetItalian .actual ⊔
      selectionalCounterfactual bvSim compatriots bizetItalianᶜ .actual ≠ .false :=
  cem_selectional bvSim compatriots bizetItalian .actual

/-- On the universal analysis both counterfactuals are false, and excluded middle fails. -/
theorem bizet_cem_fails_universal :
    .actual ∉ closestImp bvSim compatriots bizetItalian ∧
    .actual ∉ closestImp bvSim compatriots bizetItalianᶜ :=
  ⟨by decide, by decide⟩

/-- Quine's inference: *if they had been compatriots, Bizet would have been Italian or Verdi
French* is true on the universal analysis, but neither disjunct's conditional is, so
distribution fails. -/
theorem distribution_fails_bizetverdi :
    .actual ∈ closestImp bvSim compatriots (bizetItalian ∪ verdiFrench) ∧
    .actual ∉ closestImp bvSim compatriots bizetItalian ∧
    .actual ∉ closestImp bvSim compatriots verdiFrench :=
  ⟨by decide, by decide, by decide⟩

/-- Under supervaluation the disjunctive conditional is true while each disjunct's conditional
is indeterminate: distribution holds on every completion but not on the supervaluation, whose
closest worlds are not unique. -/
theorem distribution_needs_uniqueness :
    selectionalCounterfactual bvSim compatriots (bizetItalian ∪ verdiFrench) .actual
      = .true ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .indet ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .indet :=
  ⟨by decide, by decide, by decide⟩

end BizetVerdi

/-! ### The Supreme Court appointment -/

section Court

/-- The worlds of the appointment example: the actual world, with no vacancy, and two equally
close worlds in which a vacancy is filled by a different woman. -/
inductive CourtWorld
  | actual | w1 | w2
  deriving Repr, DecidableEq, Fintype

/-- The similarity ordering: the two vacancy worlds tie. -/
def courtSim : SimilarityOrdering CourtWorld := .ofBool
  (fun | .actual, .actual, _ => true
       | .actual, .w1, .w2 => true
       | .actual, .w2, .w1 => true
       | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)

/-- A vacancy occurs. -/
abbrev vacancy : Set CourtWorld := {.w1, .w2}

/-- The women who might be appointed. -/
inductive Woman
  | a | b
  deriving DecidableEq, Fintype

/-- Woman `a` is appointed in the first vacancy world, woman `b` in the second. -/
def appointed : Woman → Set CourtWorld
  | .a => {.w1}
  | .b => {.w2}

instance (x : Woman) : DecidablePred (· ∈ appointed x) := fun w ↦ by
  cases x <;> exact inferInstanceAs (Decidable (w = _))

instance : DecidablePred (· ∈ ⋃ x, appointed x) := fun w ↦
  decidable_of_iff (∃ x, w ∈ appointed x) Set.mem_iUnion.symm

/-- On the universal analysis the narrow scope, *he would have appointed some woman*, is true
while the wide scope, *some woman is such that he would have appointed her*, is false: a
scope ambiguity Lewis's analysis predicts and speakers do not perceive. -/
theorem court_scope_universal :
    .actual ∈ closestImp courtSim vacancy (⋃ x, appointed x) ∧
    ¬ ∃ x, .actual ∈ closestImp courtSim vacancy (appointed x) :=
  ⟨by decide, by decide⟩

/-- Under supervaluation the narrow scope is true while each woman's conditional is
indeterminate: there is no particular woman he would have appointed, by underdetermination
rather than ambiguity. -/
theorem court_no_particular_woman :
    selectionalCounterfactual courtSim vacancy (⋃ x, appointed x) .actual = .true ∧
    ∀ x, selectionalCounterfactual courtSim vacancy (appointed x) .actual = .indet :=
  ⟨by decide, by decide⟩

end Court

/-! ### The limit assumption -/

section Limit

variable {W : Type*} {sim : SimilarityOrdering W} {A : Set W} {w : W}

/-- Where an antecedent has no closest worlds, as for [lewis-1973]'s line more than an inch
long, *if A, it would not be x* is true on Lewis's analysis for every world `x`: below any
antecedent-world there is a closer one. -/
theorem lewisWould_ne (h : sim.closest w A = ∅) (x : W) : w ∈ variablyStrictImp sim A {x}ᶜ :=
  mem_variablyStrictImp_compl_singleton h x

/-- So there is no world the antecedent might have been, on Lewis's *might*. -/
theorem not_lewisMight_eq (h : sim.closest w A = ∅) (x : W) :
    w ∉ might (variablyStrictImp sim) A {x} :=
  notMem_might_variablyStrictImp_singleton h x

/-- Without the limit assumption the consequence condition fails: the consequents *not x*,
over all antecedent-worlds `x`, jointly entail *not A*, each conditional is true, and for a
possible antecedent the conditional with the entailed consequent is false. -/
theorem not_consequence_lewisWould (h : sim.closest w A = ∅) (hA : A.Nonempty) :
    (⋂ x ∈ A, ({x}ᶜ : Set W)) ⊆ Aᶜ ∧ (∀ x ∈ A, w ∈ variablyStrictImp sim A {x}ᶜ) ∧
      w ∉ variablyStrictImp sim A Aᶜ := by
  refine ⟨fun v hv hvA ↦ Set.mem_iInter₂.1 hv v hvA rfl, fun x _ ↦ lewisWould_ne h x, ?_⟩
  rintro (hA' | ⟨v, hv, hvc⟩)
  · exact hA.ne_empty hA'
  · exact hvc v hv (sim.closer_refl w v) hv

end Limit

/-! ### Might -/

section Might

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W) (A B : Set W)
  [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (w : W)

/-- *Might* as a possibility operator over the conditional keeps Lewis's formulation: *if A,
might B* is true exactly when *if A, would not-B* is not true. -/
theorem selectionalMight_iff (h : (sim.closest w A).Nonempty) :
    selectionalMight sim A B w ↔ selectionalCounterfactual sim A Bᶜ w ≠ .true := by
  obtain ⟨v, hv⟩ := h
  unfold selectionalMight selectionalCounterfactual
  simp only [compl_compl]
  split_ifs with h₁ h₂ h₃ <;> simp_all
  exact h₂ hv (h₁ hv)

/-- In the Bizet–Verdi example both *might* conditionals are true while both *would*
conditionals are indeterminate: *might* and *would* part, as they cannot on Lewis's dual
under excluded middle. -/
theorem might_would_asymmetry :
    selectionalMight bvSim compatriots bizetItalian .actual ∧
    selectionalMight bvSim compatriots verdiFrench .actual ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .indet ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .indet :=
  ⟨by decide, by decide, by decide, by decide⟩

end Might

end Stalnaker1981
