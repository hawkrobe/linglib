import Linglib.Semantics.Genericity.Basic
import Linglib.Semantics.Quantification.Counting

/-!
# [cohen-1999a]: Probability-Based Generic Quantification

Ariel Cohen, *Think Generic! The Meaning and Use of Generic Sentences*, 1999.

## Core Proposal

Cohen proposes that the generic quantifier GEN is a probability operator:

    GEN(P, Q) is true iff P(Q | P) > 0.5

That is, a generic "Ps are Q" is true iff the conditional probability of
an object having property Q, given that it has property P, exceeds 0.5.

This contrasts with the frequency adverb *always*, which requires
P(Q | P) = 1.

## Connection to Threshold Semantics

Cohen's GEN is a special case of threshold semantics with θ = 1/2. The
conditional probability P(Q | P) is `prevalenceOn` (the proportion of
restrictor-satisfying elements where the scope holds — the analogue of
`Rel.edgeDensity`), and `cohenGEN` is `prevalenceOn > 1/2`. The
division-free, kernel-decidable cross-multiplied form is
`thresholdGtOn _ _ _ 1 2`; the two agree (`cohen_iff_thresholdGt`).

## Homogeneity Constraint

Cohen introduces a **homogeneity** presupposition: the conditional
probability P(Q | P) must be uniform across all suitable partitions
of the domain. If the domain splits into subgroups with different
rates, the generic presupposition fails and the sentence is neither
true nor false.

This constraint is discussed in the introduction to *Genericity*
(Mari, Beyssade, Del Prete, OUP 2013):

> "A homogeneity requirement is introduced as a presupposition of
> generics and frequency statements, according to which the relative
> probability in every part of a suitable partition of any admissible
> history H must be the same as the probability in the whole H."

## Nickel's Critique ([nickel-2009])

[nickel-2009] shows that even with homogeneity, the majority-based
view cannot handle conjunctive generics like "Elephants live in Africa
and Asia." If this is equivalent to the conjunction "Elephants live in
Africa AND Elephants live in Asia," then both conjuncts would need to
hold with probability > 0.5, which is impossible if the populations
are disjoint. See `Studies/Nickel2009.lean`, which states the
divergence as a theorem against `cohenGEN`.
-/

namespace Cohen1999

open Semantics.Genericity (Situation)
open Quantification (prevalenceOn countOn everyOn thresholdGtOn thresholdGtOn_iff_prevalenceOn
  mostOn thresholdGtOn_one_two_iff_mostOn Proportional mostOn_univ_proportional
  count count_decompose)

/-! ### Cohen's Probability-Based GEN

The operators are polymorphic over the domain carrier (`prevalenceOn` is), so
the same `cohenGEN` applies to situation-based models (here) and entity-based
models ([nickel-2009]). -/

/-- Cohen's GEN: a generic "Ps are Q" is true iff the conditional probability
    P(Q | P) exceeds 0.5. `prevalenceOn domain restrictor scope` is that
    conditional probability, so Cohen's GEN is `prevalenceOn > 1/2`. -/
def cohenGEN {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] : Prop :=
  prevalenceOn domain restrictor scope > 1 / 2

instance {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] :
    Decidable (cohenGEN domain restrictor scope) := by unfold cohenGEN; infer_instance

/-- Cohen's GEN agrees with the division-free, kernel-decidable threshold form
    `thresholdGtOn … 1 2` whenever the restrictor is satisfied somewhere. -/
theorem cohen_iff_thresholdGt {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] (hR : 0 < countOn domain restrictor) :
    cohenGEN domain restrictor scope ↔ thresholdGtOn domain restrictor scope 1 2 := by
  rw [cohenGEN, thresholdGtOn_iff_prevalenceOn domain restrictor scope 1 2 (by norm_num) hR]
  norm_num

/-! ### Cohen's GEN is proportional majority quantification

Cohen's θ = 1/2 GEN is, over a non-empty restrictor domain, **exactly** the
canonical majority quantifier `mostOn` — the θ = 1/2 threshold is the cutpoint
*at* the `1 : 1` cell ratio. It therefore inherits `Proportional` from the GQ
substrate. This is the precise content of "generics as majority quantification"
— and exactly the claim the genericity literature rejects: real generics are
**not** majority statements (`cohen_wrong_on_mosquitoes`; [nickel-2009];
[leslie-2008]; [tessler-goodman-2019]). The theorems below state what is *true
of Cohen's operator*, not of generics in general. -/

/-- Cohen's GEN over a non-empty restrictor domain is exactly the canonical
    majority quantifier `mostOn` (strictly more `R∧S` than `R∧¬S`): θ = 1/2 is
    the `1 : 1` cell-ratio cutpoint (`thresholdGtOn_one_two_iff_mostOn`). -/
theorem cohen_iff_mostOn {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] (hR : 0 < countOn domain restrictor) :
    cohenGEN domain restrictor scope ↔ mostOn domain restrictor scope :=
  (cohen_iff_thresholdGt domain restrictor scope hR).trans
    (thresholdGtOn_one_two_iff_mostOn domain restrictor scope)

open Classical in
/-- Cohen's majority GEN over the whole (finite) carrier is a **proportional**
    quantifier ([peters-westerstahl-2006]): its truth depends only on the ratio
    |R∩S| : |R∖S|. Inherited from `mostOn_univ_proportional` via `cohen_iff_mostOn`,
    not re-proved.

    This proportionality is a property of Cohen's *majority* operator, **not** of
    generics in general — the prevalence asymmetry ([leslie-2008];
    `TesslerGoodman2019.same_prevalence_opposite_endorsement`) shows real generic
    endorsement is *not* ratio-determined. -/
theorem cohen_proportional {α : Type*} [Fintype α] :
    Proportional (fun (R S : α → Prop) => cohenGEN Finset.univ R S) := by
  intro R₁ S₁ R₂ S₂ tt₁ tf₁ tt₂ tf₂ h1 h2 hcross
  show cohenGEN Finset.univ R₁ S₁ ↔ cohenGEN Finset.univ R₂ S₂
  have hR1 : 0 < countOn Finset.univ R₁ := by
    show 0 < count (fun x => R₁ x); rw [count_decompose R₁ S₁]; exact h1
  have hR2 : 0 < countOn Finset.univ R₂ := by
    show 0 < count (fun x => R₂ x); rw [count_decompose R₂ S₂]; exact h2
  rw [cohen_iff_mostOn Finset.univ R₁ S₁ hR1, cohen_iff_mostOn Finset.univ R₂ S₂ hR2]
  exact mostOn_univ_proportional R₁ S₁ R₂ S₂ h1 h2 hcross

/-! ### Generic-quantifier interface

`cohenGEN` over the whole carrier IS the majority generalized quantifier
`Quantification.most_sem`, slotting Cohen's absolute reading into the `GQ`
framework (`Quantification.Generic`) alongside `genNormalcy` / `genWays`. -/

/-- Cohen's absolute-reading GEN over the whole carrier is exactly the majority
    generalized quantifier `most_sem` — the `GQ`-interface form of `cohenGEN`.
    The bare `P(Q | P) > ½` truth condition only: the homogeneity presupposition
    (`homogeneous`) and the relative reading are not part of it. -/
theorem cohenGEN_univ_eq_most_sem {α : Type*} [Fintype α] (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] (hR : 0 < countOn Finset.univ R) :
    cohenGEN Finset.univ R S ↔ Quantification.most_sem R S := by
  rw [cohen_iff_mostOn Finset.univ R S hR, Quantification.mostOn_univ]

/-- Cohen's "always": no exceptions — every restrictor-element satisfies the scope.
    For a non-empty restrictor domain this is exactly P(Q | P) = 1; stated as the
    decidable universal `everyOn` rather than the (non-kernel-decidable) ℚ equality. -/
def cohenAlways {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] : Prop :=
  everyOn domain restrictor scope

instance {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] :
    Decidable (cohenAlways domain restrictor scope) := by unfold cohenAlways; infer_instance

/-! ### Homogeneity Constraint -/

/-- Cohen's homogeneity constraint: the conditional probability P(scope | restrictor)
    must be the same in every non-empty sub-partition of the domain.

    Formally: for any sub-predicate `part`, if there are restrictor-satisfying
    elements in that partition, the proportion of scope-satisfying elements among
    `restrictor ∧ part` elements equals the overall proportion among `restrictor`
    elements — i.e. P(Q | P ∧ Pᵢ) = P(Q | P) for all partition cells Pᵢ.

    When homogeneity fails, the generic presupposition fails and the sentence
    is neither true nor false. -/
def homogeneous {α : Type*} (domain : Finset α) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope] : Prop :=
  ∀ (part : α → Prop) [DecidablePred part],
    0 < countOn domain (fun x => restrictor x ∧ part x) →
    prevalenceOn domain (fun x => restrictor x ∧ part x) scope =
    prevalenceOn domain restrictor scope

/-- A generic assertion according to Cohen: the prevalence exceeds 0.5
    AND the homogeneity presupposition is satisfied. -/
structure CohenGenericJudgment (α : Type*) where
  domain : Finset α
  restrictor : α → Prop
  scope : α → Prop
  [restrictorDec : DecidablePred restrictor]
  [scopeDec : DecidablePred scope]
  holds : Prop := @cohenGEN α domain restrictor scope restrictorDec scopeDec
  presupposition : Prop := @homogeneous α domain restrictor scope restrictorDec scopeDec

/-! ### Examples -/

section DogsBark

/-- Ten situations: 8 with a barking dog, 2 with a sleeping dog. -/
def dogSituations : Finset Situation :=
  ((List.range 10).map (fun n => (⟨n⟩ : Situation))).toFinset

abbrev isDog : Situation → Prop := fun _ => True

abbrev barks : Situation → Prop := fun s => s.id < 8

/-- The data: 8 of 10 dog-cases bark (prevalence 8/10 = 4/5). -/
example : countOn dogSituations (fun s => isDog s ∧ barks s) = 8 ∧
    countOn dogSituations isDog = 10 := by decide

/-- "Dogs bark" is true on Cohen's account: prevalence 8/10 > 1/2. -/
example : cohenGEN dogSituations isDog barks :=
  (cohen_iff_thresholdGt dogSituations isDog barks (by decide)).mpr (by decide)

/-- "Dogs always bark" is false: cases 8 and 9 don't bark. -/
example : ¬ cohenAlways dogSituations isDog barks := by decide

end DogsBark

section BirdsFly

/-- Ten cases: 8 flying, 2 non-flying (penguins, ostriches). -/
def birdSituations : Finset Situation :=
  ((List.range 10).map (fun n => (⟨n⟩ : Situation))).toFinset

abbrev isBird : Situation → Prop := fun _ => True

abbrev flies : Situation → Prop := fun s => s.id < 8

/-- "Birds fly" is true: prevalence 8/10 > 1/2. -/
example : cohenGEN birdSituations isBird flies :=
  (cohen_iff_thresholdGt birdSituations isBird flies (by decide)).mpr (by decide)

end BirdsFly

/-! ### Cohen GEN vs the relativized universal -/

/-- When the relativized universal is true (all normal restrictor-cases satisfy
    scope) and the restrictor cases are a majority, Cohen's GEN is also true.
    Agreement in the typical case. -/
theorem everyOn_true_majority_implies_cohen {α : Type*}
    (domain : Finset α) (normal restrictor scope : α → Prop)
    [DecidablePred normal] [DecidablePred restrictor] [DecidablePred scope]
    (_hUniv : everyOn domain (fun x => normal x ∧ restrictor x) scope)
    (hMajority : prevalenceOn domain restrictor scope > 1 / 2)
    : cohenGEN domain restrictor scope := hMajority

/-!
## Cohen's Advantage over Traditional GEN

Traditional GEN has a hidden **normalcy** parameter that does all the
explanatory work. Cohen's probability-based GEN eliminates this parameter:
the threshold 0.5 is fixed, and the truth value is determined by observable
prevalence.

However, Cohen's approach faces its own challenges:

1. **Rare property generics**: "Mosquitoes carry malaria" is judged true
   despite prevalence well below 50%.

2. **Conjunctive generics**: [nickel-2009]'s "Elephants live in Africa
   and Asia" shows the majority-based view predicts the wrong truth conditions
   for conjoined habitat claims.

3. **Striking property generics**: "Sharks attack swimmers" — low prevalence
   but judged true. [tessler-goodman-2019]'s RSA account handles this
   via pragmatic reasoning over priors, not a fixed threshold.
-/

section RareProperty

/-- Ten cases: only 1 carries malaria (a low-prevalence property). -/
def mosquitoSituations : Finset Situation :=
  ((List.range 10).map (fun n => (⟨n⟩ : Situation))).toFinset

abbrev isMosquito : Situation → Prop := fun _ => True

abbrev carriesMalaria : Situation → Prop := fun s => s.id = 0

/-- "Mosquitoes carry malaria" is FALSE on Cohen's account (prevalence 1/10 < 1/2),
    even though speakers judge it true. -/
example : ¬ cohenGEN mosquitoSituations isMosquito carriesMalaria := by
  rw [cohen_iff_thresholdGt mosquitoSituations isMosquito carriesMalaria (by decide)]
  decide

/-- Cohen's prediction conflicts with empirical judgments ([leslie-2008]):
    "Mosquitos carry malaria" has prevalence ~1/100 but judgment ~85/100 (clearly
    true). Cohen predicts false (1/100 < 1/2). -/
theorem cohen_wrong_on_mosquitoes :
    (1 : ℚ) / 100 < 1 / 2 ∧ (85 : ℚ) / 100 > 1 / 2 := by
  constructor <;> norm_num

end RareProperty

section HomogeneityFailure

/-- A domain that VIOLATES homogeneity: urban vs rural dogs.
    Urban dogs bark more (all 5 bark), rural dogs bark less (1 of 5 barks).
    Overall prevalence = 6/10, but the partition into urban/rural shows
    different rates (5/5 vs 1/5). -/
def mixedDogSituations : Finset Situation :=
  ((List.range 10).map (fun n => (⟨n⟩ : Situation))).toFinset

abbrev allDogs : Situation → Prop := fun _ => True

-- barks iff urban (id<5, all bark) or the one rural barker (id=5): i.e. id < 6
abbrev mixedBarks : Situation → Prop := fun s => s.id < 6

abbrev urbanPartition : Situation → Prop := fun s => s.id < 5

/-- The data: overall 6/10 bark; urban cell 5/5; rural cell 1/5. -/
example : countOn mixedDogSituations (fun s => allDogs s ∧ mixedBarks s) = 6 ∧
    countOn mixedDogSituations allDogs = 10 ∧
    countOn mixedDogSituations (fun s => (allDogs s ∧ urbanPartition s) ∧ mixedBarks s) = 5 ∧
    countOn mixedDogSituations (fun s => allDogs s ∧ urbanPartition s) = 5 := by decide

/-- The generic "Dogs bark" passes Cohen's > 1/2 test (overall 6/10). -/
example : cohenGEN mixedDogSituations allDogs mixedBarks :=
  (cohen_iff_thresholdGt mixedDogSituations allDogs mixedBarks (by decide)).mpr (by decide)

/-- ...but homogeneity FAILS: the urban rate (5/5) differs from the overall rate
    (6/10), witnessed by cross-multiplication `5·10 ≠ 6·5`. -/
theorem homogeneity_fails_mixed :
    countOn mixedDogSituations (fun s => (allDogs s ∧ urbanPartition s) ∧ mixedBarks s) *
      countOn mixedDogSituations allDogs ≠
    countOn mixedDogSituations (fun s => allDogs s ∧ mixedBarks s) *
      countOn mixedDogSituations (fun s => allDogs s ∧ urbanPartition s) := by decide

end HomogeneityFailure

end Cohen1999
