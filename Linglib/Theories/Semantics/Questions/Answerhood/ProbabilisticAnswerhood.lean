import Linglib.Core.FinitePMF
import Linglib.Core.QUD.Basic
import Linglib.Core.QUD.PrecisionProjection
import Linglib.Core.Issue.Basic
import Linglib.Core.Issue.Hamblin
import Linglib.Core.Issue.Relevance
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Mathlib.Algebra.Order.Field.Basic

/-!
# Probabilistic Answerhood @cite{thomas-2026}
@cite{groenendijk-stokhof-1984}

Answerhood in terms of probability changes, following @cite{thomas-2026}
"A probabilistic, question-based approach to additivity".

## Core Definitions

**Definition 61 - Relevance**: A proposition P is relevant to question Q iff
P changes the probability of some alternative:
```
Relevant(P, Q) ≡ ∃A ∈ Q: P(A|P) ≠ P(A)
```

**Definition 62 - Probabilistic Answerhood**: P probabilistically answers Q iff
P raises the probability of some alternative:
```
ProbAnswers(P, Q) ≡ ∃A ∈ Q: P(A|P) > P(A)
```

**Definition 63 - Evidences More Strongly**: R evidences A more strongly than R':
```
EvidencesMoreStrongly(R, R', A) ≡ P(A|info(R)) > P(A|info(R'))
```

These probabilistic notions of answerhood are central to Thomas's analysis
of additive particles like "too", "also", "either".

## API surface (Set/Prop)

All predicates operate on `Core.Issue W` (the mathlib-aligned downward-closed
inquisitive lattice) and `Set W` (with `[DecidablePred]` for computability),
in line with project-wide mathlib discipline.
-/

namespace Semantics.Questions.ProbabilisticAnswerhood

open Semantics.Questions

-- Conditional Probability Infrastructure

/-- A prior distribution as a normalized mass function over worlds.

Bundled with non-negativity and normalization (∑ w, mass w = 1) proofs
via `Core.FinitePMF`. Use `prior w` to access the mass at world `w`
(via `CoeFun`). -/
abbrev Prior (W : Type*) [Fintype W] := Core.FinitePMF W

/-! ## Set/Prop API — full mathlib alignment

Predicates operate on `Core.Issue W` (with `[HasAltList]` for finiteness witness)
and `Set W` (with `[DecidablePred]`) as the canonical types.

The relationship to FinitePMF:
- `prior.probOfSet (s : Set W) [DecidablePred (· ∈ s)]` — P(s)
- `prior.condProbSet (cond target : Set W) [...] [...]` — P(target | cond)
-/

open Classical in
/-- Probabilistic relevance: `s` changes the probability of some alternative
of `q`. @cite{thomas-2026} Def. 61. -/
noncomputable def relevantS {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Issue W) (prior : Prior W) : Prop :=
  ∃ a ∈ Core.Issue.alt q, prior.condProbSet s a ≠ prior.probOfSet a

open Classical in
/-- Probabilistic answerhood: `s` raises the probability of some alternative
of `q`. @cite{thomas-2026} Def. 62 condition (a). -/
noncomputable def probAnswersS {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Issue W) (prior : Prior W) : Prop :=
  ∃ a ∈ Core.Issue.alt q, prior.condProbSet s a > prior.probOfSet a

/-- Probabilistic answerhood implies relevance. -/
theorem probAnswersS_implies_relevantS {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Issue W) (prior : Prior W)
    (h : probAnswersS s q prior) : relevantS s q prior := by
  obtain ⟨a, ha, hgt⟩ := h
  exact ⟨a, ha, ne_of_gt hgt⟩

/-- Entailing an alternative guarantees probabilistic answerhood.

If `s ⊆ a` for some alternative `a` of `q`, and `s` has positive prior and
`a` is not already certain, then learning `s` raises `a`'s probability to
1, exceeding `P(a) < 1`. The Classical instances baked into `probAnswersS`
agree with user-supplied `[DecidablePred]` instances by `Subsingleton`. -/
theorem probAnswersS_when_entailing {W : Type*} [Fintype W] [DecidableEq W]
    (s : Set W) (q : Core.Issue W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Issue.alt q)
    (hEntails : s ⊆ a)
    (hPosS : prior.probOfSet s > 0)
    (hNotCertain : prior.probOfSet a < 1) :
    probAnswersS s q prior := by
  refine ⟨a, hAltMem, ?_⟩
  -- s ⊆ a ⟹ s ∩ a = s, so condProbSet s a = probOfSet s / probOfSet s = 1 > probOfSet a.
  have hSA : prior.probOfSet (s ∩ a) = prior.probOfSet s := by
    unfold Core.FinitePMF.probOfSet
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hw : w ∈ s
    · simp [hw, Set.mem_inter_iff, hEntails hw]
    · simp [hw, Set.mem_inter_iff]
  have hCond : prior.condProbSet s a = 1 := by
    rw [prior.condProbSet_of_pos s a hPosS, hSA]
    exact div_self (ne_of_gt hPosS)
  have hGt : prior.condProbSet s a > prior.probOfSet a := by
    rw [hCond]; exact hNotCertain
  convert hGt

/-- Evidential boost: how much `evidence` raises the probability of `conclusion`.
Returns ℚ. -/
def evidentialBoostS {W : Type*} [Fintype W]
    (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] : ℚ :=
  prior.condProbSet evidence conclusion - prior.probOfSet conclusion

/-- Evidence is positive iff its boost is strictly positive. -/
def isPositiveEvidenceS {W : Type*} [Fintype W]
    (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] : Prop :=
  evidentialBoostS evidence conclusion prior > 0

/-- Evidence is negative iff its boost is strictly negative. -/
def isNegativeEvidenceS {W : Type*} [Fintype W]
    (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] : Prop :=
  evidentialBoostS evidence conclusion prior < 0

instance {W : Type*} [Fintype W] (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] :
    Decidable (isPositiveEvidenceS evidence conclusion prior) :=
  inferInstanceAs (Decidable (_ > _))

instance {W : Type*} [Fintype W] (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] :
    Decidable (isNegativeEvidenceS evidence conclusion prior) :=
  inferInstanceAs (Decidable (_ < _))

/-- Evidence-strength comparison: `r` evidences `a` more strongly than `r'`
iff `P(a | r) > P(a | r')`. @cite{thomas-2026} Def. 63. -/
def evidencesMoreStronglyS {W : Type*} [Fintype W]
    (r r' a : Set W) (prior : Prior W)
    [DecidablePred (· ∈ r)] [DecidablePred (· ∈ r')] [DecidablePred (· ∈ a)] :
    Prop :=
  prior.condProbSet r a > prior.condProbSet r' a

instance {W : Type*} [Fintype W] (r r' a : Set W) (prior : Prior W)
    [DecidablePred (· ∈ r)] [DecidablePred (· ∈ r')] [DecidablePred (· ∈ a)] :
    Decidable (evidencesMoreStronglyS r r' a prior) :=
  inferInstanceAs (Decidable (_ > _))

/-! ### Conjunction strengthening

The core notion in @cite{thomas-2026}'s analysis of additive particles:
the conjunction `p1 ∩ p2` evidences `conclusion` more strongly than `p1`
alone. -/

/-- Conjunction `p1 ∩ p2` evidences `conclusion` more strongly than `p1`. -/
def conjunctionStrengthensS {W : Type*} [Fintype W]
    (p1 p2 conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ p1)] [DecidablePred (· ∈ p2)]
    [DecidablePred (· ∈ conclusion)] : Prop :=
  haveI : DecidablePred (· ∈ (p1 ∩ p2)) := by
    intro w; exact inferInstanceAs (Decidable (_ ∧ _))
  evidencesMoreStronglyS (p1 ∩ p2) p1 conclusion prior

instance {W : Type*} [Fintype W] (p1 p2 conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ p1)] [DecidablePred (· ∈ p2)]
    [DecidablePred (· ∈ conclusion)] :
    Decidable (conjunctionStrengthensS p1 p2 conclusion prior) := by
  unfold conjunctionStrengthensS
  exact inferInstance

open Classical in
/-- Some alternative of `q` is strengthened by adding `p2` to `p1`.

Spec uses `Classical.dec` for per-alternative decidability so the predicate
body is well-typed without an `[∀ a, DecidablePred (· ∈ a)]` hypothesis.
For computable `Decidable` instances at concrete consumers, supply the
per-alternative `[DecidablePred]` and use `decide` directly. -/
noncomputable def someResolutionStrengthenedS {W : Type*} [Fintype W]
    (p1 p2 : Set W) (q : Core.Issue W) (prior : Prior W) : Prop :=
  ∃ a ∈ Core.Issue.alt q, prior.condProbSet (p1 ∩ p2) a > prior.condProbSet p1 a

/-! ### Witness constructors — Classical/structural Decidable bridge

The three predicates above are `noncomputable` and use `open Classical in`
so that the spec body type-checks without per-alternative `[DecidablePred]`
hypotheses. Concrete consumers compute probability values with their own
structural `[DecidablePred]` instances; the two instance choices agree
because `Decidable` is a `Subsingleton`.

These `of_witness` lemmas absorb the `convert h` boilerplate that
otherwise appears at every consumer site. The pattern at the call site is:

```lean
refine probAnswersS.of_witness s q prior a hAltMem ?_
rw [my_cond_lemma, my_prob_lemma]; norm_num
```

instead of the more verbose:

```lean
refine ⟨a, hAltMem, ?_⟩
have h : prior.condProbSet s a > prior.probOfSet a := by
  rw [my_cond_lemma, my_prob_lemma]; norm_num
convert h
```

For destructuring (the negative direction in infelicity proofs), the
`convert hStr` idiom remains: the destructured hypothesis carries
Classical instances and must be bridged back to user-supplied structural
instances at use sites. -/

/-- Constructive witness for `relevantS`: produce an alternative `a` and a
    probability shift, computed using user-supplied `[DecidablePred]`
    instances. The Classical instances inside the spec match by
    `Subsingleton (Decidable _)`. -/
lemma relevantS.of_witness {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Issue W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Issue.alt q)
    (h : prior.condProbSet s a ≠ prior.probOfSet a) :
    relevantS s q prior :=
  ⟨a, hAltMem, by convert h⟩

/-- Constructive witness for `probAnswersS`: produce an alternative `a`
    that is strictly raised by `s`. -/
lemma probAnswersS.of_witness {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Issue W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Issue.alt q)
    (h : prior.condProbSet s a > prior.probOfSet a) :
    probAnswersS s q prior :=
  ⟨a, hAltMem, by convert h⟩

/-- Constructive witness for `someResolutionStrengthenedS`: produce an
    alternative `a` whose conditional probability strictly increases when
    `p2` is added to `p1`. -/
lemma someResolutionStrengthenedS.of_witness {W : Type*} [Fintype W]
    (p1 p2 : Set W) (q : Core.Issue W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ p1)] [DecidablePred (· ∈ p2)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Issue.alt q)
    (h : prior.condProbSet (p1 ∩ p2) a > prior.condProbSet p1 a) :
    someResolutionStrengthenedS p1 p2 q prior := by
  haveI : DecidablePred (· ∈ p1 ∩ p2) :=
    fun w => inferInstanceAs (Decidable (_ ∧ _))
  exact ⟨a, hAltMem, by convert h⟩

end Semantics.Questions.ProbabilisticAnswerhood
