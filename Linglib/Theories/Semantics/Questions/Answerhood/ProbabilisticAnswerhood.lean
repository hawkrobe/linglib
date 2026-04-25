import Linglib.Core.Probability.PMFFin
import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Question.Basic
import Linglib.Core.Question.Hamblin
import Linglib.Core.Question.Relevance
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy

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

## API surface (Set/Prop, ENNReal-valued)

All predicates operate on `Core.Question W` (the mathlib-aligned downward-closed
inquisitive lattice) and `Set W` (with `[DecidablePred]` for computability),
in line with project-wide mathlib discipline. Probabilities are mathlib
`PMF`-valued (`ℝ≥0∞`); comparisons are `Prop` (no `Decidable` instances —
ENNReal `<`/`>` is not constructively decidable).
-/

namespace Semantics.Questions.ProbabilisticAnswerhood

open Semantics.Questions
open scoped ENNReal

-- Conditional Probability Infrastructure

/-- A prior distribution as a mathlib `PMF` over a finite world type.

`PMF W` bundles a mass function `W → ℝ≥0∞` together with the
normalization proof. Use `prior w` to access the mass at world `w`
(via `CoeFun`). -/
abbrev Prior (W : Type*) [Fintype W] := PMF W

/-! ## Set/Prop API — full mathlib alignment

Predicates operate on `Core.Question W` (with `[HasAltList]` for finiteness witness)
and `Set W` (with `[DecidablePred]`) as the canonical types.

The relationship to `PMF`:
- `prior.probOfSet (s : Set W) [DecidablePred (· ∈ s)]` — P(s)
- `prior.condProbSet (cond target : Set W) [...] [...]` — P(target | cond)

(see `Linglib.Core.Probability.PMFFin`). -/

open Classical in
/-- Probabilistic relevance: `s` changes the probability of some alternative
of `q`. @cite{thomas-2026} Def. 61. -/
noncomputable def relevantS {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Question W) (prior : Prior W) : Prop :=
  ∃ a ∈ Core.Question.alt q, prior.condProbSet s a ≠ prior.probOfSet a

open Classical in
/-- Probabilistic answerhood: `s` raises the probability of some alternative
of `q`. @cite{thomas-2026} Def. 62 condition (a). -/
noncomputable def probAnswersS {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Question W) (prior : Prior W) : Prop :=
  ∃ a ∈ Core.Question.alt q, prior.condProbSet s a > prior.probOfSet a

/-- Probabilistic answerhood implies relevance. -/
theorem probAnswersS_implies_relevantS {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Question W) (prior : Prior W)
    (h : probAnswersS s q prior) : relevantS s q prior := by
  obtain ⟨a, ha, hgt⟩ := h
  exact ⟨a, ha, ne_of_gt hgt⟩

/-- Entailing an alternative guarantees probabilistic answerhood.

If `s ⊆ a` for some alternative `a` of `q`, and `s` has positive prior and
`a` is not already certain, then learning `s` raises `a`'s probability to
1, exceeding `P(a) < 1`. The Classical instances baked into `probAnswersS`
agree with user-supplied `[DecidablePred]` instances by `Subsingleton`. -/
theorem probAnswersS_when_entailing {W : Type*} [Fintype W] [DecidableEq W]
    (s : Set W) (q : Core.Question W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Question.alt q)
    (hEntails : s ⊆ a)
    (hPosS : prior.probOfSet s > 0)
    (hNotCertain : prior.probOfSet a < 1) :
    probAnswersS s q prior := by
  refine ⟨a, hAltMem, ?_⟩
  -- s ⊆ a ⟹ s ∩ a = s, so condProbSet s a = probOfSet s / probOfSet s = 1 > probOfSet a.
  have hSA : prior.probOfSet (s ∩ a) = prior.probOfSet s :=
    congrArg prior.probOfSet (Set.inter_eq_left.mpr hEntails)
  have hCond : prior.condProbSet s a = 1 := by
    rw [PMF.condProbSet_eq_div, hSA]
    exact ENNReal.div_self hPosS.ne' (PMF.probOfSet_ne_top prior s)
  have hGt : prior.condProbSet s a > prior.probOfSet a := by
    rw [hCond]; exact hNotCertain
  convert hGt

/-- Evidence is positive iff `condProbSet evidence conclusion > probOfSet conclusion`.

ENNReal subtraction truncates at zero, so the positive-evidence predicate
is phrased as a direct comparison rather than a sign-of-subtraction
predicate. -/
noncomputable def isPositiveEvidenceS {W : Type*} [Fintype W]
    (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] : Prop :=
  prior.condProbSet evidence conclusion > prior.probOfSet conclusion

/-- Evidence is negative iff `condProbSet evidence conclusion < probOfSet conclusion`. -/
noncomputable def isNegativeEvidenceS {W : Type*} [Fintype W]
    (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)] : Prop :=
  prior.condProbSet evidence conclusion < prior.probOfSet conclusion

/-- Algebraic bridge: positive evidence iff impact ratio exceeds 1
(under positive, finite conclusion-prior). Connects the comparison-style
predicate `isPositiveEvidenceS` to the ratio-style `PMF.impactRatio`. -/
theorem isPositiveEvidenceS_iff_impactRatio_gt_one {W : Type*} [Fintype W]
    (evidence conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ conclusion)]
    (hPos : prior.probOfSet conclusion > 0)
    (hNeTop : prior.probOfSet conclusion ≠ ⊤) :
    isPositiveEvidenceS evidence conclusion prior ↔
      prior.impactRatio evidence conclusion > 1 := by
  unfold isPositiveEvidenceS PMF.impactRatio
  rw [show (1 : ℝ≥0∞) = prior.probOfSet conclusion / prior.probOfSet conclusion from
        (ENNReal.div_self hPos.ne' hNeTop).symm]
  exact (ENNReal.div_lt_div_iff_left hPos.ne' hNeTop).symm

/-- Evidence-strength comparison: `r` evidences `a` more strongly than `r'`
iff `P(a | r) > P(a | r')`. @cite{thomas-2026} Def. 63. -/
noncomputable def evidencesMoreStronglyS {W : Type*} [Fintype W]
    (r r' a : Set W) (prior : Prior W)
    [DecidablePred (· ∈ r)] [DecidablePred (· ∈ r')] [DecidablePred (· ∈ a)] :
    Prop :=
  prior.condProbSet r a > prior.condProbSet r' a

/-! ### Conjunction strengthening

The core notion in @cite{thomas-2026}'s analysis of additive particles:
the conjunction `p1 ∩ p2` evidences `conclusion` more strongly than `p1`
alone. -/

/-- Conjunction `p1 ∩ p2` evidences `conclusion` more strongly than `p1`. -/
noncomputable def conjunctionStrengthensS {W : Type*} [Fintype W]
    (p1 p2 conclusion : Set W) (prior : Prior W)
    [DecidablePred (· ∈ p1)] [DecidablePred (· ∈ p2)]
    [DecidablePred (· ∈ conclusion)] : Prop :=
  haveI : DecidablePred (· ∈ (p1 ∩ p2)) := by
    intro w; exact inferInstanceAs (Decidable (_ ∧ _))
  evidencesMoreStronglyS (p1 ∩ p2) p1 conclusion prior

open Classical in
/-- Some alternative of `q` is strengthened by adding `p2` to `p1`.

Spec uses `Classical.dec` for per-alternative decidability so the predicate
body is well-typed without an `[∀ a, DecidablePred (· ∈ a)]` hypothesis. -/
noncomputable def someResolutionStrengthenedS {W : Type*} [Fintype W]
    (p1 p2 : Set W) (q : Core.Question W) (prior : Prior W) : Prop :=
  ∃ a ∈ Core.Question.alt q, prior.condProbSet (p1 ∩ p2) a > prior.condProbSet p1 a

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
    (s : Set W) (q : Core.Question W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Question.alt q)
    (h : prior.condProbSet s a ≠ prior.probOfSet a) :
    relevantS s q prior :=
  ⟨a, hAltMem, by convert h⟩

/-- Constructive witness for `probAnswersS`: produce an alternative `a`
    that is strictly raised by `s`. -/
lemma probAnswersS.of_witness {W : Type*} [Fintype W]
    (s : Set W) (q : Core.Question W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Question.alt q)
    (h : prior.condProbSet s a > prior.probOfSet a) :
    probAnswersS s q prior :=
  ⟨a, hAltMem, by convert h⟩

/-- Constructive witness for `someResolutionStrengthenedS`: produce an
    alternative `a` whose conditional probability strictly increases when
    `p2` is added to `p1`. -/
lemma someResolutionStrengthenedS.of_witness {W : Type*} [Fintype W]
    (p1 p2 : Set W) (q : Core.Question W) (prior : Prior W) (a : Set W)
    [DecidablePred (· ∈ p1)] [DecidablePred (· ∈ p2)] [DecidablePred (· ∈ a)]
    (hAltMem : a ∈ Core.Question.alt q)
    (h : prior.condProbSet (p1 ∩ p2) a > prior.condProbSet p1 a) :
    someResolutionStrengthenedS p1 p2 q prior := by
  haveI : DecidablePred (· ∈ p1 ∩ p2) :=
    fun w => inferInstanceAs (Decidable (_ ∧ _))
  exact ⟨a, hAltMem, by convert h⟩

/-! ### Conditional Answers (Def. 62 full: a + b)

`probAnswersS` captures Def. 62 condition (a) only. The full Def. 62 also
requires condition (b): the witness subset `T ⊆ alt(Q)` whose intersection
is strengthened must have **strictly maximum impact ratio** among
non-superset candidates. `⋂₀ T` is @cite{thomas-2026}'s `Q|R`.

**Faithful to Thomas's literal Def. 62b**, including the `A'_T ⊉ A_T`
filter that excludes super-collections from the comparison. Linguistic
content of this filter: a SUPER-collection of T (e.g., `T ∪ {extra alt}`)
is a "more informative answer," not a competitor — both T and a
super-T can be legitimate resolutions, with T the "minimal sufficient"
and the super-T a "fuller answer." Thomas's text supports this layered
view (cf. "Who came?" "Bailey" vs "Bailey and Cameron" — both answer).

A strict-max strengthening (drop the `¬ T ⊆ T'` filter, get uniqueness
via `lt_asymm`) was considered and rejected; see CHANGELOG 0.230.322 for
the linguistic argument that the filter is non-accidental.

**Uniqueness is asserted by Thomas but NOT formally derivable from a+b
alone.** Suppose `T₁ ⊊ T₂` both candidates with `impactRatio T₂ > impactRatio T₁`.
T₁'s clause excludes T₂ (T₁ ⊆ T₂); T₂'s clause demands T₂ > T₁ ✓; T₁'s
clause needs T₁ to dominate non-supersets ✓ (possibly). Both can satisfy
clauses — Thomas's "If such a set A exists, it is unique" appears to
require an implicit additional hypothesis (e.g., antichain alts under
non-degenerate prior, or maximality among candidates) that is not stated.
We therefore omit a generic `unique` theorem; consumers quantify
universally over conditional answers (sound regardless of uniqueness).
The deterministic-limit theorems below DO prove uniqueness in special
cases where it holds.

The `impactRatio` primitive lives in `Core.Probability.PMFFin` (general
PMF/Set machinery, reusable beyond answerhood). -/

open Classical in
/-- Def. 62a applied to `⋂₀ T`: `T` is a non-empty finite subcollection
of `q.alt`, and `R` strengthens the intersection. -/
noncomputable def IsConditionalAnswerCandidate {W : Type*} [Fintype W]
    (R : Set W) (q : Core.Question W) (prior : PMF W)
    (T : Set (Set W)) : Prop :=
  T.Nonempty ∧ T.Finite ∧ (∀ A ∈ T, A ∈ Core.Question.alt q) ∧
  prior.condProbSet R (⋂₀ T) > prior.probOfSet (⋂₀ T)

open Classical in
/-- Def. 62 (full): `T` is a candidate AND has strictly maximum impact
ratio over `R` among all non-superset finite non-empty subcollections of
`q.alt`. Faithful to Thomas's literal text including the `¬ T ⊆ T'` filter. -/
noncomputable def IsConditionalAnswer {W : Type*} [Fintype W]
    (R : Set W) (q : Core.Question W) (prior : PMF W)
    (T : Set (Set W)) : Prop :=
  IsConditionalAnswerCandidate R q prior T ∧
  ∀ T' : Set (Set W), T'.Nonempty → T'.Finite →
    (∀ A ∈ T', A ∈ Core.Question.alt q) →
    ¬ T ⊆ T' →
    prior.impactRatio R (⋂₀ T) > prior.impactRatio R (⋂₀ T')

/-- Singleton-resolution corollary: when the conditional answer is
`{a}` for a single alternative, `a` is in `q.alt` and is strengthened by `R`. -/
theorem IsConditionalAnswer.singleton_strengthens {W : Type*} [Fintype W]
    {R : Set W} {q : Core.Question W} {prior : PMF W} {a : Set W}
    (h : IsConditionalAnswer R q prior {a}) :
    a ∈ Core.Question.alt q ∧ prior.condProbSet R a > prior.probOfSet a := by
  obtain ⟨⟨_, _, hAlt, hStr⟩, _⟩ := h
  rw [Set.sInter_singleton] at hStr
  exact ⟨hAlt a (Set.mem_singleton _), hStr⟩

/-- Bridge: a singleton conditional answer over `R = p₁ ∩ p₂` provides
the existential witness for `someResolutionStrengthenedS p₁ p₂ q prior`,
*provided* the strengthening is also strict relative to `p₁` alone (not
just relative to the unconditional prior). The base predicate
`IsConditionalAnswer` strengthens against the unconditional `P(a)`; the
existing `someResolutionStrengthenedS` strengthens against `P(a | p₁)`.
The two coincide when `p₁` is uninformative about `a`; in general
`someResolutionStrengthenedS` is the strictly stronger comparison.

This bridge therefore takes the comparison-against-`p₁` strengthening as
a separate hypothesis. -/
theorem IsConditionalAnswer.singleton_someResolutionStrengthened
    {W : Type*} [Fintype W]
    {p1 p2 : Set W} {q : Core.Question W} {prior : PMF W} {a : Set W}
    [DecidablePred (· ∈ p1)] [DecidablePred (· ∈ p2)] [DecidablePred (· ∈ a)]
    (h : IsConditionalAnswer (p1 ∩ p2) q prior {a})
    (hStrAnt : prior.condProbSet (p1 ∩ p2) a > prior.condProbSet p1 a) :
    someResolutionStrengthenedS p1 p2 q prior :=
  someResolutionStrengthenedS.of_witness p1 p2 q prior a
    h.singleton_strengthens.1 hStrAnt

/-! ### Karttunen-style deterministic limit

Classical answerhood (Karttunen 1977) takes "the answer to Q at world w₀" to
be the conjunction of alternatives true at w₀. `IsConditionalAnswer` should
specialize to this when evidence is deterministic (`R = {w₀}` for a single
world). The `karttunenAlts` set captures Karttunen's witness: the alts of
`q` containing `w₀`. This section establishes:

- `IsConditionalAnswer.deterministic_subset_karttunenAlts` — any conditional
  answer for `R = {w₀}` consists only of alts containing `w₀`. Proves the
  forward direction of "uniqueness in deterministic limit" — the substrate's
  open uniqueness obligation is provable in this special case.
- `sInter_karttunenAlts_eq` — pure Set algebra: the intersection of
  `karttunenAlts q w₀` is the Karttunen exhaustive answer at `w₀`.
- `isConditionalAnswer_singleton_karttunen` — existence: when there's a
  unique alt of `q` containing `w₀` (the partition / polar case),
  `{a}` IS the conditional answer for `R = {w₀}`.

The general existence direction for arbitrary `karttunenAlts` (mention-some
case) requires non-degeneracy hypotheses on alt intersections (antichain
alone is insufficient; pairwise non-redundancy under the prior needed).
Deferred. The literal entity-based `karttunenCompleteAnswer` in
`Theories/Semantics/Questions/Answerhood/Answerhood.lean` uses a different
`(domain, pred)` presentation; bridging requires a `Question.ofKarttunen`
constructor — also deferred. -/

/-- The set of alternatives of `q` true at world `w₀` — the natural
"Karttunen-style" witness for an exhaustive answer at `w₀`. -/
def karttunenAlts {W : Type*} (q : Core.Question W) (w₀ : W) : Set (Set W) :=
  {A | A ∈ Core.Question.alt q ∧ w₀ ∈ A}

/-- Intersection characterisation: `⋂₀ karttunenAlts q w₀` equals
the Karttunen exhaustive answer at `w₀` (pure Set algebra). -/
theorem sInter_karttunenAlts_eq {W : Type*} (q : Core.Question W) (w₀ : W) :
    ⋂₀ (karttunenAlts q w₀) =
      {v | ∀ A ∈ Core.Question.alt q, w₀ ∈ A → v ∈ A} := by
  ext v
  simp only [karttunenAlts, Set.mem_sInter, Set.mem_setOf_eq, and_imp]

/-- Forward direction of "uniqueness in deterministic limit": any conditional
answer for `R = {w₀}` consists only of alternatives containing `w₀`.

The substrate's general uniqueness is open (see `IsConditionalAnswer`'s
docstring), but this special case is provable directly from the strengthening
clause — `condProbSet ({w₀}) (⋂T) > probOfSet (⋂T)` forces `w₀ ∈ ⋂T`, hence
`w₀ ∈ A` for every `A ∈ T`. -/
theorem IsConditionalAnswer.subset_karttunenAlts {W : Type*} [Fintype W]
    {q : Core.Question W} {prior : PMF W} {w₀ : W} {T : Set (Set W)}
    [DecidableEq W]
    (h : IsConditionalAnswer ({w₀}) q prior T)
    (hPos : prior.probOfSet ({w₀} : Set W) > 0) :
    T ⊆ karttunenAlts q w₀ := by
  intro A hA
  obtain ⟨⟨_, _, hAlt, hStr⟩, _⟩ := h
  refine ⟨hAlt A hA, ?_⟩
  -- w₀ ∈ A. By contradiction: if not, w₀ ∉ ⋂T, so condProbSet({w₀}) ⋂T = 0,
  -- contradicting the strengthening clause.
  by_contra h_notin
  have h_w0_notin_inter : w₀ ∉ ⋂₀ T := fun h_in =>
    h_notin (Set.mem_sInter.mp h_in A hA)
  have h_inter_empty : ({w₀} : Set W) ∩ ⋂₀ T = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
               Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hv⟩
    exact h_w0_notin_inter hv
  have h_cond_zero : prior.condProbSet ({w₀} : Set W) (⋂₀ T) = 0 := by
    rw [PMF.condProbSet_eq_div, h_inter_empty, PMF.probOfSet_empty,
        ENNReal.zero_div]
  have h_cond_zero' : prior.condProbSet ({w₀} : Set W) (⋂₀ T) = 0 := by
    convert h_cond_zero
  rw [h_cond_zero'] at hStr
  exact absurd hStr (not_lt.mpr (zero_le _))

/-- Existence in the unique-alt deterministic limit: when there's exactly one
alt of `q` containing `w₀` (the partition / polar case where Karttunen
collapses to a single cell), that singleton IS a conditional answer for
`R = {w₀}`.

For the multi-alt mention-some case (e.g., Thomas's example 68), this
restricted existence theorem doesn't apply — the general existence proof
needs non-degeneracy hypotheses on alt intersections under the prior.
Deferred. -/
theorem isConditionalAnswer_singleton_karttunen {W : Type*} [Fintype W]
    [DecidableEq W]
    (q : Core.Question W) (prior : PMF W) (w₀ : W) (a : Set W)
    [DecidablePred (· ∈ a)]
    (h_alt : a ∈ Core.Question.alt q)
    (h_mem : w₀ ∈ a)
    (h_unique : ∀ A ∈ Core.Question.alt q, w₀ ∈ A → A = a)
    (hPos_w0 : prior.probOfSet ({w₀} : Set W) > 0)
    (hLt_a : prior.probOfSet a < 1) :
    IsConditionalAnswer ({w₀}) q prior {a} := by
  refine ⟨⟨Set.singleton_nonempty _, Set.finite_singleton _, ?alts, ?strengthen⟩,
          ?max⟩
  case alts =>
    intro A hA
    rw [Set.mem_singleton_iff] at hA; subst hA; exact h_alt
  case strengthen =>
    rw [Set.sInter_singleton]
    have h_sub : ({w₀} : Set W) ⊆ a := by
      intro v hv; rw [Set.mem_singleton_iff] at hv; subst hv; exact h_mem
    have h_cond_one : prior.condProbSet ({w₀} : Set W) a = 1 := by
      rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr h_sub]
      exact ENNReal.div_self hPos_w0.ne' (PMF.probOfSet_ne_top _ _)
    have h_cond_one' : prior.condProbSet ({w₀} : Set W) a = 1 := by
      convert h_cond_one
    rw [h_cond_one']; exact hLt_a
  case max =>
    intro T' hNeT' _hFinT' hAltT' hNotSub
    rw [Set.sInter_singleton]
    have h_a_notin_T' : a ∉ T' :=
      fun h => hNotSub (Set.singleton_subset_iff.mpr h)
    have h_w0_notin_inter : w₀ ∉ ⋂₀ T' := by
      obtain ⟨A₀, hA₀⟩ := hNeT'
      intro h_w0_in
      have h_w0_in_A₀ : w₀ ∈ A₀ := Set.mem_sInter.mp h_w0_in A₀ hA₀
      have h_A₀_eq : A₀ = a := h_unique A₀ (hAltT' A₀ hA₀) h_w0_in_A₀
      exact h_a_notin_T' (h_A₀_eq ▸ hA₀)
    have h_cond_T'_zero : prior.condProbSet ({w₀} : Set W) (⋂₀ T') = 0 := by
      have h_empty : ({w₀} : Set W) ∩ ⋂₀ T' = ∅ := by
        ext v
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
                   Set.mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hv⟩
        exact h_w0_notin_inter hv
      rw [PMF.condProbSet_eq_div, h_empty, PMF.probOfSet_empty,
          ENNReal.zero_div]
    have h_sub_a : ({w₀} : Set W) ⊆ a := by
      intro v hv; rw [Set.mem_singleton_iff] at hv; subst hv; exact h_mem
    have h_cond_a_one : prior.condProbSet ({w₀} : Set W) a = 1 := by
      rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr h_sub_a]
      exact ENNReal.div_self hPos_w0.ne' (PMF.probOfSet_ne_top _ _)
    unfold PMF.impactRatio
    classical
    rw [show prior.condProbSet ({w₀} : Set W) a = 1 from by convert h_cond_a_one,
        show prior.condProbSet ({w₀} : Set W) (⋂₀ T') = 0 from by convert h_cond_T'_zero,
        ENNReal.zero_div]
    rw [gt_iff_lt, ENNReal.div_pos_iff]
    exact ⟨one_ne_zero, PMF.probOfSet_ne_top _ _⟩

end Semantics.Questions.ProbabilisticAnswerhood
