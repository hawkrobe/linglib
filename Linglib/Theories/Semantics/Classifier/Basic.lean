import Linglib.Core.Mereology
import Linglib.Core.Lexical.NounCategorization
import Linglib.Theories.Semantics.Plurality.Link1983

/-!
# Classifier Semantics
@cite{chierchia-1998} @cite{little-moroney-royer-2022} @cite{moroney-2021}

Unified compositional semantics for classifier constructions, connecting
the typological vocabulary in `Core.NounCategorization` to the mereological
infrastructure in `Core.Mereology` and the materialization homomorphism
in `Theories.Semantics.Plurality.Link1983`.

## Two Semantic Strategies

Numeral classifiers form a heterogeneous class
(@cite{little-moroney-royer-2022}). Two families of theories are BOTH
correct, for different languages:

- **CLF-for-N** (@cite{chierchia-1998}; @cite{jenks-2011};
  @cite{nomoto-2013}): the classifier atomizes the noun denotation.
  `⟦CLF⟧ = λPλx.[P(x) ∧ Atom(x)]`. This is `Mereology.atomize`.
  Languages: Shan, Mandarin, Japanese.

- **CLF-for-NUM** (@cite{krifka-1995}; @cite{bale-coon-2014}): the
  classifier is a measure function required by the numeral.
  `⟦TWO⟧ = λmλPλx.[P(x) ∧ m(x) = 2]`. This is `Mereology.QMOD`.
  Languages: Ch'ol.

Both strategies convert CUM predicates to QUA predicates — this is the
universal semantic function of classifiers regardless of strategy.

## Group Classifiers

Group classifiers like Shan *phŭŋ* 'group' use Link's materialization
homomorphism: `⟦phŭŋ⟧ = λPλx.∃y[P(y) ∧ μ(x) = 1 ∧ h(y) = h(x)]`.
The group is a single entity (μ = 1) whose material constitution matches
that of some P-entity.

## Architecture

This module composes existing pieces:
- `Mereology.atomize` — CLF-for-N denotation
- `Mereology.QMOD` — CLF-for-NUM denotation
- `Mereology.atomize_qua` — QUA result for CLF-for-N
- `Mereology.extMeasure_qua` — QUA result for CLF-for-NUM
- `Link1983.Materialization` — group classifier semantics
- `NounCategorization.ClassifierStrategy` — typological dispatch
-/

namespace Semantics.Classifier

open Mereology
open Core.NounCategorization (ClassifierStrategy)

-- ============================================================================
-- §1: CLF-for-N — Atomization (@cite{chierchia-1998})
-- ============================================================================

/-- CLF-for-N denotation: the classifier atomizes the noun denotation.
    ⟦CLF⟧ = λPλx.[P(x) ∧ ¬∃y[P(y) ∧ y < x]]

    This IS `Mereology.atomize`. The wrapper aliases it under the
    classifier namespace for discoverability and adds the
    @cite{little-moroney-royer-2022} citation. -/
abbrev clfForNoun {α : Type*} [PartialOrder α] (P : α → Prop) : α → Prop :=
  atomize P

/-- CLF-for-N produces quantized predicates: the atomized noun
    denotation is QUA, enabling counting by the numeral.
    This IS `Mereology.atomize_qua`. -/
theorem clfForNoun_qua {α : Type*} [PartialOrder α]
    {P : α → Prop} : QUA (clfForNoun P) :=
  atomize_qua

/-- CLF-for-N restricts: `clfForNoun P ⊆ P`. -/
theorem clfForNoun_sub {α : Type*} [PartialOrder α]
    {P : α → Prop} {x : α} (h : clfForNoun P x) : P x :=
  atomize_sub h

-- ============================================================================
-- §2: CLF-for-NUM — Measure Modification (@cite{krifka-1995})
-- ============================================================================

/-- CLF-for-NUM denotation: the classifier is a measure function, and
    the numeral selects entities with the right measure value.
    ⟦TWO-CLF⟧ = λPλx.[P(x) ∧ μ(x) = 2]

    This IS `Mereology.QMOD` instantiated with a measure function μ
    and a target value n. -/
abbrev clfForNum {α : Type*} (P : α → Prop) (μ : α → ℚ) (n : ℚ) : α → Prop :=
  QMOD P μ n

/-- CLF-for-NUM produces quantized predicates when μ is an extensive
    measure: no proper part of an n-measure entity also has measure n.
    Generalizes over any base predicate P. -/
theorem clfForNum_qua {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) :
    QUA (fun x => QMOD P μ n x) :=
  fun x y ⟨_, hx⟩ hlt ⟨_, hy⟩ => by
    have := hμ.strict_mono x y hlt
    rw [hy, hx] at this
    exact absurd this (lt_irrefl _)

-- ============================================================================
-- §3: Group Classifier — Materialization (@cite{moroney-2021} Ch. 3)
-- ============================================================================

/-- Group classifier denotation using Link's materialization homomorphism.

    ⟦phŭŋ_CLF⟧ = λPλx.∃y[P(y) ∧ Atom(x) ∧ h(y) = h(x)]

    The group classifier takes a predicate P and returns a predicate true
    of atomic entities x whose material constitution (`h(x)`) matches
    that of some P-entity y. This is how "a group of dogs" can denote
    a single atomic group-entity made of the same "stuff" as the dogs.

    @cite{moroney-2021} §3.3.2: ⟦phŭŋ_CLF⟧ = λP.λx.∃y[P(y) ∧
    μ_GROUP.A(x) = 1 ∧ h(y) = h(x)].

    We use `Atom x` instead of `μ(x) = 1` since atomicity is the
    mereological content of "counting as one group." -/
def groupClf {E D : Type*} [SemilatticeSup E] [SemilatticeSup D]
    (mat : Semantics.Plurality.Link1983.Materialization E D)
    (P : E → Prop) (x : E) : Prop :=
  Atom x ∧ ∃ y, P y ∧ mat.h y = mat.h x

/-- Group classifier output is quantized: no proper part of a group
    is itself a group (since groups are atoms). -/
theorem groupClf_qua {E D : Type*} [SemilatticeSup E] [SemilatticeSup D]
    (mat : Semantics.Plurality.Link1983.Materialization E D)
    {P : E → Prop} : QUA (groupClf mat P) := by
  intro x y ⟨hAtom, _⟩ hlt _
  exact absurd (hAtom y (le_of_lt hlt)) (ne_of_lt hlt)

-- ============================================================================
-- §4: Strategy-Indexed Dispatch
-- ============================================================================

/-- Dispatch from `ClassifierStrategy` to a noun-side predicate transformer.

    - `.forNoun` → `clfForNoun P` (Chierchia/LMR: classifier atomizes the noun)
    - `.forNumeral` → `clfForNum P μ n` (Krifka/Bale-Coon/LMR: measure-modify the numeral)
    - `.sudoBlocking` → `clfForNoun P` (Sudo: at the noun-side composition,
      the sortal-presupposition body of the classifier individuates atoms;
      the dispatch agrees with `.forNoun` here because we're projecting a
      numeral-side analysis onto a noun-side abstraction. The disagreement
      with Chierchia is *not* in noun-side individuation; it's in *where*
      the obligation to use a classifier comes from. See
      `Phenomena/Classifiers/Studies/Sudo2016.lean`.) -/
def classifierDenot {α : Type*} [PartialOrder α]
    (s : ClassifierStrategy) (P : α → Prop) (μ : α → ℚ) (n : ℚ) : α → Prop :=
  match s with
  | .forNoun     => clfForNoun P
  | .forNumeral  => clfForNum P μ n
  | .sudoBlocking => clfForNoun P

/-- Both classifier strategies produce QUA predicates.

    - CLF-for-N: `atomize_qua`
    - CLF-for-NUM: `extMeasure_qua` (when μ is extensive)
    - Group CLF: `groupClf_qua`

    The common thread: classifiers convert cumulative (uncountable)
    predicates into quantized (countable) predicates, enabling
    numeral modification. -/
theorem classifier_quantizes_forNoun {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (_hCum : CUM P) : QUA (clfForNoun P) :=
  clfForNoun_qua

-- ============================================================================
-- §5: CLF-for-N Preserves Membership
-- ============================================================================

/-- Atomization is a restriction: every atom of P is in P. -/
theorem clfForNoun_mem {α : Type*} [PartialOrder α]
    {P : α → Prop} {x : α} (hAtom : Atom x) (hP : P x) :
    clfForNoun P x :=
  ⟨hP, hAtom⟩

/-- If P has atoms, then CLF-for-N is non-empty. This is the
    content of the "sortal classifier" requirement: the classifier
    can only apply to nouns whose denotation includes atoms.
    Mass nouns (divisive predicates with no atoms) require a
    mensural classifier instead. -/
theorem clfForNoun_nonempty {α : Type*} [PartialOrder α]
    {P : α → Prop} {a : α} (hP : P a) (hAtom : Atom a) :
    ∃ x, clfForNoun P x :=
  ⟨a, hP, hAtom⟩

end Semantics.Classifier
