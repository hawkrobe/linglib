import Linglib.Features.Polarity

/-!
# Multiplicity Inferences: Empirical Data

Theory-neutral empirical patterns for multiplicity inferences —
the observation that bare plurals trigger a "more than one" reading
in upward-entailing contexts but not in downward-entailing contexts.

## The Puzzle

- "Emily fed giraffes" → Emily fed more than one giraffe
- "Emily didn't feed giraffes" ≠ Emily didn't feed more than one giraffe
  (rather: Emily didn't feed any giraffes)

This monotonicity sensitivity parallels classical scalar implicatures
(e.g., "some" → "not all" in UE but not DE contexts).

## Theoretical Approaches

Three main accounts:
1. **Ambiguity** (@cite{farkas-de-swart-2010}): Plural is ambiguous
   (inclusive "one or more" vs exclusive "more than one"), resolved by
   Strongest Meaning Hypothesis.
2. **Implicature** (@cite{sauerland-2003}, @cite{spector-2007},
   @cite{zweig-2009}): Plural literally means "one or more," multiplicity
   arises as a scalar implicature with the singular as alternative.
3. **Homogeneity** (@cite{kriz-2015}): Plural interpretation via
   homogeneity presupposition.

## Key References

- @cite{sauerland-2003}
- @cite{spector-2007}
- @cite{zweig-2009}
- @cite{farkas-de-swart-2010}
- @cite{tieu-etal-2020}
-/

set_option autoImplicit false

namespace Phenomena.Plurals.Multiplicity

open Features (Polarity)

-- ============================================================================
-- §1  Empirical Data
-- ============================================================================

/--
A multiplicity inference datum: a bare plural sentence tested
in upward-entailing (positive) and downward-entailing (negative) contexts.
-/
structure MultiplicityDatum where
  /-- The bare plural sentence (positive form) -/
  positiveSentence : String
  /-- The negated form -/
  negativeSentence : String
  /-- Does the "more than one" inference arise in the positive? -/
  multiplicityInPositive : Bool
  /-- Does the "more than one" inference arise in the negative? -/
  multiplicityInNegative : Bool
  deriving Repr

/--
Core example: "Emily fed giraffes."

In UE: interpreted as "Emily fed more than one giraffe."
In DE: "Emily didn't feed giraffes" ≈ "Emily didn't feed any giraffes."
-/
def fedGiraffes : MultiplicityDatum :=
  { positiveSentence := "Emily fed giraffes"
  , negativeSentence := "Emily didn't feed giraffes"
  , multiplicityInPositive := true
  , multiplicityInNegative := false
  }

/-- Conditional antecedent (DE context). -/
def booksOnDesk : MultiplicityDatum :=
  { positiveSentence := "There are books on Stephen's desk"
  , negativeSentence := "If there are books on Stephen's desk, Robin should lock the door"
  , multiplicityInPositive := true
  , multiplicityInNegative := false
  }

-- ── Per-datum monotonicity verification ──────────────────────

/-- Multiplicity arises in UE but not DE for "fed giraffes". -/
theorem fedGiraffes_monotonicity :
    fedGiraffes.multiplicityInPositive = true ∧
    fedGiraffes.multiplicityInNegative = false := ⟨rfl, rfl⟩

/-- Multiplicity arises in UE but not DE for "books on desk". -/
theorem booksOnDesk_monotonicity :
    booksOnDesk.multiplicityInPositive = true ∧
    booksOnDesk.multiplicityInNegative = false := ⟨rfl, rfl⟩

-- ============================================================================
-- §2  Scalar Parallels
-- ============================================================================

/--
The monotonicity sensitivity of multiplicity inferences parallels that
of classical scalar implicatures. This structure captures the parallel.
-/
structure MonotonicityParallel where
  /-- The scalar term (e.g., "some", bare plural) -/
  weakTerm : String
  /-- Its stronger alternative (e.g., "all", singular) -/
  strongAlternative : String
  /-- Inference in UE context -/
  inferenceInUE : String
  /-- Does inference arise in UE? -/
  arisesInUE : Bool
  /-- Does inference arise in DE? -/
  arisesInDE : Bool
  deriving Repr

/-- Some/all parallel. -/
def someAllParallel : MonotonicityParallel :=
  { weakTerm := "some"
  , strongAlternative := "all"
  , inferenceInUE := "not all"
  , arisesInUE := true
  , arisesInDE := false
  }

/-- Plural/singular parallel. -/
def pluralSingularParallel : MonotonicityParallel :=
  { weakTerm := "plural (giraffes)"
  , strongAlternative := "singular (a giraffe)"
  , inferenceInUE := "more than one"
  , arisesInUE := true
  , arisesInDE := false
  }

/-- Or/and parallel. -/
def orAndParallel : MonotonicityParallel :=
  { weakTerm := "or"
  , strongAlternative := "and"
  , inferenceInUE := "not both"
  , arisesInUE := true
  , arisesInDE := false
  }

-- ── Per-parallel monotonicity verification ───────────────────

/-- Some/all: implicature in UE, not in DE. -/
theorem someAll_monotonicity :
    someAllParallel.arisesInUE = true ∧
    someAllParallel.arisesInDE = false := ⟨rfl, rfl⟩

/-- Plural/singular: multiplicity in UE, not in DE. -/
theorem pluralSingular_monotonicity :
    pluralSingularParallel.arisesInUE = true ∧
    pluralSingularParallel.arisesInDE = false := ⟨rfl, rfl⟩

/-- Or/and: exclusivity in UE, not in DE. -/
theorem orAnd_monotonicity :
    orAndParallel.arisesInUE = true ∧
    orAndParallel.arisesInDE = false := ⟨rfl, rfl⟩

-- ============================================================================
-- §3  Competing Theories
-- ============================================================================

/--
Competing theoretical approaches to multiplicity inferences.
-/
inductive PluralTheory where
  /-- Plural is ambiguous; Strongest Meaning Hypothesis resolves. -/
  | ambiguity
  /-- Plural literally means "one or more"; multiplicity is implicature. -/
  | implicature
  /-- Plural interpretation via homogeneity presupposition. -/
  | homogeneity
  deriving DecidableEq, Repr, Inhabited

-- ── Core mechanistic property ────────────────────────────────

/-- The fundamental discriminating property: does the theory analyze
    multiplicity as arising via the same mechanism as scalar implicatures?

    This is the single primitive from which all empirical predictions
    are derived. The implicature theory says multiplicity IS an SI;
    ambiguity says it arises from lexical polysemy + Strongest Meaning;
    homogeneity says it arises from presupposition. -/
def PluralTheory.usesSIMechanism : PluralTheory → Bool
  | .implicature => true
  | _ => false

-- ── Derived predictions ─────────────────────────────────────
-- Each prediction follows from the mechanistic claim: if multiplicity
-- is an SI, then known properties of SIs (acquisition delay, uniformity,
-- polarity sensitivity, truth-value asymmetry) transfer to multiplicity.

/-- Children undercompute SIs (@cite{noveck-2001}). If multiplicity IS
    an SI, children should compute fewer multiplicity inferences. -/
def PluralTheory.predictsChildrenComputeFewer (t : PluralTheory) : Bool :=
  t.usesSIMechanism

/-- SIs sharing a mechanism have correlated rates within individuals
    (Uniformity Prediction). Multiplicity rates should correlate with
    standard SI rates iff they share the SI mechanism. -/
def PluralTheory.predictsMultiplicitySICorrelation (t : PluralTheory) : Bool :=
  t.usesSIMechanism

/-- SIs show UE/DE polarity asymmetry. If multiplicity is an SI,
    the polarity asymmetry in children follows from children's general
    difficulty with SIs. -/
def PluralTheory.accountsForPolarityAsymmetry (t : PluralTheory) : Bool :=
  t.usesSIMechanism

/-- In singular contexts (exactly one object acted on):
    - If multiplicity is an SI: positive is literally true + false
      implicature (misleading); negative is literally false → different
      truth-value status.
    - If multiplicity is lexical/presuppositional: both are undefined
      or both false → same status.
    Only the SI mechanism predicts asymmetric truth-value judgments. -/
def PluralTheory.positiveNegativeDiffer (t : PluralTheory) : Bool :=
  t.usesSIMechanism

-- ── Structural theorems ─────────────────────────────────────

/-- All four predictions reduce to the single mechanistic property.
    This makes the structure explicit: we don't have four independent
    stipulations, but one property with four consequences. -/
theorem predictions_equivalent_to_mechanism (t : PluralTheory) :
    (t.predictsChildrenComputeFewer = true ↔ t.usesSIMechanism = true) ∧
    (t.predictsMultiplicitySICorrelation = true ↔ t.usesSIMechanism = true) ∧
    (t.accountsForPolarityAsymmetry = true ↔ t.usesSIMechanism = true) ∧
    (t.positiveNegativeDiffer = true ↔ t.usesSIMechanism = true) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- The implicature theory is uniquely identified by ANY of the four
    predictions (since they all reduce to `usesSIMechanism`). -/
theorem implicature_uniquely_predicts (t : PluralTheory)
    (h : t.usesSIMechanism = true) :
    t = .implicature := by
  cases t <;> simp_all [PluralTheory.usesSIMechanism]

/-- Any single prediction suffices to identify the implicature theory,
    since all predictions reduce to `usesSIMechanism`. Here we show this
    for `predictsChildrenComputeFewer` (the others are identical). -/
theorem childrenComputeFewer_identifies (t : PluralTheory)
    (h : t.predictsChildrenComputeFewer = true) :
    t = .implicature :=
  implicature_uniquely_predicts t h

/-- Singular context asymmetry identifies implicature. -/
theorem implicature_uniquely_discriminates_singular (t : PluralTheory)
    (h : t.positiveNegativeDiffer = true) :
    t = .implicature :=
  implicature_uniquely_predicts t h

/-- The competing theories do NOT use the SI mechanism. -/
theorem ambiguity_not_si : PluralTheory.ambiguity.usesSIMechanism = false := rfl
theorem homogeneity_not_si : PluralTheory.homogeneity.usesSIMechanism = false := rfl

end Phenomena.Plurals.Multiplicity
