/-!
# [iatridou-anagnostopoulou-izvorski-2001]: Observations about the form and meaning of the Perfect
[iatridou-anagnostopoulou-izvorski-2001]

Iatridou, Anagnostopoulou & Izvorski (Kenstowicz ed., *Ken Hale: A
Life in Language*, MIT Press 2001) introduce the **Perfect Time Span
(PTS)** framework for analyzing English perfect-aspect morphology
and its interaction with temporal adverbials.

## Verified content (vs PDF; § refs from the paper, not page numbers)

- **PTS framework with LB and RB terminology** (§3.1, "Inclusion of
  the utterance time by assertion"): "There is an interval that we
  will call the *perfect time span*. The *left boundary* (LB) of the
  perfect time span is specified by the argument of the adverbial.
  The *right boundary* (RB) is set by tense."
- **U-perfect vs E-perfect distinction** (§3): the paper's central
  focus, arguing for a semantic (not pragmatic) treatment of the
  ambiguity.
- **Four uses of the present perfect** (§2.2): universal,
  experiential, perfect of result, perfect of recent past — descriptive
  taxonomy borrowed from McCawley 1971, Comrie 1976, Binnick 1991.
- **Unmodified perfects are never U-perfects** (§3.2.1): diagnostic
  for U-reading availability — requires adverbial modification.
- **Bounded vs unbounded distinction** (§3): related to but distinct
  from stativity; perfect of state requires unboundedness.
- **Perfect-level vs eventuality-level adverbials** (§3.2.2): two
  levels at which adverbials can attach, corresponding to scope.

## Companion files (paper-anchored extensions)

- `Studies/Kiparsky2002.lean` — [kiparsky-2002]'s event-structure
  account of perfect polysemy (four readings from subevent-structure
  mappings; three puzzles).
- `Studies/IatridouZeijlstra2021.lean` —
  [iatridou-zeijlstra-2021]'s unification of *in years* and
  *until* via the Until Time Span (UTS), NPI-strength classification,
  Actuality Inference and Beyond Expectation Inference. Imports the
  `BoundaryKind` from this file.

-/

namespace IatridouEtAl2001

/-- Which boundary of a time span an adverbial sets.
    - `left`: LB adverbials (*in years*, *since*, *in (the last) 5 years*)
    - `right`: RB adverbials (*until*)
    [iatridou-anagnostopoulou-izvorski-2001] §3.1. -/
inductive BoundaryKind where
  | left   -- sets the left boundary (e.g., *since Monday*, *in years*)
  | right  -- sets the right boundary (e.g., *until 5pm*)
  deriving DecidableEq, Repr

/-- The two perfect readings IAI 2001 argue for as semantically (not
    pragmatically) distinct: universal (U-perfect) and existential
    (E-perfect). The paper's central §3 focus.

    The four-use descriptive taxonomy (universal / experiential /
    result / recent past) borrowed from McCawley 1971 lives in the
    Kiparsky2002 file's richer `PerfectReading` enum, which folds
    recent past into resultative per Kiparsky's own §1. -/
inductive PerfectVariant where
  | universal     -- U-perfect: eventuality holds throughout PTS
  | existential   -- E-perfect: eventuality holds somewhere in PTS
  deriving DecidableEq, Repr

/-- IAI §3.2.1: "Unmodified perfects are never U-perfects". A perfect
    sentence has a U-reading available only if it carries an adverbial
    modifier. We encode this as a property of perfect sentences: the
    `U` constructor takes evidence of adverbial modification. -/
inductive PerfectAvailability where
  /-- Unmodified perfect: only the E-reading is available. -/
  | unmodified
  /-- Adverbially modified perfect: both U- and E- readings available. -/
  | adverbiallyModified
  deriving DecidableEq, Repr

/-- The U-perfect-requires-adverbial diagnostic. -/
def availableVariants : PerfectAvailability → List PerfectVariant
  | .unmodified => [.existential]
  | .adverbiallyModified => [.universal, .existential]

/-- Unmodified perfects do not license the U-reading (§3.2.1). -/
theorem unmodifiedNotU :
    PerfectVariant.universal ∉ availableVariants .unmodified := by
  intro h
  simp only [availableVariants, List.mem_singleton] at h
  cases h

/-- Adverbially modified perfects license both readings. -/
theorem adverbiallyModifiedBothVariants :
    PerfectVariant.universal ∈ availableVariants .adverbiallyModified ∧
    PerfectVariant.existential ∈ availableVariants .adverbiallyModified :=
  ⟨List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩

end IatridouEtAl2001
