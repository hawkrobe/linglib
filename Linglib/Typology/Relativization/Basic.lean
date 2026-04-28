import Linglib.Datasets.WALS.Features.F122A
import Linglib.Datasets.WALS.Features.F123A

/-!
# Cross-Linguistic Typology of Relativization (WALS Chapters 122/123)
@cite{comrie-1989} @cite{keenan-comrie-1977} @cite{comrie-2013}

WALS-aggregate findings on relative-clause formation strategies from two
WALS chapters by @cite{comrie-2013}. The `RelativizationProfile` struct
+ strategy enums + WALS converters live in `Typology/Relativization/Defs.lean`;
per-language data lives in `Fragments/{Lang}/Relativization.lean`.

## Ch 122: Relativization on Subjects

How languages form relative clauses on subject position. Strategies: gap
(the relativized position is empty), pronoun retention (a resumptive
pronoun fills the relativized position), relative pronoun (a dedicated
wh-element fills the position and typically fronts), non-reduction (head
noun repeated inside the relative clause).

Sample: 166 languages (WALS v2020.4). Gap dominates for subjects,
reflecting the high accessibility of subject position on the
@cite{keenan-comrie-1977} hierarchy.

## Ch 123: Relativization on Obliques

Whether oblique positions can be relativized, and by what strategy. Many
gap-on-subject languages switch to pronoun retention or relative pronouns
for obliques, or cannot relativize obliques at all.

Sample: 112 languages (WALS v2020.4). Gap remains the most common
strategy, but pronoun retention is much more common than for subjects, and
a sizeable minority of languages cannot relativize obliques at all.

## @cite{keenan-comrie-1977} Accessibility Hierarchy

The Accessibility Hierarchy ranks grammatical positions by their
accessibility to relativization:

  Subject > Direct Object > Indirect Object > Oblique > Genitive > Object of Comparison

Three Hierarchy Constraints follow:

1. **HC₁**: A language must be able to relativize subjects.
2. **HC₂ (Continuity)**: Any RC-forming strategy must apply to a continuous
   segment of the AH.
3. **HC₃ (Cut-off)**: Strategies that apply at one point may cease at any
   lower point.

From these, the **Primary Relativization Constraint** follows: if a
language's primary strategy can apply to a low position, it can also apply
to all higher positions.
-/

namespace Typology.Relativization

private abbrev ch122 := Datasets.WALS.F122A.allData
private abbrev ch123 := Datasets.WALS.F123A.allData

set_option maxRecDepth 2000 in
/-- WALS Ch 122: gap is the most common subject relativization strategy,
    followed by non-reduction, relative pronoun, and pronoun retention. -/
theorem gap_most_common_for_subjects :
    (ch122.filter (·.value == .gap)).length >
    (ch122.filter (·.value == .nonReduction)).length ∧
    (ch122.filter (·.value == .nonReduction)).length >
    (ch122.filter (·.value == .relativePronoun)).length ∧
    (ch122.filter (·.value == .relativePronoun)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 2000 in
/-- WALS Chs 122/123: pronoun retention is more common for obliques than
    for subjects — a key Accessibility-Hierarchy prediction
    (@cite{keenan-comrie-1977}). -/
theorem retention_increases_for_obliques :
    (ch123.filter (·.value == .pronounRetention)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by decide

set_option maxRecDepth 2000 in
/-- WALS Ch 123: some languages cannot relativize obliques at all,
    contrasting with subjects, where the Ch 122 enum has no "not
    possible" value. -/
theorem obliques_sometimes_not_relativizable :
    (ch123.filter (·.value == .notPossible)).length > 0 := by decide

end Typology.Relativization
