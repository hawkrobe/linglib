import Linglib.Syntax.RelativeClause.Basic
import Linglib.Data.WALS.Features.F90D
import Linglib.Data.WALS.Features.F122A
import Linglib.Data.WALS.Features.F123A

/-!
# Relative clauses: typological survey (WALS)
[comrie-1989] [keenan-comrie-1977] [comrie-kuteva-2013a] [comrie-kuteva-2013b] [dryer-2013-wals]

The cross-linguistic WALS-survey facet of the relative clause: relativization
strategies (WALS Chs 122/123/90D), RC position, and the [keenan-comrie-1977]
Accessibility-Hierarchy cut-off, with the WALS converters and aggregate
distribution theorems. Per-language values are bare `def`s in a
`Relativization` namespace in `Fragments/{Lang}/Relativization.lean`.

## Main declarations

* `RelativeClause.SubjStrategy` — subject relativization strategy (WALS Ch 122).
* `RelativeClause.OblStrategy` — oblique relativization strategy (WALS Ch 123),
  including the `.notRelativizable` value subjects structurally lack.
* `RelativeClause.RCPosition`, `AHPosition` — RC position and AH cut-off.
* `RelativeClause.InternallyHeadedStrategy` — status of the head-internal
  strategy (WALS Ch 90D).
* `fromWALS122A` / `fromWALS123A` / `fromWALS90D` — WALS raw-value converters.

## Implementation notes

WALS Chs 122/123 do not distinguish a "mixed" category; `.mixed` profiles
cannot be grounded against WALS via the converters. Subject relativization
(Ch 122) has no "not possible" value — every language can relativize subjects
(HC₁) — whereas oblique relativization (Ch 123) does, so `OblStrategy` carries
`.notRelativizable` and `SubjStrategy` does not.
-/

set_option autoImplicit false

namespace RelativeClause

/-! ### Subject relativization strategies (WALS Ch 122) -/

/-- WALS Ch 122: strategy used to relativize the subject position. -/
inductive SubjStrategy where
  /-- The relativized position is empty. E.g., English "the man [that _ left]". -/
  | gap
  /-- A resumptive pronoun fills the position. E.g., dialectal Arabic. -/
  | pronounRetention
  /-- A dedicated wh-element / relative pronoun fills the position and
      typically fronts. E.g., German "der Mann [der ging]". -/
  | relativePronoun
  /-- The head noun (or a full NP) is repeated inside the RC. -/
  | nonReduction
  /-- The language productively uses more than one of the above for
      subjects. WALS does not distinguish a "mixed" category; this is
      used only in our profiles. -/
  | mixed
  deriving DecidableEq, Repr

/-! ### Oblique relativization strategies (WALS Ch 123) -/

/-- WALS Ch 123: strategy used to relativize oblique positions, or
    whether obliques can be relativized at all. -/
inductive OblStrategy where
  /-- Gap on obliques (often with preposition stranding). -/
  | gap
  /-- Resumptive pronoun on obliques (more common than for subjects). -/
  | pronounRetention
  /-- Relative pronoun on obliques. E.g., English "in which", German "in der". -/
  | relativePronoun
  /-- Head noun repeated inside the RC. -/
  | nonReduction
  /-- Multiple strategies productively used. WALS does not distinguish a
      "mixed" category; used only in our profiles. -/
  | mixed
  /-- Obliques cannot be relativized at all in this language. -/
  | notRelativizable
  deriving DecidableEq, Repr

/-! ### Internally-headed strategy (WALS Ch 90D) -/

/-- WALS Ch 90D: status of the internally-headed strategy in a language.

    WALS distinguishes whether the internally-headed strategy is the dominant
    relativization pattern, co-dominant with another (RelN, NRel, correlative,
    double-headed), present as a non-dominant alternative, merely attested, or
    absent entirely. -/
inductive InternallyHeadedStrategy where
  /-- Internally-headed is the dominant strategy. -/
  | dominant
  /-- Co-dominant with a relative-noun construction. -/
  | coRelN
  /-- Co-dominant with a noun-relative construction. -/
  | coNRel
  /-- Co-dominant with a correlative construction. -/
  | coCorrelative
  /-- Co-dominant with a double-headed construction. -/
  | coDoubleHeaded
  /-- Present as a non-dominant alternative. -/
  | nondominant
  /-- Attested but not dominant or co-dominant (WALS lumps this as "exists"). -/
  | attested
  /-- The internally-headed strategy is not attested in this language.
      WALS 90D codes only languages that *have* the strategy in some form, so
      this case is for hand-coded profiles whose Fragment asserts absence. -/
  | absent
  deriving DecidableEq, Repr


/-! ### WALS converters (Chs 122, 123, 90D) -/

/-- Convert a WALS 122A subject relativization value to `SubjStrategy`.
    WALS does not distinguish a "mixed" category, so languages whose
    profile is `.mixed` cannot be grounded against WALS via this converter
    alone. -/
def fromWALS122A : Data.WALS.F122A.SubjectRelativization → SubjStrategy
  | .relativePronoun => .relativePronoun
  | .nonReduction    => .nonReduction
  | .pronounRetention => .pronounRetention
  | .gap             => .gap

/-- Convert a WALS 123A oblique relativization value to `OblStrategy`.
    WALS `.notPossible` becomes `.notRelativizable`; `.mixed` profiles
    cannot be grounded against WALS via this converter. -/
def fromWALS123A : Data.WALS.F123A.ObliqueRelativization → OblStrategy
  | .relativePronoun => .relativePronoun
  | .nonReduction    => .nonReduction
  | .pronounRetention => .pronounRetention
  | .gap             => .gap
  | .notPossible     => .notRelativizable

/-- Convert a WALS 90D internally-headed value to `InternallyHeadedStrategy`.
    WALS does not code an `.absent` case (the chapter only sampled languages
    that *have* the strategy), so absence is asserted by hand in the Fragment. -/
def fromWALS90D : Data.WALS.F90D.InternallyHeadedRelativeClauses →
    InternallyHeadedStrategy
  | .relativeClauseDominant   => .dominant
  | .orReln                   => .coRelN
  | .orNrel                   => .coNRel
  | .orCorrelative            => .coCorrelative
  | .orDoubleHeaded           => .coDoubleHeaded
  | .occursAsNondominantType  => .nondominant
  | .exists_                  => .attested

/-! ### Distribution theorems

WALS-aggregate findings on relative-clause formation strategies
([comrie-kuteva-2013a] [comrie-kuteva-2013b] [dryer-2013-wals]).
Ch 122 (subjects): 166 languages; gap dominates,
reflecting subjects' high accessibility on the [keenan-comrie-1977]
hierarchy. Ch 123 (obliques): 112 languages; gap remains most common, but
pronoun retention is far more frequent than for subjects, and a sizeable
minority cannot relativize obliques at all. -/

private abbrev ch122 := Data.WALS.F122A.allData
private abbrev ch123 := Data.WALS.F123A.allData

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
    ([keenan-comrie-1977]). -/
theorem retention_increases_for_obliques :
    (ch123.filter (·.value == .pronounRetention)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by decide

set_option maxRecDepth 2000 in
/-- WALS Ch 123: some languages cannot relativize obliques at all,
    contrasting with subjects, where the Ch 122 enum has no "not
    possible" value. -/
theorem obliques_sometimes_not_relativizable :
    (ch123.filter (·.value == .notPossible)).length > 0 := by decide

end RelativeClause
