import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Morphology.Focus
import Linglib.Syntax.Extraction

/-!
# Tsotsil Agreement Fragment

Agreement morphology for Zinacantec Tsotsil (Tseltalan, Mayan)
([polian-2013]; [aissen-polian-2025]).

## Main declarations

* `Tsotsil.ArgPosition` with `.case`, `.accCase`: argument positions and
  their case (ergative-absolutive, no aspect split).
* `Tsotsil.setALinearity`, `Tsotsil.setBLinearity`: prefixal Set A,
  prefixal-or-suffixal Set B.
* `Tsotsil.setAExponent`, `Tsotsil.setBExponent`: Zinacantec Tsotsil
  exponent tables ([polian-2013]).
* `Tsotsil.Extraction.realize`: unmarked extraction (no Agent Focus).

## Implementation notes

Tsotsil has two agreement paradigms on the verb: Set A (ERG/GEN) prefixes
cross-reference the transitive agent (ergative) and possessor (genitive),
which are homophonous ([polian-2013]); Set B (ABS) markers cross-reference
the absolutive argument (intransitive subject and transitive patient), and
occur prefixally or suffixally by dialect and morphosyntactic context.
Canonical word order is VOA (verb-initial), though both arguments are
usually unpronounced unless topicalized or focused. 3rd person singular Set
B has no overt exponent (∅). Grammatical-function classification is shared
across Tseltalan (`Mayan.Tseltalan`).

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per [polian-2013]).
-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy)

namespace Tsotsil

open Mayan (MarkerSet MarkerLinearity ExponentTable)
open Agreement

-- Re-export shared Tseltalan types
export Mayan.Tseltalan (GramFunction)

/-! ### Argument positions -/

/-- Argument positions in a Tsotsil clause, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Case assignment for Tsotsil: `Mayan.caseTseltalan .Perf`
    (A → ERG, S/P → ABS); Tseltalan has no aspect-conditioned split. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.caseTseltalan .Perf

/-- Non-perfective case assignment for Tsotsil: identical to perfective
    (no aspect split, [polian-2013]). -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.caseTseltalan .Imp

/-! ### Absolutive position (LOW-ABS) -/

/-- Tsotsil's absolutive morphemes appear in low (post-stem) position when
    suffixal (Tseltalan is LOW-ABS). The prefixal-or-suffixal alternation is
    conditioned by morphosyntactic context (see `setBLinearity`); LOW-ABS
    refers to the structural position of the licensing head, not the linear
    position of every Set B exponent. -/
def absPosition : Mayan.ABSPosition := .low

/-! ### Agreement marker linearity -/

/-- Set A markers in Tsotsil are prefixal (per [aissen-polian-2025]
    Table 1; pan-Mayan invariant). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B markers in Tsotsil are prefixal or suffixal by dialect and
    morphosyntactic context ([aissen-polian-2025] Table 1) — the headline
    Tseltalan-internal divergence from Tseltal. -/
def setBLinearity : MarkerLinearity := .either

/-! ### Set A/B exponents (Zinacantec Tsotsil) -/

/-- Set A (ERG/GEN) exponents for Zinacantec Tsotsil ([polian-2013]) by
    following-segment environment: prefixes on the verb (ERG) or
    possessed noun (GEN) — `j-`/`a-`/`s-` pre-consonantally,
    `k-`/`av-`/`y-` pre-vocalically (same orientation as Tseltal; an
    earlier revision reversed the 1st-person pair). -/
def setAExponent : Morphology.Following → ExponentTable
  | .consonant =>
    [(.pn .first .Sing, [.pref "j"]), (.pn .second .Sing, [.pref "a"]),
     (.pn .third .Sing, [.pref "s"]), (.pn .first .Plur, [.pref "j"]),
     (.pn .second .Plur, [.pref "a"]), (.pn .third .Plur, [.pref "s"])]
  | .vowel =>
    [(.pn .first .Sing, [.pref "k"]), (.pn .second .Sing, [.pref "av"]),
     (.pn .third .Sing, [.pref "y"]), (.pn .first .Plur, [.pref "k"]),
     (.pn .second .Plur, [.pref "av"]), (.pn .third .Plur, [.pref "y"])]

/-- Set B (ABS) exponents for Zinacantec Tsotsil ([polian-2013]): 3rd
    person singular has zero exponence. The default `-o-` series is
    listed; harmonic variants (`-un`, `-at`, `-utik`, conditioned by the
    preceding stem vowel per Aissen/Haviland course materials — the
    cited Table 1 itself was not accessible for verification) are morph
    variants of the same suffixes, recorded here rather than as a
    second table. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, [.suff "on"]), (.pn .second .Sing, [.suff "ot"]),
   (.pn .third .Sing, []), (.pn .first .Plur, [.suff "otik"]),
   (.pn .second .Plur, [.suff "oxuk"]), (.pn .third .Plur, [.suff "ik"])]

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches per [kaufman-norman-1984] Table 8. **Not**
    pan-Mayan: see Mam exception via `Mayan.isStandard`. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some [] := rfl

/-! ### Extraction marking -/

namespace Extraction

/-- No Agent Focus morphology is required for A-extraction, consistent
    with Tsotsil being LOW-ABS. -/
def realize : ExtractionTarget → List (Morphology.Focus.Reflex Empty) :=
  fun _ => []

/-- WALS-style label: extraction is unmarked. -/
def strategy : ExtractionMarkingStrategy := .unmarked

end Extraction

end Tsotsil
