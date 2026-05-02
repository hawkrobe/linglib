import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Qanjobal.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Tseltal.Agreement
import Linglib.Fragments.Mayan.Tsotsil.Agreement

/-!
# Cross-Mayan Alignment Typology
@cite{kaufman-norman-1984} @cite{coon-mateo-pedro-preminger-2014}
@cite{aissen-polian-2025} @cite{polian-2013}

Cross-Mayan typology theorems quantified over `Fragments.Mayan.MayanLang`,
made statable by the per-language Fragment shape consolidation
(Phases 1–6 of the Mayan agreement refactor). Each theorem replaces
what previously had to be enumerated as parallel `rfl` facts in
per-paper Studies.

## What this file is anchored on

- **Tada's Generalization** (the HIGH-ABS / syntactic-ergativity
  correlation) — empirically motivated by @cite{coon-mateo-pedro-preminger-2014}
  and the broader Mayan literature.
- **Pan-Mayan Set B 3sg null** — proto-Cholan reconstruction in
  @cite{kaufman-norman-1984} Table 8, holds across all the formalised
  Mayan fragments.
- **Pan-Mayan Set A prefixal** — @cite{aissen-polian-2025} Table 1
  (Tseltalan instance); the morphological position of Set A is
  uniformly prefixal across the formalised Mayan languages.
- **Pan-Mayan perfective ergative alignment** — the unmarked aspect
  is canonically ergative across all Mayan branches; aspect-conditioned
  splits affect only non-perfective aspects.

## Why this is not in `Phenomena/Ergativity/Typology.lean`

The directory rule (`feedback_no_phenomena_typology_lean`) bans
recreating `Phenomena/X/Typology.lean` files; cross-linguistic
theorems anchored on a documented empirical pattern instead live in a
topically-named file. This file is anchored on **Tada's Generalization**
plus the pan-Mayan agreement-paradigm invariants — a recognised
empirical literature, not an editorial synthesis.
-/

namespace Phenomena.Ergativity.MayanAlignment

open Fragments.Mayan (MayanLang PersonNumber MarkerLinearity ABSPosition)

-- ============================================================================
-- § 1: Per-Language Dispatchers
-- ============================================================================

/-- Set B exponent table indexed by Mayan language. Routes to the
    per-language `setBExponent` defined in each Fragment. Return type
    is `Fragments.Mayan.ExponentTable` (not the unfolded function type)
    to enable `.IsThirdSgZero` dot-notation. -/
def setBExponentOf : MayanLang → Fragments.Mayan.ExponentTable
  | .Chol      => Fragments.Mayan.Chol.setBExponent
  | .Qanjobal  => Fragments.Mayan.Qanjobal.setBExponent
  | .Kaqchikel => Fragments.Mayan.Kaqchikel.setBExponent
  | .Tseltal   => Fragments.Mayan.Tseltal.setBExponent
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setBExponent

/-- Set A exponent table (canonical / pre-consonantal allomorph) indexed
    by Mayan language. -/
def setAExponentOf : MayanLang → Fragments.Mayan.ExponentTable
  | .Chol      => Fragments.Mayan.Chol.setAExponent
  | .Qanjobal  => Fragments.Mayan.Qanjobal.setAExponent
  | .Kaqchikel => Fragments.Mayan.Kaqchikel.setAExponent
  | .Tseltal   => Fragments.Mayan.Tseltal.setAExponent
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setAExponent

/-- Set A linearity (uniformly prefixal across Mayan; see theorem below). -/
def setALinearityOf : MayanLang → MarkerLinearity
  | .Chol      => .prefixal
  | .Qanjobal  => .prefixal
  | .Kaqchikel => .prefixal
  | .Tseltal   => Fragments.Mayan.Tseltal.setALinearity
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setALinearity

/-- Set B linearity. Varies across Mayan: suffixal in Cholan, Q'anjob'alan,
    and Tseltal; prefixal in Kaqchikel (HIGH-ABS K'ichean); either in
    Tsotsil (dialectally and morphosyntactically conditioned). -/
def setBLinearityOf : MayanLang → MarkerLinearity
  | .Chol      => .suffixal
  | .Qanjobal  => .suffixal
  | .Kaqchikel => .prefixal
  | .Tseltal   => Fragments.Mayan.Tseltal.setBLinearity
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setBLinearity

/-- Absolutive structural position (HIGH-ABS / LOW-ABS) indexed by
    Mayan language. The substantive parameter for Tada's Generalization. -/
def absPositionOf : MayanLang → ABSPosition
  | .Chol      => Fragments.Mayan.Chol.absPosition
  | .Qanjobal  => Fragments.Mayan.Qanjobal.absPosition
  | .Kaqchikel => Fragments.Mayan.Kaqchikel.absPosition
  | .Tseltal   => Fragments.Mayan.Tseltal.absPosition
  | .Tsotsil   => Fragments.Mayan.Tsotsil.absPosition

-- ============================================================================
-- § 2: Pan-Mayan Set B 3sg Null Invariant (@cite{kaufman-norman-1984})
-- ============================================================================

/-- **Pan-Mayan Set B 3sg invariant**: across all formalised Mayan
    languages, the third-person singular Set B exponent is morphologically
    null. Replaces five parallel per-language `rfl` facts with one
    universally-quantified theorem.

    Notation differs by linearity (`"-∅"` for suffixal Set B,
    `"∅"` for prefixal); `IsThirdSgZero` is notation-agnostic. -/
theorem mayan_p3sg_abs_null (lang : MayanLang) :
    (setBExponentOf lang).IsThirdSgZero := by
  cases lang <;> decide

-- ============================================================================
-- § 3: Pan-Mayan Set A Uniformly Prefixal
-- ============================================================================

/-- **Pan-Mayan Set A linearity invariant**: Set A markers are prefixal
    across all formalised Mayan languages. The morphological-position
    pan-Mayan claim corresponding to the structural-position invariant
    that ergative is licensed by the highest functional head in the
    verbal extended projection. -/
theorem mayan_set_a_uniformly_prefixal (lang : MayanLang) :
    setALinearityOf lang = .prefixal := by
  cases lang <;> rfl

-- ============================================================================
-- § 4: Pan-Mayan Perfective Ergative Alignment
-- ============================================================================

/-- **Pan-Mayan perfective alignment invariant**: in perfective aspect,
    every formalised Mayan language assigns case canonically ergatively
    (A → ERG, S/P → ABS), regardless of any aspect-conditioned splits in
    non-perfective aspects. -/
theorem mayan_perfective_ergative
    (lang : MayanLang) (r : Features.Prominence.ArgumentRole) :
    Fragments.Mayan.caseAt lang .Perf r =
      Alignment.ergative.assignCase r := by
  cases lang <;> rfl

-- ============================================================================
-- § 5: Tada's Generalization (parameterized form lives in CMP 2014 Study)
-- ============================================================================

-- The Tada bridge theorem `hasSyntacticErgativity (toCaseLocus
-- (absPositionOf lang)) = true ↔ absPositionOf lang = .high` requires
-- CMP 2014's analytical apparatus (`subjectTrapped`, `objectMustExitVP`)
-- and so lives in `Phenomena/Ergativity/Studies/CoonMateoPedroPreminger2014.lean`,
-- where the `absPositionOf` dispatcher above is consumed by the
-- parameterized `mayan_tada` theorem. The data file consumes only
-- Fragment data, not paper-specific analyses.

end Phenomena.Ergativity.MayanAlignment
