import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Qanjobal.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Tseltal.Agreement
import Linglib.Fragments.Mayan.Tsotsil.Agreement
import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Kiche.Agreement

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
  | .Mam       => Fragments.Mayan.Mam.setBExponent
  | .Kiche     => Fragments.Mayan.Kiche.setBExponent

/-- Set A exponent table (canonical / pre-consonantal allomorph) indexed
    by Mayan language. -/
def setAExponentOf : MayanLang → Fragments.Mayan.ExponentTable
  | .Chol      => Fragments.Mayan.Chol.setAExponent
  | .Qanjobal  => Fragments.Mayan.Qanjobal.setAExponent
  | .Kaqchikel => Fragments.Mayan.Kaqchikel.setAExponent
  | .Tseltal   => Fragments.Mayan.Tseltal.setAExponent
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setAExponent
  | .Mam       => Fragments.Mayan.Mam.setAExponent
  | .Kiche     => Fragments.Mayan.Kiche.setAExponent

/-- Set A linearity (uniformly prefixal across Mayan; see theorem below). -/
def setALinearityOf : MayanLang → MarkerLinearity
  | .Chol      => .prefixal
  | .Qanjobal  => .prefixal
  | .Kaqchikel => .prefixal
  | .Tseltal   => Fragments.Mayan.Tseltal.setALinearity
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setALinearity
  | .Mam       => Fragments.Mayan.Mam.setALinearity
  | .Kiche     => Fragments.Mayan.Kiche.setALinearity

/-- Set B linearity. Varies across Mayan: suffixal in Cholan, Q'anjob'alan,
    and Tseltal; prefixal in Kaqchikel and K'iche' (HIGH-ABS K'ichean) and
    Mam (HIGH-ABS pre-stem on Infl); either in Tsotsil (dialectally and
    morphosyntactically conditioned). -/
def setBLinearityOf : MayanLang → MarkerLinearity
  | .Chol      => .suffixal
  | .Qanjobal  => .suffixal
  | .Kaqchikel => .prefixal
  | .Tseltal   => Fragments.Mayan.Tseltal.setBLinearity
  | .Tsotsil   => Fragments.Mayan.Tsotsil.setBLinearity
  | .Mam       => Fragments.Mayan.Mam.setBLinearity
  | .Kiche     => Fragments.Mayan.Kiche.setBLinearity

/-- Absolutive structural position (HIGH-ABS / LOW-ABS) indexed by
    Mayan language. The substantive parameter for Tada's Generalization. -/
def absPositionOf : MayanLang → ABSPosition
  | .Chol      => Fragments.Mayan.Chol.absPosition
  | .Qanjobal  => Fragments.Mayan.Qanjobal.absPosition
  | .Kaqchikel => Fragments.Mayan.Kaqchikel.absPosition
  | .Tseltal   => Fragments.Mayan.Tseltal.absPosition
  | .Tsotsil   => Fragments.Mayan.Tsotsil.absPosition
  | .Mam       => Fragments.Mayan.Mam.absPosition
  | .Kiche     => Fragments.Mayan.Kiche.absPosition

-- ============================================================================
-- § 2: Pan-Mayan Set B 3sg Null Invariant (@cite{kaufman-norman-1984})
-- ============================================================================

/-- **Pan-Mayan Set B 3sg invariant** (standard languages): across the
    formalised Mayan languages with the **standard ergative-absolutive
    base** (Cholan, Q'anjob'alan, Tseltalan, K'ichean — i.e., all except
    Mam), the third-person singular Set B exponent is morphologically
    null. Replaces parallel per-language `rfl` facts with one
    universally-quantified theorem.

    Notation differs by linearity (`"-∅"` for suffixal Set B,
    `"∅"` for prefixal); `IsThirdSgZero` is notation-agnostic.

    **Mam exception**: per @cite{scott-2023}, San Juan Atitán Mam's
    Set B 3sg surfaces as the default `tz'=` form (not null) — see
    `mam_set_b_3sg_not_null` below. This theorem hypothesizes
    `lang.isStandard = true` to scope around the exception. -/
theorem mayan_p3sg_abs_null (lang : MayanLang) (h : lang.isStandard = true) :
    (setBExponentOf lang).IsThirdSgZero := by
  cases lang <;> first | decide | (simp [MayanLang.isStandard] at h)

/-- The Mam exception to the pan-Mayan Set B 3sg null invariant: Mam's
    default Set B `tz'=` surfaces in the 3sg slot, not a null morpheme. -/
theorem mam_set_b_3sg_not_null :
    ¬ (setBExponentOf .Mam).IsThirdSgZero := by decide

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

/-- **Pan-Mayan perfective alignment invariant** (standard languages):
    in perfective aspect, every formalised Mayan language with the
    standard ergative-absolutive base assigns case canonically
    ergatively (A → ERG, S/P → ABS), regardless of any aspect-conditioned
    splits in non-perfective aspects.

    **Mam exception**: per @cite{scott-2023}, Mam is morphologically
    tripartite — `caseMam .Perf .P = .acc`, not `.abs`. The substrate
    surfaces this falsification when Mam is in scope; this theorem
    hypothesizes `lang.isStandard = true` to scope around it. See
    `mam_is_tripartite_in_perfective` for the contrast. -/
theorem mayan_perfective_ergative
    (lang : MayanLang) (h : lang.isStandard = true)
    (r : Features.Prominence.ArgumentRole) :
    Fragments.Mayan.caseAt lang .Perf r =
      Alignment.ergative.assignCase r := by
  cases lang <;> first | rfl | (simp [MayanLang.isStandard] at h)

/-- The Mam exception to pan-Mayan ergative perfective alignment:
    `caseMam .Perf .P = .acc` (tripartite, not ergative). -/
theorem mam_is_tripartite_in_perfective :
    Fragments.Mayan.caseAt .Mam .Perf .P =
      Alignment.tripartite.assignCase .P := rfl

-- ============================================================================
-- § 5: Tada's Generalization (parameterized form lives in CMP 2014 Study)
-- ============================================================================

-- The Tada bridge theorem `hasSyntacticErgativity (toCaseLocus
-- (absPositionOf lang)) = true ↔ absPositionOf lang = .high` requires
-- CMP 2014's analytical apparatus (`subjectTrapped`, `objectMustExitVP`)
-- and so lives in `Studies/CoonMateoPedroPreminger2014.lean`,
-- where the `absPositionOf` dispatcher above is consumed by the
-- parameterized `mayan_tada` theorem. The data file consumes only
-- Fragment data, not paper-specific analyses.

end Phenomena.Ergativity.MayanAlignment
