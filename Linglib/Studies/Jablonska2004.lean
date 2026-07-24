import Linglib.Data.Examples.Jablonska2004
import Linglib.Studies.Svenonius2004

/-!
# Jabłońska (2004): When the Prefixes Meet the Suffixes

[jablonska-2004] specialises the lexical / superlexical distinction of
[svenonius-2004] to Polish. Her central claim: the interpretation of
superlexical *po-* (delimitative vs distributive vs inceptive) is
**verbalizer-sensitive** — it depends on the embedded verbalizer, with a
common semantic denominator across the readings. Her fn. 2 notes that
*na-* patterns with *po-* in its ability to stack (to occur in Asp3).

## Main definitions

* `analyses` — her classified examples: delimitative *po-* on a stative
  (fn. 21), inceptive *po-* on a psych stative ((54a)), inceptive *za-*
  on a low -ej- verbalizer stem ((53)).

## Main results

* `po_same_form_different_readings` — the same fragment morph *po-*
  carries different superlexical readings across analyses: the
  verbalizer-sensitivity datum.
* `superlexical_selects_imperfective` — all her superlexical
  derivations sit on imperfective stems, consistent with
  [svenonius-2004]'s diagnostic (56c).
-/

namespace Jablonska2004

open Semantics.Aspect (Perfectivity)
open Svenonius2004 (Analysis WellStacked)
open Polish.Verbs

/-- fn. 21: *po-siedzieć* 'sit for a while' — delimitative *po-* on the
    stative *siedzieć* (contra Młynarczyk's claim that delimitative
    *po-* avoids statives). -/
def aFn21 : Analysis :=
  ⟨Examples.fn21, siedziec, [(po, .superlexical .delimitative)]⟩

/-- (54a) *po-kochać* 'start loving' — *po-* fixing the left boundary
    of a state: an inceptive reading of the same prefix. -/
def a54a : Analysis :=
  ⟨Examples.ex_54a, kochac, [(po, .superlexical .inceptive)]⟩

/-- (53) *za-jaśnieć* 'start being bright' — inceptive *za-* on a low
    -ej- verbalizer stem; the reading is inchoation of a state, not of
    a becoming. -/
def a53 : Analysis :=
  ⟨Examples.ex_53, jasniec, [(za, .superlexical .inceptive)]⟩

/-- All analyses of this study. -/
def analyses : List Analysis := [aFn21, a54a, a53]

/-! ### Results -/

/-- The verbalizer-sensitivity datum: `aFn21` and `a54a` carry the same
    fragment morph *po-* with different superlexical readings
    (delimitative on the plain stative, inceptive on the psych
    stative). -/
theorem po_same_form_different_readings :
    aFn21.prefixes.map (·.1) = a54a.prefixes.map (·.1) ∧
      aFn21.prefixes.map (·.2) ≠ a54a.prefixes.map (·.2) := by
  exact ⟨rfl, by decide⟩

/-- All her superlexical derivations sit on imperfective stems,
    consistent with [svenonius-2004]'s diagnostic (56c). -/
theorem superlexical_selects_imperfective
    (a : Analysis) (ha : a ∈ analyses) :
    a.stem.perfectivity = Perfectivity.imperfective := by
  fin_cases ha <;> rfl

/-- The citation-form analyses match her hyphen segmentation ((53)
    *za-jaś-ni-e-ć* is segmented down to verbalizer suffixes and is
    excluded). -/
theorem analyses_match_segmentation
    (a : Analysis) (ha : a ∈ [aFn21, a54a]) :
    a.MatchesSegmentation := by
  fin_cases ha <;> decide

end Jablonska2004
