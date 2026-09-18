import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Phonology.Segmental.Defs
import Linglib.Syntax.Reflex
import Linglib.Syntax.Clause.ArgumentRole

/-!
# Tsotsil Agreement Fragment

Agreement morphology for Zinacantec Tsotsil (Tseltalan, Mayan)
([polian-2013]; [aissen-polian-2025]).

## Main declarations

* `Tsotsil.template`, `Tsotsil.assignCase`: the verbal complex, with Set B
  after the stem in citation order, and ergative-absolutive case in every aspect.
* `Tsotsil.setAExponent`, `Tsotsil.setBExponent`: Zinacantec Tsotsil
  exponent tables ([polian-2013]).
* `Tsotsil.Extraction.realize`: the optional, obviation-conditioned Agent Focus form
  under transitive-subject extraction.

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

## References

* [aissen-1999a]
* [aissen-polian-2025]
* [kaufman-norman-1984]
* [polian-2013]
-/


namespace Tsotsil

open Mayan (MarkerSet ExponentTable)
open Agreement

-- Re-export shared Tseltalan types
export Mayan.Tseltalan (GrammaticalFunction)

/-! ### The verbal complex -/

/-- The position classes of the Zinacantec Tsotsil verbal complex in citation order: the
aspect marker and Set A before the stem, Set B after it. Set B is prefixal in some dialects
and morphosyntactic contexts ([aissen-polian-2025]), a variation the single template does not
record. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setA], [.setB]⟩

/-- Tsotsil is ergative-absolutive in every aspect, with no aspect-conditioned split
([polian-2013]). -/
def assignCase : UD.Aspect → ArgumentRole → Case := fun _ ↦ Alignment.ergative.assignCase

/-! ### Set A/B exponents (Zinacantec Tsotsil) -/

/-- Set A (ERG/GEN) exponents for Zinacantec Tsotsil ([polian-2013]) by
    following-segment environment: prefixes on the verb (ERG) or
    possessed noun (GEN) — `j-`/`a-`/`s-` pre-consonantally,
    `k-`/`av-`/`y-` pre-vocalically (same orientation as Tseltal; an
    earlier revision reversed the 1st-person pair). -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.pn .first .singular, [.pref "j"]), (.pn .second .singular, [.pref "a"]),
     (.pn .third .singular, [.pref "s"]), (.pn .first .plural, [.pref "j"]),
     (.pn .second .plural, [.pref "a"]), (.pn .third .plural, [.pref "s"])]
  | .vowel =>
    [(.pn .first .singular, [.pref "k"]), (.pn .second .singular, [.pref "av"]),
     (.pn .third .singular, [.pref "y"]), (.pn .first .plural, [.pref "k"]),
     (.pn .second .plural, [.pref "av"]), (.pn .third .plural, [.pref "y"])]

/-- Set B (ABS) exponents for Zinacantec Tsotsil ([polian-2013]): 3rd
    person singular has zero exponence. The default `-o-` series is
    listed; harmonic variants (`-un`, `-at`, `-utik`, conditioned by the
    preceding stem vowel per Aissen/Haviland course materials — the
    cited Table 1 itself was not accessible for verification) are morph
    variants of the same suffixes, recorded here rather than as a
    second table. -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.suff "on"]), (.pn .second .singular, [.suff "ot"]),
   (.pn .third .singular, []), (.pn .first .plural, [.suff "otik"]),
   (.pn .second .plural, [.suff "oxuk"]), (.pn .third .plural, [.suff "ik"])]

/-- Third person singular Set B is null, as across the Mayan branches with an ergative
perfective ([kaufman-norman-1984]); San Juan Atitán Mam's default Set B surfaces there. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .singular) = some [] := rfl

/-! ### Extraction marking -/

namespace Extraction

/-- The host of the Tsotsil extraction reflex. -/
inductive Host where
  | verb
  deriving DecidableEq, Repr

/-- Transitive-subject extraction may switch the verb to the Agent Focus form. The form is
not obligatory, agents extracting from transitive and Agent Focus clauses alike, and it is used
when the patient outranks the agent in obviation ([aissen-1999a]); no other extraction is
marked. -/
def realize : ArgumentRole → Finset (Reflex Host)
  | .A => {.morpheme .verb}
  | _ => ∅

end Extraction

end Tsotsil
