import Linglib.Theories.Phonology.Templates
import Linglib.Fragments.Hebrew.ConsonantalRoots
import Linglib.Fragments.Amharic.ConsonantalRoots

/-!
# Faust (2026) — Intrusion as Template Satisfaction
@cite{faust-2026} @cite{mccarthy-1981} @cite{broselow-1984}
@cite{lowenstamm-1996} @cite{lowenstamm-2014}

Faust, Noam. 2026. *Intrusion as template satisfaction and the
QaTaT–QaTa problem in Semitic.* Linguistic Inquiry 57(2): 427–441.
https://doi.org/10.1162/ling_a_00524

## Core contribution

A single alignment principle, **\*Misalignment**, jointly resolves two
puzzles in Semitic templatic morphology:

1. **The QaTaT–QaTa problem** (Hebrew). Triradical [j]-final roots like √klj
   would be predicted by template satisfaction (@cite{mccarthy-1981}) to
   spread the medial radical to the final C-slot, yielding \*[kalal]. They
   surface instead as [kala], with an empty final C-slot.
   @cite{faust-2026} (4): the missing form is ruled out because spreading
   would put the *nonfinal* root segment /l/ in the *template-final*
   position, violating \*Misalignment.

2. **Amharic [t]-intrusion** (@cite{broselow-1984}). The [t] in Amharic
   gerund [fädʤto] and INF forms is reanalyzed not as a default consonant
   inserted to satisfy the template (@cite{broselow-1984}'s account), but
   as the feminine-gender suffix /t/ — a sister bound root in the sense of
   @cite{lowenstamm-2014} — which satisfies the template *without* being a
   nonfinal root segment, hence not violating \*Misalignment. The strategy
   is unavailable for verbal forms because gender markers are inherent on
   n, not contextual on V/Agr (@cite{faust-2026} (11)).

## Architectural integration

This file is the first study to consume the new shared infrastructure:

- `Core.Morphology.Root` — single source of truth for consonantal roots,
  parametric over the segment type.
- `Phonology.Templates` — `CVSlot`, `Template`, `Association`,
  `RootTemplateMatch`, with the derived `isMisaligned` predicate.
- `Phonology.Templates.starMisalign` — the \*Misalignment alignment
  constraint, built from the generic `mkAlign` constructor in
  `Phonology.Constraints`.

All four canonical derivations (Hebrew \*[kalal], Hebrew [tadmit],
Amharic [fädʤä], Amharic [fädʤto]) are evaluated by `decide` on the
shared types — no local re-stipulation.
-/

namespace Phenomena.TemplaticMorphology.Studies.Faust2026

open Core.Morphology
open Phonology.Templates

-- ============================================================================
-- § 1: Hebrew templates
-- ============================================================================

/-- The Hebrew PST.3MSG verbal template `CaCaC[+c]`
    (@cite{faust-2026} (1), (3a–c), (4)). Five slots; the final C-slot
    is [+consonantal], blocking association from the glide /j/. -/
def hebrewPst3msg : Template :=
  ⟨[.C, .V, .C, .V, .Cspec]⟩

/-- The Hebrew passive-participle template `CaCuC` (@cite{faust-2026} (3c)
    discussion). Five slots; the final C-slot is *not* [+c]-specified, so
    the glide /j/ can associate to it freely (yielding [kaluj], [tʃamuj]). -/
def hebrewPassPrtcpl : Template :=
  ⟨[.C, .V, .C, .V, .C]⟩

/-- The Hebrew nominal template `taQTiL[+c]` (@cite{faust-2026} (9)–(10)):
    six slots, the leading `taQ` morphologically prefixed via the n[+gen]
    head. The final C-slot is [+c], so [j]-final roots (like √dmj) cannot
    satisfy it directly — but the feminine /t/ exponent intrudes
    (@cite{faust-2026} (10b–c)). -/
def hebrewTaQTiL : Template :=
  ⟨[.C, .V, .C, .C, .V, .Cspec]⟩

-- ============================================================================
-- § 2: Amharic templates
-- ============================================================================

/-- The Amharic PFV.3MSG verbal template (type-A pattern `CäC.CäC[+c]`,
    @cite{faust-2026} (5), (7)). Final C-slot [+c]; the medial C is
    geminated in the surface paradigm (modeled here as a doubled C; the
    \*Misalignment argument is independent of gemination). -/
def amharicPfv3msg : Template :=
  ⟨[.C, .V, .C, .C, .V, .Cspec]⟩

/-- The Amharic gerund template `CäC.C-o` (@cite{faust-2026} (8)).
    Final slot is V (the -o suffix), with the medial C doubled. The penult
    C-slot is [+c]-specified — this is where the [t]-intruder lands when
    the root is [j]-final. -/
def amharicGrnd : Template :=
  ⟨[.C, .V, .C, .Cspec, .V]⟩

-- ============================================================================
-- § 3: Hebrew derivations — the QaTaT–QaTa problem (@cite{faust-2026} (4))
-- ============================================================================

/-- Candidate (4) of @cite{faust-2026}: \*[kalal] derivation of √klj +
    `CaCaC[+c]` via spreading. The medial /l/ at root index 1 is
    spread to the final [+c] C-slot at template index 4. This is the
    candidate that template satisfaction predicts. -/
def hebrewKlj_kalal : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klj
    template := hebrewPst3msg
    associations :=
      [⟨.root, 0, 0⟩,   -- k → C0
       ⟨.root, 1, 2⟩,   -- l → C2
       ⟨.root, 1, 4⟩] } -- l → Cspec4 (spread, nonfinal-to-final)

/-- The actual surface form [kala]: only k and l associate; the final
    [+c] slot is left unfilled because /j/ cannot satisfy [+c] and
    spreading /l/ would violate \*Misalignment. -/
def hebrewKlj_kala : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klj
    template := hebrewPst3msg
    associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 2⟩] }

/-- The passive participle [kaluj]: /j/ surfaces because the final C-slot
    is not [+c]-specified, so direct association succeeds and no spreading
    is needed. -/
def hebrewKlj_kaluj : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klj
    template := hebrewPassPrtcpl
    associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 2⟩, ⟨.root, 2, 4⟩] }

-- ============================================================================
-- § 4: Hebrew derivation — taQTiL templatic intrusion (@cite{faust-2026} (10))
-- ============================================================================

/-- The illicit derivation (@cite{faust-2026} (10a)): √dmj associated
    directly to taQTiL[+c]. The /j/ at root index 2 fails to fill the
    [+c] final slot, but spreading /m/ there would put a nonfinal root
    segment in template-final position. (Modeled here as the spreading
    candidate.) -/
def hebrewDmj_illicit : RootTemplateMatch String :=
  { root := Fragments.Hebrew.dmj
    template := hebrewTaQTiL
    associations :=
      [⟨.root, 0, 0⟩,   -- d → C0
       ⟨.root, 1, 2⟩,   -- m → C2
       ⟨.root, 1, 5⟩] } -- m → Cspec5 (spread, nonfinal-to-final)

/-- The licit [tadmit] derivation (@cite{faust-2026} (10b–c)): the
    feminine n[+gen] exponent /t/ is added as a sister bound root, and
    its /t/ associates to the final [+c] C-slot. Because this is an
    *intruder* association (not a `.root` association), \*Misalignment
    does not fire. -/
def hebrewDmj_tadmit : RootTemplateMatch String :=
  { root := Fragments.Hebrew.dmj
    template := hebrewTaQTiL
    associations :=
      [⟨.root, 0, 0⟩,        -- d → C0
       ⟨.root, 1, 2⟩,        -- m → C2
       ⟨.root, 2, 3⟩,        -- j → C3 (medial C, not [+c])
       ⟨.intruder, 0, 5⟩] }  -- /t/ intruder → Cspec5

-- ============================================================================
-- § 5: Amharic derivations — verbal vs nominal (@cite{faust-2026} (7), (8))
-- ============================================================================

/-- Amharic [fädʤ-ä] PFV.3MSG: √fdj in `CäC.CäC[+c]`. The /j/ at root
    index 2 palatalizes /d/ at root index 1 (modeled as /j/ associating
    to the medial C-slot, paralleling the Cspec slot occupant via
    spreading of /d/). \*Misalignment is satisfied because the spread
    /d/ is the *medial* radical, but the template-final slot — which
    would have hosted /j/ if /j/ qualified for [+c] — is empty here, so
    no nonfinal root element occupies it. -/
def amharicFdj_pfv : RootTemplateMatch String :=
  { root := Fragments.Amharic.fdj
    template := amharicPfv3msg
    associations :=
      [⟨.root, 0, 0⟩,   -- f → C0
       ⟨.root, 1, 2⟩,   -- d → C2
       ⟨.root, 1, 3⟩,   -- d → C3 (gemination, also nonfinal — but slot 3 is not final)
       ⟨.root, 2, 4⟩] } -- j → V4 (palatality merges with vowel; modelled as V-association)

/-- Amharic gerund [fädʤto] (@cite{faust-2026} (8)): the feminine /t/
    intruder fills the [+c] penult slot, and the final V slot hosts -o.
    Because /t/ is an intruder (not a root segment), \*Misalignment
    does not block it. -/
def amharicFdj_grnd : RootTemplateMatch String :=
  { root := Fragments.Amharic.fdj
    template := amharicGrnd
    associations :=
      [⟨.root, 0, 0⟩,         -- f → C0
       ⟨.root, 1, 2⟩,         -- d → C2
       ⟨.intruder, 0, 3⟩] }   -- /t/ intruder → Cspec3

-- ============================================================================
-- § 6: Theorems — *Misalignment derives the empirical pattern
-- ============================================================================

/-! ### Hebrew QaTaT–QaTa (@cite{faust-2026} (4))

The spreading candidate \*[kalal] is misaligned; the empty-slot
candidate [kala] is not. The correct surface form is the one not
ruled out by \*Misalignment. -/

theorem hebrew_kalal_misaligned :
    hebrewKlj_kalal.isMisaligned = true := by decide

theorem hebrew_kala_not_misaligned :
    hebrewKlj_kala.isMisaligned = false := by decide

/-- The passive participle [kaluj] is also unproblematic: the final
    C-slot is not [+c]-specified, so /j/ associates directly and no
    spreading occurs — \*Misalignment trivially satisfied. -/
theorem hebrew_kaluj_not_misaligned :
    hebrewKlj_kaluj.isMisaligned = false := by decide

/-! ### Hebrew taQTiL intrusion (@cite{faust-2026} (10)) -/

/-- The illicit [tadmij]-style derivation (no intruder, spreading /m/)
    is misaligned: nonfinal /m/ landed at the template-final slot. -/
theorem hebrew_dmj_illicit_misaligned :
    hebrewDmj_illicit.isMisaligned = true := by decide

/-- The licit [tadmit] derivation, with the feminine /t/ intruder
    occupying the final [+c] slot, is not misaligned. The intruder
    association is exempt from \*Misalignment. -/
theorem hebrew_tadmit_not_misaligned :
    hebrewDmj_tadmit.isMisaligned = false := by decide

/-! ### Amharic verbal vs nominal (@cite{faust-2026} (8)) -/

theorem amharic_fdj_pfv_not_misaligned :
    amharicFdj_pfv.isMisaligned = false := by decide

theorem amharic_fdj_grnd_not_misaligned :
    amharicFdj_grnd.isMisaligned = false := by decide

-- ============================================================================
-- § 7: Cross-derivation theorems — the squib's main claims
-- ============================================================================

/-- @cite{faust-2026}'s central observation about Hebrew (4): for the
    same root √klj and template `CaCaC[+c]`, the spreading candidate
    violates \*Misalignment while the empty-slot candidate does not. The
    grammar must therefore prefer the empty slot. -/
theorem hebrew_klj_spreading_blocked_by_misalignment :
    hebrewKlj_kalal.isMisaligned = true ∧
    hebrewKlj_kala.isMisaligned = false := by
  exact ⟨by decide, by decide⟩

/-- @cite{faust-2026}'s analytical move on Hebrew (10): templatic
    intrusion via the feminine /t/ is licit precisely because the
    intruder is not a root segment, so \*Misalignment doesn't apply
    to it. Compare a non-intruder derivation (which would be
    misaligned) to the actual [tadmit] form. -/
theorem hebrew_intrusion_satisfies_template_without_misalignment :
    hebrewDmj_illicit.isMisaligned = true ∧
    hebrewDmj_tadmit.isMisaligned = false := by
  exact ⟨by decide, by decide⟩

/-- @cite{faust-2026}'s parallel claim about Amharic (5)/(8):
    [t]-intrusion is licit in nominal templates (gerund) for the same
    reason it's licit in Hebrew taQTiL — the intruder is not a root
    segment. -/
theorem amharic_intrusion_not_misaligned :
    amharicFdj_grnd.isMisaligned = false := by decide

/-- The squib's core analytical claim, in one statement: across both
    languages and both phenomena, every form claimed to surface satisfies
    \*Misalignment, while every form claimed to be ruled out violates it. -/
theorem misalignment_predicts_all_four_cases :
    -- ruled out
    hebrewKlj_kalal.isMisaligned = true ∧
    hebrewDmj_illicit.isMisaligned = true ∧
    -- surfaces
    hebrewKlj_kala.isMisaligned = false ∧
    hebrewDmj_tadmit.isMisaligned = false ∧
    amharicFdj_pfv.isMisaligned = false ∧
    amharicFdj_grnd.isMisaligned = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 8: Connection to Kramer 2020 (gender on n)
-- ============================================================================

/-! ### Cross-domain integration with @cite{kramer-2020}

@cite{faust-2026} (11) attributes the nominal-only distribution of
[t]-intrusion to the structural fact that gender is realized on the
nominalizing head n in nouns (cf. @cite{kramer-2020}'s `n[+gen]`),
whereas in verbs gender is realized on a higher Agr head (contextual
agreement, not inherent inflection). The intruder /t/ is precisely
the exponent of `n[+gen]`, and the bound-root analysis of
@cite{lowenstamm-2014} is what makes this exponent available for
template satisfaction. The structural piece (n vs. Agr) is verified
in `Phenomena/Gender/Studies/Kramer2020.lean`; the prosodic piece
(intrusion ⇒ no \*Misalignment violation) is verified here. -/

end Phenomena.TemplaticMorphology.Studies.Faust2026
