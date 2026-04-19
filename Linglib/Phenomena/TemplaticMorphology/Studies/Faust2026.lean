import Linglib.Theories.Phonology.Prosodic.Templates
import Linglib.Theories.Phonology.Constraints
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Fragments.Hebrew.ConsonantalRoots
import Linglib.Fragments.Amharic.ConsonantalRoots

/-!
# Faust (2026) — Intrusion as Template Satisfaction
@cite{faust-2026} @cite{mccarthy-1981} @cite{broselow-1984}
@cite{lowenstamm-1996} @cite{lowenstamm-2014} @cite{kramer-2020}

Faust, Noam. 2026. *Intrusion as template satisfaction and the
QaTaT–QaTa problem in Semitic.* Linguistic Inquiry 57(2): 427–441.
https://doi.org/10.1162/ling_a_00524

## Core contribution

A single alignment principle, **\*Misalignment** — "a nonfinal root
element must not be template-final" (@cite{faust-2026} (2)/(6b)) —
jointly resolves three Semitic puzzles:

1. **The QaTaT–QaTa gap** (Modern Hebrew). Triradical [j]-final roots
   like √klj `roast` would be predicted by template satisfaction
   (@cite{mccarthy-1981}) to fill the [+c]-specified template-final
   slot via *spreading* of the medial radical /l/, yielding \*[kalal].
   They surface instead as [kala] with an *unfilled* C-slot
   (@cite{faust-2026} (3c), (4)). \*Misalignment derives this:
   spreading /l/ to template-final would put a *nonfinal* root
   element in template-final position. The grammar tolerates an
   unfilled C-slot rather than violate \*Misalignment.

2. **Amharic [t]-intrusion** (@cite{broselow-1984}). The [t] in
   Amharic gerund [fädʤto] and INF forms is reanalyzed not as a
   default consonant inserted to satisfy the template
   (@cite{broselow-1984}), but as the feminine /t/ — the n[+gen]
   exponent realized as a sister bound root in the sense of
   @cite{lowenstamm-2014} — which satisfies the template *without*
   being a nonfinal root segment, hence not violating \*Misalignment.
   The strategy is unavailable for verbal forms because gender
   markers are *inherent* on n, not contextual on Agr
   (@cite{faust-2026} (11) — connects to @cite{kramer-2020}).

3. **Apparent OCP-violating Amharic biradicals** are reanalyzed.
   @cite{broselow-1984} concluded that Amharic admits OCP-violating
   √TT roots like √dd for [wäddäd-ä] `liked`. @cite{faust-2026}
   (page 432) shows: once `scorch`-type verbs are reanalyzed as
   triradical (√fdj, not biradical √fd), there is no remaining
   reason to posit OCP-violating roots. The [wäddäd-ä] form is based
   on biradical √wd, where /w/ ≠ /d/ — the surface gemination is a
   *template-spreading effect*, and \*Misalignment is satisfied
   because the spread /d/ is the *final* root segment.

## Architectural integration

This file consumes and exercises the shared infrastructure:

- `Core.Morphology.Root` — polymorphic consonantal-root carrier.
- `Phonology.Templates` — `CVSlot`, `Template`, `Association`,
  `RootTemplateMatch`, with derived `isMisaligned`, `allCSlotsFilled`,
  `satisfies`.
- `Phonology.Templates.starMisalign` — the \*Misalignment alignment
  constraint, built via the generic `mkAlign` constructor.
- `Phonology.Constraints.adjacentIdentical` — drives the root-level
  OCP, used to verify @cite{faust-2026}'s OCP-related reanalysis.

Per-derivation `decide` theorems test all four combinations of
`isMisaligned ∈ {true, false} × allCSlotsFilled ∈ {true, false}`,
making the central squib claim — *Misalignment-violating candidates
are blocked even when they satisfy the template* — visible at the
type level rather than restated in prose.
-/

namespace Phenomena.TemplaticMorphology.Studies.Faust2026

open Core.Morphology
open Phonology.Templates

-- ============================================================================
-- § 1: Hebrew templates (@cite{faust-2026} (1), (3), (9)–(10))
-- ============================================================================

/-- The Hebrew PST.3MSG verbal template `CaCaC[+c]` (@cite{faust-2026}
    (1), (3a–c), (4)). Five slots; the final C-slot is [+consonantal],
    blocking association from the glide /j/. -/
def hebrewPst3msg : Template :=
  ⟨[.C, .V, .C, .V, .Cspec]⟩

/-- The Hebrew passive-participle template `CaCuC` (@cite{faust-2026}
    (3c) discussion). Five slots; the final C-slot is *not*
    [+c]-specified, so the glide /j/ associates to it freely
    (yielding [kaluj], [tʃamuj]). -/
def hebrewPassPrtcpl : Template :=
  ⟨[.C, .V, .C, .V, .C]⟩

/-- The Hebrew nominal template `taQTiL[+c]` (@cite{faust-2026} (9)–(10)):
    six slots `C V C C V C[+c]`. The first `C V` (= "ta") is realized
    by the n[+gen]-internal /t/ exponent and template vocalization;
    the medial `C C` hosts the first two root radicals; the final
    `C[+c]` is the slot that hosts the intruding feminine /t/ in the
    feminine-noun reading (@cite{faust-2026} (10b–c)). -/
def hebrewTaQTiL : Template :=
  ⟨[.C, .V, .C, .C, .V, .Cspec]⟩

-- ============================================================================
-- § 2: Amharic templates (@cite{faust-2026} (5), (7)–(8), (12)–(13))
-- ============================================================================

/-- The Amharic PFV.3MSG verbal template (type-A pattern `CäC.CäC[+c]`,
    @cite{faust-2026} (5), (7)). Six slots `C V C C V C[+c]`; the
    medial geminate `C C` is the position where Amharic spreads its
    second radical, and the final C-slot is [+c]. The verbal -ä
    person-marking suffix attaches outside this template. -/
def amharicPfv3msg : Template :=
  ⟨[.C, .V, .C, .C, .V, .Cspec]⟩

/-- The Amharic gerund template `CäC.C[+c]-o` (@cite{faust-2026} (8)).
    Five slots: the final `V` hosts the gerund [-o] suffix; the
    penult `C[+c]` is where the [t]-intruder lands when the root is
    [j]-final. -/
def amharicGrnd : Template :=
  ⟨[.C, .V, .C, .Cspec, .V]⟩

-- ============================================================================
-- § 3: Hebrew QaTaT–QaTa (@cite{faust-2026} (3), (4))
-- ============================================================================

/-! ### The three-way QaTaT–QaTa contrast (@cite{faust-2026} (3))

@cite{faust-2026} (3) presents three Modern Hebrew verbs sharing the
same `CaCaC[+c]` template:

- (3a) [kalat] from √klt — full triradical, all radicals surface.
- (3b) [kalal] from √kll — final radical /l/ spreads/associates to
  template-final; legitimate because the spreading segment IS the
  final root segment (no \*Misalignment violation).
- (3c) [kala]  from √klj — analogous spreading would put nonfinal /l/
  at template-final; \*Misalignment blocks it, so the [+c] slot is
  left unfilled and the surface form has only two consonants.

The squib's analytical move: (3b) and (3c) look superficially
*identical* — both would (or do) involve the medial radical surfacing
in the final position — but \*Misalignment discriminates by *which root
index* the template-final segment came from. -/

/-- (3a) [kalat] from √klt: full triradical control case. Every
    root segment associates to a distinct template C-slot; no spreading,
    no misalignment. -/
def hebrewKlt_kalat : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klt
    template := hebrewPst3msg
    associations :=
      [⟨.root, 0, 0⟩,    -- k → C0
       ⟨.root, 1, 2⟩,    -- l → C2
       ⟨.root, 2, 4⟩] }  -- t → C[+c]4

/-- (3b) [kalal] from √kll: the *attested* QaTaT pattern. The final
    /l/ at root index 2 associates to template-final C[+c]; this is the
    final-of-final case and \*Misalignment is satisfied. -/
def hebrewKll_kalal : RootTemplateMatch String :=
  { root := Fragments.Hebrew.kll
    template := hebrewPst3msg
    associations :=
      [⟨.root, 0, 0⟩,    -- k → C0
       ⟨.root, 1, 2⟩,    -- l → C2
       ⟨.root, 2, 4⟩] }  -- l (final root segment!) → C[+c]4

/-- Candidate (4) of @cite{faust-2026}: the *spreading* derivation of
    \*[kalal] from √klj + `CaCaC[+c]`. The medial /l/ at root
    index 1 is spread to the [+c] template-final slot (template
    index 4). This is the candidate template satisfaction predicts;
    @cite{faust-2026} (4) shows it is ruled out by \*Misalignment. -/
def hebrewKlj_kalal : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klj
    template := hebrewPst3msg
    associations :=
      [⟨.root, 0, 0⟩,    -- k → C0
       ⟨.root, 1, 2⟩,    -- l → C2
       ⟨.root, 1, 4⟩] }  -- l → C[+c]4 (spread, NONFINAL → FINAL)

/-- The actual surface form [kala] (@cite{faust-2026} (3c)): only /k/
    and /l/ associate; the [+c] template-final slot is left unfilled
    because /j/ cannot satisfy [+c] and spreading /l/ would violate
    \*Misalignment. The grammar tolerates the unfilled C-slot. -/
def hebrewKlj_kala : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klj
    template := hebrewPst3msg
    associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 2⟩] }

/-- The passive participle [kaluj] (@cite{faust-2026} (3c)): /j/
    surfaces because the final C-slot is *not* [+c]-specified, so
    direct association succeeds and no spreading is required —
    \*Misalignment trivially satisfied, all C-slots filled. -/
def hebrewKlj_kaluj : RootTemplateMatch String :=
  { root := Fragments.Hebrew.klj
    template := hebrewPassPrtcpl
    associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 2⟩, ⟨.root, 2, 4⟩] }

-- ============================================================================
-- § 4: Hebrew taQTiL templatic intrusion (@cite{faust-2026} (10))
-- ============================================================================

/-- The illicit derivation (@cite{faust-2026} (10a)): √dmj associated
    directly to taQTiL[+c]. The prefix /t/ fills C0 (intruder, since
    it belongs to the template-internal "ta" exponent rather than
    √dmj), the root /d/ and /m/ fill C2 and C3 respectively, and to
    fill the [+c] final slot we attempt to spread /m/ — but /m/ is
    nonfinal in √dmj, so this violates \*Misalignment. -/
def hebrewDmj_illicit : RootTemplateMatch String :=
  { root := Fragments.Hebrew.dmj
    template := hebrewTaQTiL
    associations :=
      [⟨.intruder, 0, 0⟩,   -- prefix /t/ (template-internal "ta")
       ⟨.root, 0, 2⟩,       -- d → C2
       ⟨.root, 1, 3⟩,       -- m → C3
       ⟨.root, 1, 5⟩] }     -- m → C[+c]5 (spread, NONFINAL → FINAL)

/-- The licit [tadmit] derivation (@cite{faust-2026} (10b–c)): the
    feminine n[+gen] exponent /t/ is added as a sister bound root,
    and its /t/ associates from the right to the [+c] final C-slot.
    Both the prefix /t/ at C0 and the suffix /t/ at C5 are *intruder*
    associations (not part of √dmj), so \*Misalignment doesn't fire
    on either; the root /d/ and /m/ occupy nonfinal C-slots. -/
def hebrewDmj_tadmit : RootTemplateMatch String :=
  { root := Fragments.Hebrew.dmj
    template := hebrewTaQTiL
    associations :=
      [⟨.intruder, 0, 0⟩,   -- prefix /t/ (template-internal "ta")
       ⟨.root, 0, 2⟩,       -- d → C2
       ⟨.root, 1, 3⟩,       -- m → C3
       ⟨.intruder, 1, 5⟩] } -- suffix /t/ from √at[+gen] → C[+c]5

-- ============================================================================
-- § 5: Amharic /j/-final verbal forms (@cite{faust-2026} (5), (7))
-- ============================================================================

/-- Amharic [fädʤ-ä] PFV.3MSG: √fdj in `CäC.CäC[+c]`. Following
    @cite{faust-2026} (7a) with truncation: /f/ → C0, /d/ → C2 (and
    spreads to C3 for gemination), /j/ has *no slot* — its palatality
    merges with the preceding /d/ to yield [dʒ], and the penult V
    plus final C[+c] are truncated in the surface form. The unfilled
    final C-slot is precisely what the squib's analysis predicts. -/
def amharicFdj_pfv : RootTemplateMatch String :=
  { root := Fragments.Amharic.fdj
    template := amharicPfv3msg
    associations :=
      [⟨.root, 0, 0⟩,   -- f → C0
       ⟨.root, 1, 2⟩,   -- d → C2
       ⟨.root, 1, 3⟩] } -- d → C3 (gemination; /d/ is nonfinal but slot 3 is nonfinal too)

/-- Amharic gerund [fädʤto] (@cite{faust-2026} (8)): the feminine /t/
    intruder fills the [+c] penult slot, and the final V slot hosts
    the gerund [-o] suffix. Because /t/ is an intruder (not a root
    segment), \*Misalignment does not block it. -/
def amharicFdj_grnd : RootTemplateMatch String :=
  { root := Fragments.Amharic.fdj
    template := amharicGrnd
    associations :=
      [⟨.root, 0, 0⟩,        -- f → C0
       ⟨.root, 1, 2⟩,        -- d → C2
       ⟨.intruder, 0, 3⟩] }  -- /t/ intruder → C[+c]3

-- ============================================================================
-- § 6: Faust's biradical reanalysis — Amharic [wäddäd-ä] (page 432)
-- ============================================================================

/-- Amharic [wäddäd-ä] `liked` PFV.3MSG: √wd is *biradical*
    (@cite{faust-2026} page 432). /w/ → C0; /d/ → C2 (and spreads to
    C3 for gemination, and to C[+c]5 to fill the final slot). The
    spread of /d/ to template-final is *licit* under \*Misalignment
    because /d/ is at root index 1, the **final** root segment of
    √wd — there is no nonfinal-to-final misalignment. This is the
    type-level demonstration that the surface contrast between
    [wäddäd-ä] (biradical, OK) and \*[kalal] (triradical, blocked)
    falls out of \*Misalignment alone, with no need for OCP-violating
    roots. -/
def amharicWd_pfv : RootTemplateMatch String :=
  { root := Fragments.Amharic.wd
    template := amharicPfv3msg
    associations :=
      [⟨.root, 0, 0⟩,   -- w → C0
       ⟨.root, 1, 2⟩,   -- d → C2
       ⟨.root, 1, 3⟩,   -- d → C3 (gemination)
       ⟨.root, 1, 5⟩] } -- d → C[+c]5 (spread, FINAL → FINAL — OK!)

-- ============================================================================
-- § 7: Theorems — *Misalignment derives the empirical pattern
-- ============================================================================

/-! ### Hebrew QaTaT–QaTa (@cite{faust-2026} (3), (4)) -/

/-- (3a) [kalat] from √klt: the full-triradical control case satisfies
    everything — every C-slot filled, no \*Misalignment. -/
theorem hebrew_kalat_satisfies :
    hebrewKlt_kalat.satisfies = true := by decide

/-- (3b) [kalal] from √kll: the *attested* QaTaT pattern satisfies the
    template (every C-slot filled) AND respects \*Misalignment, because
    the segment at template-final is /l/ at *root index 2* — the final
    root segment, so no nonfinal-to-final misalignment fires. -/
theorem hebrew_kll_kalal_satisfies :
    hebrewKll_kalal.satisfies = true := by decide

/-- (4) The spreading candidate \*[kalal] from √klj is misaligned. -/
theorem hebrew_kalal_misaligned :
    hebrewKlj_kalal.isMisaligned = true := by decide

/-- (3c) The empty-slot candidate [kala] from √klj is not misaligned. -/
theorem hebrew_kala_not_misaligned :
    hebrewKlj_kala.isMisaligned = false := by decide

/-- Spreading would have *satisfied* the template — i.e., kalal fills
    every C-slot — but it violates \*Misalignment. The squib's central
    argument is that this latter violation is decisive. -/
theorem hebrew_kalal_filled :
    hebrewKlj_kalal.allCSlotsFilled = true := by decide

/-- The empty-slot [kala] candidate violates the C-slot-filling
    requirement. The grammar tolerates this *because* every alternative
    violates \*Misalignment. (See `qataT_qata_three_way_contrast` for
    the joint statement of the three-way fate.) -/
theorem hebrew_kala_unfilled :
    hebrewKlj_kala.allCSlotsFilled = false := by decide

/-- The passive participle [kaluj] is unproblematic on every dimension:
    final C-slot is not [+c]-specified, /j/ associates directly, no
    spreading required. -/
theorem hebrew_kaluj_satisfies :
    hebrewKlj_kaluj.satisfies = true := by decide

/-- The full three-way contrast of @cite{faust-2026} (3): three roots,
    one template, three different fates determined by \*Misalignment +
    [+c]-specification. The decisive feature is *which root index*
    sits at template-final:

    - √klt:    root-index 2 (= final). \*Misalignment satisfied. ✓ [kalat]
    - √kll:    root-index 2 (= final, identical to medial). ✓ [kalal]
    - √klj→l: root-index 1 (= nonfinal!). \*Misalignment fires. ✗
    - √klj→∅: no association at template-final. ✓ but C-slot empty: [kala]

    The QaTaT–QaTa "puzzle" dissolves: superficially-identical surface
    patterns ([kalal] from √kll vs hypothetical [kalal] from √klj) have
    *different root-template alignments*, and \*Misalignment discriminates
    by alignment, not by surface form. -/
theorem qataT_qata_three_way_contrast :
    hebrewKlt_kalat.satisfies = true ∧
    hebrewKll_kalal.satisfies = true ∧
    hebrewKlj_kalal.allCSlotsFilled = true ∧
    hebrewKlj_kalal.isMisaligned = true ∧
    hebrewKlj_kala.allCSlotsFilled = false ∧
    hebrewKlj_kala.isMisaligned = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Hebrew taQTiL intrusion (@cite{faust-2026} (10)) -/

/-- The illicit spreading derivation (@cite{faust-2026} (10a)) is
    misaligned: nonfinal /m/ landed at the template-final slot. -/
theorem hebrew_dmj_illicit_misaligned :
    hebrewDmj_illicit.isMisaligned = true := by decide

/-- The licit [tadmit] derivation (@cite{faust-2026} (10b–c)) — feminine
    /t/ intruder at the final [+c] slot — is not misaligned. -/
theorem hebrew_tadmit_not_misaligned :
    hebrewDmj_tadmit.isMisaligned = false := by decide

/-- And [tadmit] *does* satisfy the template (all C-slots filled).
    This is the squib's central analytical move: intrusion is a
    template-satisfaction strategy that escapes \*Misalignment by
    not being a root segment in the first place. -/
theorem hebrew_tadmit_satisfies :
    hebrewDmj_tadmit.satisfies = true := by decide

/-! ### Amharic [j]-final verbal vs nominal (@cite{faust-2026} (5), (8)) -/

/-- Amharic [fädʤ-ä] PFV is not misaligned (the final [+c] slot is
    truncated/unfilled, so no nonfinal root element is there). -/
theorem amharic_fdj_pfv_not_misaligned :
    amharicFdj_pfv.isMisaligned = false := by decide

/-- Amharic [fädʤto] gerund satisfies the template via [t]-intrusion. -/
theorem amharic_fdj_grnd_satisfies :
    amharicFdj_grnd.satisfies = true := by decide

/-! ### Faust's biradical reanalysis (@cite{faust-2026} page 432) -/

/-- √wd's biradical [wäddäd-ä] satisfies the template — every C-slot
    filled, no \*Misalignment violation (spreading /d/ to template-final
    is licit because /d/ is the *final* root segment). The OCP-violating
    √dd analysis @cite{broselow-1984} posited is therefore unnecessary. -/
theorem amharic_wd_satisfies :
    amharicWd_pfv.satisfies = true := by decide

-- ============================================================================
-- § 8: Cross-derivation theorems — the squib's main claims
-- ============================================================================

/-- @cite{faust-2026}'s central observation about Hebrew (4): for the
    same root √klj and template `CaCaC[+c]`, the spreading candidate
    violates \*Misalignment (despite satisfying the template) while
    the empty-slot candidate satisfies \*Misalignment (despite an
    unfilled C-slot). The grammar's preference for the empty slot
    is exactly what \*Misalignment >> FILL predicts — the squib's
    OT-implicit ranking. -/
theorem hebrew_klj_misalign_dominates_fill :
    -- *kalal: filled but misaligned
    hebrewKlj_kalal.allCSlotsFilled = true ∧
    hebrewKlj_kalal.isMisaligned = true ∧
    -- kala: unfilled but well-aligned
    hebrewKlj_kala.allCSlotsFilled = false ∧
    hebrewKlj_kala.isMisaligned = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- @cite{faust-2026}'s analytical move on Hebrew (10): templatic
    intrusion via the feminine /t/ is licit precisely because the
    intruder is not a root segment, so \*Misalignment doesn't apply
    to it — and *because* it's licit, the template can be satisfied
    without an unfilled C-slot. The intruder strategy is strictly
    superior to spreading on both dimensions. -/
theorem hebrew_intrusion_strictly_superior_to_spreading :
    -- spreading: filled but misaligned
    hebrewDmj_illicit.allCSlotsFilled = true ∧
    hebrewDmj_illicit.isMisaligned = true ∧
    -- intrusion: filled AND well-aligned
    hebrewDmj_tadmit.allCSlotsFilled = true ∧
    hebrewDmj_tadmit.isMisaligned = false ∧
    hebrewDmj_tadmit.satisfies = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- @cite{faust-2026}'s reanalysis (page 432): biradical vs
    triradical roots interact with \*Misalignment differently.
    Spreading the final radical of a *biradical* root to template-final
    is licit (final-of-final), while spreading the medial radical of
    a *triradical* root is not. This is the type-level demonstration
    that the surface contrast between [wäddäd-ä] (OK) and \*[kalal]
    (blocked) reduces to \*Misalignment alone — no OCP-violating
    biradicals like @cite{broselow-1984}'s √dd are needed. -/
theorem biradical_spread_ok_triradical_spread_blocked :
    amharicWd_pfv.isMisaligned = false ∧
    hebrewKlj_kalal.isMisaligned = true := by
  exact ⟨by decide, by decide⟩

/-- The squib's core analytical claim, in one statement: across both
    languages and all three phenomena, every form claimed to surface
    satisfies \*Misalignment, while every form claimed to be ruled
    out violates it. -/
theorem misalignment_predicts_all_cases :
    -- ruled out
    hebrewKlj_kalal.isMisaligned = true ∧
    hebrewDmj_illicit.isMisaligned = true ∧
    -- surfaces
    hebrewKlj_kala.isMisaligned = false ∧
    hebrewKlj_kaluj.isMisaligned = false ∧
    hebrewDmj_tadmit.isMisaligned = false ∧
    amharicFdj_pfv.isMisaligned = false ∧
    amharicFdj_grnd.isMisaligned = false ∧
    amharicWd_pfv.isMisaligned = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 9: Root-level OCP — Faust's reanalysis vindicates the OCP
-- ============================================================================

/-! ### Connecting to the OCP infrastructure (@cite{mccarthy-1981})

Faust's biradical reanalysis turns on a substantive empirical claim
about the OCP at the root level: once √fdj is recognized as
triradical (with /j/ as the third radical, not a default-[t]-inducing
biradical √fd), the only remaining "OCP violators" — apparent
biradicals like √wd — turn out to have *distinct* radicals after all
(/w/ ≠ /d/), with surface gemination produced by template spreading
rather than root identity.

The `Root.satisfiesOCP` predicate (in `Core.Morphology`) makes this
verifiable rather than asserted. -/

/-- @cite{faust-2026} page 432: √wd has no OCP violation at the root
    level — even though [wäddäd-ä] surfaces with adjacent identical
    [d][d], the surface gemination is a template-spreading effect. -/
theorem amharic_wd_satisfies_root_ocp :
    Root.satisfiesOCP Fragments.Amharic.wd = true := rfl

/-- @cite{faust-2026}'s reanalysis: √fdj (the triradical analysis) has
    no OCP violation. -/
theorem amharic_fdj_satisfies_root_ocp :
    Root.satisfiesOCP Fragments.Amharic.fdj = true := rfl

/-- And the Hebrew [j]-final root √klj also satisfies the OCP. -/
theorem hebrew_klj_satisfies_root_ocp :
    Root.satisfiesOCP Fragments.Hebrew.klj = true := rfl

/-- Sanity: a hypothetical OCP-violating biradical √dd (which
    @cite{broselow-1984} would have posited but @cite{faust-2026}
    rejects) really does violate the OCP under our predicate. -/
theorem hypothetical_dd_violates_root_ocp :
    Root.satisfiesOCP (⟨["d", "d"]⟩ : Root String) = false := rfl

-- ============================================================================
-- § 10: Strict CV hollow roots + NCC (@cite{faust-2026} (12)–(13))
-- ============================================================================

/-! @cite{faust-2026} (11)'s structural diagnosis — that [t]-intrusion
is the exponent of `n[+gen]` (cf. @cite{kramer-2020}) and unavailable
for verbs because gender lives on a higher Agr head — is formalized
cross-paper in §12 below (the verbal/nominal asymmetry). The structural
Kramer-2015/2020 background itself is verified in
`Phenomena/Gender/Studies/Kramer2020.lean`. -/

/-! ### The medial- vs. final-empty asymmetry

@cite{faust-2026} (13) presents an asymmetry inside the [t]-intrusion
paradigm itself. Three Amharic INF forms are derived from roots whose
"hollow" element (a non-consonantal radical merging with vocalization)
sits at *different* positions in the root:

- (13a) [mäsmat] from √sma — non-consonantal **final** /a/ leaves the
  template-final C-slot unfilled. Right-edge [t]-intrusion fills that
  slot; the intruder is at the right edge of the association lines, so
  no other root association sits to its right. **No NCC violation.**

- (13b) [mäsam] from √sam — non-consonantal **medial** /a/ leaves the
  *medial* C-slot unfilled, but the *final* C-slot is filled by the
  third radical /m/. Right-edge [t]-intrusion would have to land at
  the medial slot, with /m/ already associated to the final slot —
  and the intruder line would cross the /m/ line. **NCC blocks it.**

- (13c) [mähid] from √hid — same structural configuration as (13b),
  but with /i/ as the non-consonantal medial. Same NCC blocking.

The Strict-CV @cite{lowenstamm-1996} representation makes this
asymmetry visible: *which* C-slot is empty matters because the
No-Crossing Constraint @cite{goldsmith-1976} discriminates by position
relative to the rest of the association lines.

The infrastructure for this analysis lives in
`Theories/Phonology/Templates.lean`:
`RootTemplateMatch.unfilledCSlots`, `RootTemplateMatch.violatesNCC`, and
the `noCross` constraint. -/

/-- Amharic infinitive template (the five CV-skeletal slots after the
    [mä-] infinitive prefix). The final slot is [+c]-specified, which
    is what makes the [t]-intrusion question arise at all. -/
def amharicInf : Template :=
  ⟨[.C, .V, .C, .V, .Cspec]⟩

/-- (13a) [mäsmat] from √sma `hear`: the non-consonantal **final**
    radical /a/ leaves the template-final C-slot unfilled, and right-edge
    [t]-intrusion fills it without crossing any other root line. -/
def amharicSma_inf : RootTemplateMatch String :=
  { root := Fragments.Amharic.sma
    template := amharicInf
    associations :=
      [⟨.root, 0, 0⟩,        -- s → C0
       ⟨.root, 1, 2⟩,        -- m → C2
       ⟨.intruder, 0, 4⟩] }  -- /t/ → C[+c]4 (right edge: no crossing)

/-- (13b) [mäsam] from √sam `kiss`: the non-consonantal **medial**
    radical /a/ leaves the *medial* C-slot unfilled, while the third
    radical /m/ fills the final C-slot. The medial position remains
    empty in the surface form. -/
def amharicSam_inf : RootTemplateMatch String :=
  { root := Fragments.Amharic.sam
    template := amharicInf
    associations :=
      [⟨.root, 0, 0⟩,    -- s → C0
       ⟨.root, 2, 4⟩] }  -- m → C[+c]4  (medial /a/ skipped)

/-- Hypothetical [t]-intrusion candidate for √sam: tries to fill the
    medial C-slot from the right. The /m/ at C4 forces line-crossing.
    Demonstrates why intrusion is blocked in (13b). -/
def amharicSam_inf_intrusion : RootTemplateMatch String :=
  { root := Fragments.Amharic.sam
    template := amharicInf
    associations :=
      [⟨.root, 0, 0⟩,        -- s → C0
       ⟨.intruder, 0, 2⟩,    -- /t/ at medial (would cross /m/ at C4)
       ⟨.root, 2, 4⟩] }

/-- (13c) [mähid] from √hid `go`: structurally identical to (13b) —
    non-consonantal medial /i/ leaves the medial C-slot unfilled, /d/
    fills the final C-slot. Same NCC blocking of [t]-intrusion. -/
def amharicHid_inf : RootTemplateMatch String :=
  { root := Fragments.Amharic.hid
    template := amharicInf
    associations :=
      [⟨.root, 0, 0⟩,    -- h → C0
       ⟨.root, 2, 4⟩] }  -- d → C[+c]4 (medial /i/ skipped)

/-- Hypothetical [t]-intrusion candidate for √hid: same NCC violation
    as `amharicSam_inf_intrusion`. -/
def amharicHid_inf_intrusion : RootTemplateMatch String :=
  { root := Fragments.Amharic.hid
    template := amharicInf
    associations :=
      [⟨.root, 0, 0⟩,
       ⟨.intruder, 0, 2⟩,
       ⟨.root, 2, 4⟩] }

/-! #### Theorems — final-empty licenses intrusion, medial-empty blocks it -/

/-- (13a): √sma's [t]-intrusion derivation satisfies the template — every
    C-slot is filled (root + intruder), no \*Misalignment fires. -/
theorem amharic_sma_inf_satisfies :
    amharicSma_inf.satisfies = true := by decide

/-- (13a): the right-edge intruder in √sma's INF does NOT violate the
    No-Crossing Constraint — there is no root association sitting to its
    right to be crossed. -/
theorem amharic_sma_inf_no_ncc :
    amharicSma_inf.violatesNCC = false := by decide

/-- (13b)/(13c): without intrusion, the medial C-slot of √sam INF is
    unfilled. Indices into `amharicInf = [C, V, C, V, Cspec]`: only
    C2 is unfilled (C0 and C4 have associations, V1 and V3 aren't C-slots). -/
theorem amharic_sam_inf_medial_unfilled :
    amharicSam_inf.unfilledCSlots = [2] := by decide

/-- (13c): same medial-only unfilled-slot pattern for √hid INF. -/
theorem amharic_hid_inf_medial_unfilled :
    amharicHid_inf.unfilledCSlots = [2] := by decide

/-- (13b): the hypothetical [t]-intrusion derivation for √sam violates
    the No-Crossing Constraint — the intruder at C2 would cross the
    /m/ root association at C4. This is what blocks intrusion in (13b). -/
theorem amharic_sam_inf_intrusion_violates_ncc :
    amharicSam_inf_intrusion.violatesNCC = true := by decide

/-- (13c): same NCC violation blocks intrusion in √hid INF. -/
theorem amharic_hid_inf_intrusion_violates_ncc :
    amharicHid_inf_intrusion.violatesNCC = true := by decide

/-- The structural asymmetry behind @cite{faust-2026} (13) in one
    statement: among the three hollow-root INFs, the one where the
    non-consonantal radical is *final* (√sma, leaving the final C-slot
    empty) admits [t]-intrusion without violating NCC, while the two
    where the non-consonantal radical is *medial* (√sam, √hid, leaving
    the medial C-slot empty) do not — a hypothetical medial intruder
    would have to cross the final root association line. -/
theorem hollow_root_intrusion_asymmetry :
    -- Final-empty (13a): intrusion allowed
    amharicSma_inf.violatesNCC = false ∧
    amharicSma_inf.satisfies = true ∧
    -- Medial-empty (13b/c): hypothetical intrusion blocked
    amharicSam_inf_intrusion.violatesNCC = true ∧
    amharicHid_inf_intrusion.violatesNCC = true ∧
    -- Without intrusion, both medial-empty cases leave C2 unfilled
    amharicSam_inf.unfilledCSlots = [2] ∧
    amharicHid_inf.unfilledCSlots = [2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 11: Explicit OT tableau — \*Misalign >> FILL (@cite{faust-2026} (4))
-- ============================================================================

/-! ### The QaTaT–QaTa choice as an OT optimization, grounded in §3

The squib's analysis is implicitly an OT ranking argument: the grammar
chooses the candidate that satisfies \*Misalignment over the candidate
that satisfies FILL. Sections 7–8 state this ranking via the joint
`hebrew_klj_misalign_dominates_fill` predicate; here we make it
explicit by building tableaux **directly over the `RootTemplateMatch`
candidates defined in §3**, using the existing `starMisalign` and
`fill` constraints from `Theories/Phonology/Templates.lean`.

This is the "derive, don't stipulate" architecture: the OT verdicts
follow from the *same* `isMisaligned` and `allCSlotsFilled` predicates
that prove §3–§7, so any change to those predicates would propagate
into the tableau predictions automatically.

Two demonstrations:

1. **The empirical ranking** \*Misalign >> FILL selects [kala], the
   surface form. This is the prediction.
2. **The reversed ranking** FILL >> \*Misalign selects \*[kalal], the
   form that is empirically ruled out. This shows that the ranking is
   doing real work — without \*Misalignment dominating, the spreading
   candidate would win on template-satisfaction grounds. -/

open Core.OT (mkTableau mkFactorialOptima)

/-- The √klj candidate set: the spreading attempt and the empty-slot
    actual surface form. Built as the `RootTemplateMatch` values from
    §3 — no enum re-stipulation. -/
def kljCandidates : List (RootTemplateMatch String) :=
  [hebrewKlj_kalal, hebrewKlj_kala]

theorem kljCandidates_ne : kljCandidates ≠ [] := by decide

/-- **The empirical ranking** \*Misalign >> FILL selects [kala]: the
    surface form, with an unfilled template-final C-slot, wins because
    \*Misalignment outranks FILL. The verdict follows from the
    `isMisaligned`/`allCSlotsFilled` computations on the `RootTemplateMatch`
    values — no stipulated violation tables. -/
theorem kala_wins_under_misalign_over_fill :
    (mkTableau kljCandidates [starMisalign, fill] kljCandidates_ne).optimal
    = {hebrewKlj_kala} := by decide

/-- **Reversed ranking** FILL >> \*Misalign predicts the spreading
    candidate \*[kalal] — the form @cite{faust-2026} (4) explicitly
    argues against. The reversed-ranking demo shows that \*Misalignment
    dominance is doing the empirical work; without it, template
    satisfaction would force the wrong winner. -/
theorem kalal_predicted_under_reversed_ranking :
    (mkTableau kljCandidates [fill, starMisalign] kljCandidates_ne).optimal
    = {hebrewKlj_kalal} := by decide

/-- **Factorial typology over {\*Misalign, FILL}**: the two rankings
    yield two distinct optimal sets. This is the OT-typological
    statement of @cite{faust-2026}'s claim — the constraint set predicts
    exactly two languages, the attested Hebrew/Amharic pattern (kala-
    type, with empty C-slots tolerated) and a hypothetical mirror
    (kalal-type, where spreading wins). -/
theorem klj_factorial_typology_size_two :
    (mkFactorialOptima kljCandidates [starMisalign, fill]
      kljCandidates_ne).length = 2 := by decide

/-! ### The (3) three-way contrast as a tableau

For √klt and √kll, no \*Misalignment violation arises in any candidate,
so both surface forms (`hebrewKlt_kalat`, `hebrewKll_kalal`) are
unique winners under any ranking — the QaTaT–QaTa "puzzle" only bites
when the third radical is /j/. -/

/-- (3a) [kalat] from √klt is the unique optimum because every C-slot
    is filled and \*Misalignment is satisfied — both constraints have
    zero violations, so it wins under any ranking. -/
theorem kalat_unique_optimum :
    (mkTableau [hebrewKlt_kalat] [starMisalign, fill]
      (by decide)).optimal = {hebrewKlt_kalat} := by decide

/-- (3b) [kalal] from √kll likewise wins as the unique optimum: the
    legitimate final-of-final spreading satisfies \*Misalignment AND
    fills the template. Same logic as (3a), but the empirical interest
    is that the *surface form* is identical to the ungrammatical
    \*[kalal] derivation from √klj — only the underlying root index
    differs, and that's exactly what \*Misalignment is sensitive to. -/
theorem kalal_from_kll_unique_optimum :
    (mkTableau [hebrewKll_kalal] [starMisalign, fill]
      (by decide)).optimal = {hebrewKll_kalal} := by decide

/-! ### The Hebrew taQTiL intrusion case as a three-candidate tableau

The taQTiL[+c] template admits three derivations for √dmj: the
illicit spreading (10a, `hebrewDmj_illicit`), the licit intrusion
(10b–c, `hebrewDmj_tadmit`), and the empty-slot fallback. We need to
construct the empty-slot candidate explicitly to populate the tableau. -/

/-- Empty-slot candidate for √dmj + taQTiL[+c]: the prefix /t/ plus
    /d/ and /m/ at C2/C3, with the [+c] final C-slot unfilled.
    Hypothetical (not the empirical winner) — included to exhibit the
    full three-way comparison. -/
def hebrewDmj_empty : RootTemplateMatch String :=
  { root := Fragments.Hebrew.dmj
    template := hebrewTaQTiL
    associations :=
      [⟨.intruder, 0, 0⟩,   -- prefix /t/ (template-internal "ta")
       ⟨.root, 0, 2⟩,       -- d → C2
       ⟨.root, 1, 3⟩] }     -- m → C3 (no association at slot 5)

def taqtilCandidates : List (RootTemplateMatch String) :=
  [hebrewDmj_illicit, hebrewDmj_empty, hebrewDmj_tadmit]

theorem taqtilCandidates_ne : taqtilCandidates ≠ [] := by decide

/-- The intrusion candidate [tadmit] is *strictly better* than both
    alternatives: it has 0 violations on \*Misalign AND 0 violations
    on FILL. So under any ranking of these two constraints, [tadmit]
    wins. This is @cite{faust-2026}'s core analytical point about (10):
    intrusion lets the grammar "have it both ways". -/
theorem tadmit_wins_under_misalign_over_fill :
    (mkTableau taqtilCandidates [starMisalign, fill]
      taqtilCandidates_ne).optimal = {hebrewDmj_tadmit} := by decide

/-- And it wins under the reversed ranking too — because intrusion
    satisfies *both* constraints, the ranking between them is irrelevant
    once the intrusion candidate is in the candidate set. -/
theorem tadmit_wins_under_fill_over_misalign :
    (mkTableau taqtilCandidates [fill, starMisalign]
      taqtilCandidates_ne).optimal = {hebrewDmj_tadmit} := by decide

/-- The taQTiL factorial typology collapses to **one** language: when an
    intrusion strategy is in the candidate set, both rankings of
    {\*Misalign, FILL} pick the same winner. The OT-typological
    statement that intrusion is "ranking-invariant" — exactly the
    sense in which @cite{faust-2026} (10b–c) makes intrusion the
    grammar's optimal escape from the misalignment dilemma. -/
theorem taqtil_factorial_typology_size_one :
    (mkFactorialOptima taqtilCandidates [starMisalign, fill]
      taqtilCandidates_ne).length = 1 := by decide

-- ============================================================================
-- § 12: The verbal/nominal asymmetry, derived from Kramer 2020
-- ============================================================================

/-! ### Cross-paper bridge — `n[+gen]` licenses intrusion, Agr does not

@cite{faust-2026} (11) attributes the *nominal-only* distribution of
[t]-intrusion to a structural fact: the intruding /t/ is the exponent
of the n[+gen] head in @cite{kramer-2020}'s sense — gender is realized
*inherently* on n, exposed as a sister bound root in
@cite{lowenstamm-2014}'s sense. In verbal forms the corresponding
gender feature lives on a higher Agr head as contextual agreement,
not as an inherent root-like exponent on v itself; consequently no
intruder is morphosyntactically available to fill the templatic slot.

Sections 1–11 verify the prosodic side of the analysis (intrusion
satisfies the template without violating \*Misalignment). This
section verifies the *morphological* side by formalizing the Faust
claim as a predicate on Kramer's `CatHead`:

> Intrusion is licensed iff the categorizer is `n` and carries a
> gender feature.

Once that predicate is in place, the verbal/nominal asymmetry is no
longer a docstring stipulation — it falls out by `rfl` from
`RootTemplateMatch.intrusionLicensed` applied to the per-template
`CatHead` tags, and breaks if either Faust's morphological claim or
Kramer's `CatHead` taxonomy changes. -/

open Morphology.DM (CatHead)

/-! The morphological-licensing predicate `CatHead.licensesIntrusion`
itself lives in `Theories/Morphology/DM/Categorizer.lean` (alongside
the Kramer taxonomy it ranges over), together with its per-canonical-
head verification theorems (`n_uFem_licenses_intrusion`,
`v_plain_blocks_intrusion`, etc.) and the iff characterization
`Morphology.DM.licensesIntrusion_iff_n_and_gen`. The Faust-specific
content of §12 is the *per-template `CatHead` tagging* and the
per-derivation verdicts below. -/

/-! #### Per-template `CatHead` tags

Faust's analysis assigns each templatic morphology slot to a specific
categorizer head. These are the morphosyntactic claims; the
intrusion-licensing predictions follow mechanically. -/

/-- Hebrew PST.3MSG `CaCaC[+c]` is realized at v (verbal categorizer);
    gender lives on the Agr head outside the template, so v itself
    has no gender-bearing exponent to intrude. -/
def hebrewPst3msg_locus : CatHead := CatHead.v_plain

/-- Hebrew passive participle `CaCuC` is also v-realized. -/
def hebrewPassPrtcpl_locus : CatHead := CatHead.v_plain

/-- Hebrew taQTiL[+c] is a feminine deverbal noun realized at n[+gen]
    (the u[+FEM] head in Kramer's Set 1 taxonomy — the source of the
    intruding /t/). -/
def hebrewTaQTiL_locus : CatHead := CatHead.n_uFem

/-- Amharic PFV.3MSG `CäC.CäC[+c]` is v-realized. -/
def amharicPfv3msg_locus : CatHead := CatHead.v_plain

/-- Amharic gerund `CäC.C[+c]-o` is a deverbal nominal at n[+gen]. -/
def amharicGrnd_locus : CatHead := CatHead.n_uFem

/-- Amharic infinitive `mä-CVCVC[+c]` is also a deverbal nominal at
    n[+gen] — confirmed by the (13a) [t]-intrusion in [mäsmat].
    @cite{faust-2026}'s analysis treats Amharic infinitives as
    nominalizations whose template is hosted on n. -/
def amharicInf_locus : CatHead := CatHead.n_uFem

/-! #### Universal licensing structure (Faust + Kramer)

The Faust-`CatHead` interaction is governed by a single structural
fact, derivable by composing `intrusionLicensed_iff`
(Templates.lean) with `licensesIntrusion_iff_n_and_gen`
(Categorizer.lean). The per-derivation `decide` theorems below and the
end-of-section `verbal_nominal_asymmetry_from_kramer` bundle are all
instances of this universal claim. -/

/-- **The Faust+Kramer integration theorem.** A `RootTemplateMatch`
    passes intrusion-licensing under a `CatHead` iff either the match
    is intruder-free OR the head is a gender-bearing nominal (n[+gen],
    in @cite{kramer-2020}'s sense).

    This is the universal-quantification of @cite{faust-2026} (11):
    every per-derivation verdict in §12 reduces to checking which
    disjunct holds for the specific (match, head) pair. -/
theorem intrusion_wellformed_iff_no_intruder_or_n_with_gen
    (m : RootTemplateMatch String) (ch : CatHead) :
    m.intrusionLicensed ch.licensesIntrusion = true ↔
      m.hasIntruder = false ∨ (ch.cat = .n ∧ ch.phi.gender.isSome = true) := by
  rw [intrusionLicensed_iff]
  constructor
  · rintro (hlic | hno)
    · exact Or.inr ((Morphology.DM.licensesIntrusion_iff_n_and_gen ch).mp hlic)
    · exact Or.inl hno
  · rintro (hno | hgen)
    · exact Or.inr hno
    · exact Or.inl ((Morphology.DM.licensesIntrusion_iff_n_and_gen ch).mpr hgen)

/-- **Corollary (verbal half).** Under a verbal locus (`v_plain`, with
    no gender feature), licensing reduces to intruder-freeness. This is
    why every verbal Faust derivation in §3–§6 must be intruder-free
    to be morphologically licensed — the spreading and empty-slot
    strategies are the only options open to v. -/
theorem v_plain_licenses_iff_no_intruder (m : RootTemplateMatch String) :
    m.intrusionLicensed CatHead.v_plain.licensesIntrusion = true ↔
      m.hasIntruder = false := by
  rw [intrusion_wellformed_iff_no_intruder_or_n_with_gen]
  constructor
  · rintro (h | ⟨hcat, _⟩)
    · exact h
    · exact absurd hcat (by decide)
  · exact Or.inl

/-- **Corollary (nominal half).** Under an `n_uFem` locus (gender-
    bearing nominal), every match is licensed regardless of intruder
    status. This is why intrusion is *available* to nominal templates
    like Hebrew taQTiL and Amharic gerunds/INFs — the Kramer-2020
    structure makes the n[+gen] exponent morphosyntactically present. -/
theorem n_uFem_licenses_universally (m : RootTemplateMatch String) :
    m.intrusionLicensed CatHead.n_uFem.licensesIntrusion = true := by
  rw [intrusion_wellformed_iff_no_intruder_or_n_with_gen]
  exact Or.inr ⟨rfl, rfl⟩

/-! #### Per-derivation licensing theorems

For every match, the predicate `RootTemplateMatch.intrusionLicensed`
applied to the corresponding template's `CatHead.licensesIntrusion`
gives the well-formedness verdict. The proofs are `decide` — the
disjunction reduces by `rfl` once the predicates evaluate. -/

/-! ##### Hebrew verbal forms (no intrusion possible) -/

theorem kalat_licensed_at_v :
    hebrewKlt_kalat.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = true := by decide

theorem kalal_kll_licensed_at_v :
    hebrewKll_kalal.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = true := by decide

theorem kala_licensed_at_v :
    hebrewKlj_kala.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = true := by decide

theorem kalal_klj_licensed_at_v :
    hebrewKlj_kalal.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = true := by decide

theorem kaluj_licensed_at_v :
    hebrewKlj_kaluj.intrusionLicensed
      hebrewPassPrtcpl_locus.licensesIntrusion = true := by decide

/-! ##### Hebrew nominal taQTiL (intrusion possible) -/

/-- The illicit-spreading derivation also passes intrusion-licensing
    (its prefix /t/ is an intruder, but n[+gen] licenses it). The
    derivation is ruled out by \*Misalignment, not by the
    morphological licensing — a useful separation. -/
theorem dmj_illicit_licensed_at_n :
    hebrewDmj_illicit.intrusionLicensed
      hebrewTaQTiL_locus.licensesIntrusion = true := by decide

theorem tadmit_licensed_at_n :
    hebrewDmj_tadmit.intrusionLicensed
      hebrewTaQTiL_locus.licensesIntrusion = true := by decide

/-! ##### Amharic verbal vs nominal -/

theorem fdj_pfv_licensed_at_v :
    amharicFdj_pfv.intrusionLicensed
      amharicPfv3msg_locus.licensesIntrusion = true := by decide

theorem wd_pfv_licensed_at_v :
    amharicWd_pfv.intrusionLicensed
      amharicPfv3msg_locus.licensesIntrusion = true := by decide

theorem fdj_grnd_licensed_at_n :
    amharicFdj_grnd.intrusionLicensed
      amharicGrnd_locus.licensesIntrusion = true := by decide

theorem sma_inf_licensed_at_n :
    amharicSma_inf.intrusionLicensed
      amharicInf_locus.licensesIntrusion = true := by decide

/-! #### The verbal-intrusion blocking theorem

The empirical content of @cite{faust-2026} (11) is *negative*: a
verbal template cannot host an [t]-intruder, even when a phonological
analog of intrusion would technically resolve a misalignment problem.
Construct a hypothetical verbal candidate that *tries* to use
intrusion — analogous to the licit nominal [tadmit] — and prove it
fails morphological licensing. -/

/-- Hypothetical: √dmj realized in the *verbal* PST.3MSG template
    `CaCaC[+c]` with a feminine /t/ intruder occupying the [+c]
    final slot. Phonologically identical to a nominal intrusion
    candidate, but Agr-locus precludes the n[+gen] exponent
    morphosyntactically. -/
def hebrewDmj_pst3msg_intrusion : RootTemplateMatch String :=
  { root := Fragments.Hebrew.dmj
    template := hebrewPst3msg
    associations :=
      [⟨.root, 0, 0⟩,        -- d → C0
       ⟨.root, 1, 2⟩,        -- m → C2
       ⟨.intruder, 0, 4⟩] }  -- /t/ intruder → C[+c]4 — but unlicensed!

/-- The hypothetical verbal-intrusion candidate has all C-slots
    filled and is not misaligned: it satisfies the *prosodic*
    well-formedness conditions @cite{faust-2026} states. -/
theorem hebrew_pst3msg_intrusion_prosodically_satisfies :
    hebrewDmj_pst3msg_intrusion.satisfies = true := by decide

/-- But under @cite{faust-2026}'s morphological-licensing predicate,
    it fails: v-locus does not license n[+gen]'s /t/ exponent. -/
theorem hebrew_pst3msg_intrusion_morphologically_blocked :
    hebrewDmj_pst3msg_intrusion.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = false := by decide

/-! #### The cross-paper integration theorem -/

/-- The verbal/nominal asymmetry of @cite{faust-2026} (11), derived
    from @cite{kramer-2020}'s `CatHead` taxonomy:

    1. **Intrusion is licensed at n[+gen] (here `n_uFem`).** Both
       Hebrew taQTiL [tadmit] and the hypothetical verbal-template
       intrusion `hebrewDmj_pst3msg_intrusion` would pass
       intrusion-licensing if the locus were n[+gen]. The first
       derivation IS at n[+gen]; the second is not.

    2. **Intrusion is blocked at v.** The hypothetical verbal
       intrusion candidate, despite satisfying the template, fails
       intrusion-licensing because v doesn't expose a gender exponent.

    3. **Intruder-free verbal derivations always pass licensing.**
       Every verbal candidate in §3–§6 (kala, kalal, kalat, kaluj,
       fdj_pfv, wd_pfv) is intruder-free, so it passes vacuously.

    The asymmetry is therefore *derived* — not stipulated — from the
    composition of two independent claims: Faust's licensing
    predicate (only n with [+gen]) and Kramer's `CatHead` structure
    (n vs. v). -/
theorem verbal_nominal_asymmetry_from_kramer :
    -- Nominal locus licenses intrusion candidates
    hebrewDmj_tadmit.intrusionLicensed
      hebrewTaQTiL_locus.licensesIntrusion = true ∧
    amharicFdj_grnd.intrusionLicensed
      amharicGrnd_locus.licensesIntrusion = true ∧
    -- Verbal locus blocks intrusion candidates
    hebrewDmj_pst3msg_intrusion.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = false ∧
    -- The verbal candidate's prosodic satisfaction is irrelevant —
    -- it satisfies the template but fails the morphological licensing
    hebrewDmj_pst3msg_intrusion.satisfies = true ∧
    -- Intruder-free verbal forms always pass
    hebrewKlj_kala.intrusionLicensed
      hebrewPst3msg_locus.licensesIntrusion = true ∧
    amharicFdj_pfv.intrusionLicensed
      amharicPfv3msg_locus.licensesIntrusion = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Phenomena.TemplaticMorphology.Studies.Faust2026
