import Linglib.Core.Morphology.DegreeContainment
import Linglib.Core.Case.Allomorphy
import Linglib.Theories.Morphology.DegreeContainment

/-!
# Smith, Moskal, Xu, Kang & Bobaljik (2019) — Case and Number Suppletion in Pronouns
@cite{smith-moskal-xu-kang-bobaljik-2019}

@cite{smith-moskal-xu-kang-bobaljik-2019} extend `@cite{bobaljik-2012}`'s
structural-containment account of *ABA in adjectival degree suppletion
(`good–better–best` / `*good–better–goodest`) to two further empirical
domains: pronominal case suppletion (using `@cite{caha-2009}`'s case
hierarchy as the structural backbone) and pronominal number suppletion
(using `@cite{harbour-2008}` / `@cite{noyer-1992}` for the number-feature
geometry).

The cross-domain extension is not seamless: the paper identifies three
points where the empirical generalizations require theoretical
refinement of the Bobaljik 2012 framework:

1. **§3.6 — AAB attestation diverges across domains.** AAB patterns
   (e.g., a paradigm where positive and comparative share a root and
   the superlative is suppletive) are systematically *unattested* in
   adjectival degree but *are attested* in pronominal case and
   pronominal number. This is the divergence formalized below.

2. **§3.7 — domain-based locality replaces structural/linear
   adjacency.** The locality predicate from @cite{bobaljik-2012} (and
   @cite{embick-2010}) is too restrictive once AAB is admitted. The
   paper proposes the weaker domain-based locality from
   @cite{moskal-2015}.

3. **§4.3.1 — markedness × suppletion.** Cross-linguistic variation
   in pronominal number suppletion correlates with independent
   evidence for variation in the internal complexity / markedness of
   the number head — connecting suppletion theory to the feature
   recursion of @cite{harbour-2014} (already substrate in this
   codebase, see `Theories/Syntax/Minimalist/Agreement/FeatureRecursion.lean`).

This file formalizes (1) directly: the DM-derivation in
`Theories/Morphology/DegreeContainment.lean` predicts AAB exclusion in
*every* domain it applies to (because `vi_cmpr_eq_sprl` forces the two
inner cells to share a root); the empirical data the paper reports
falsifies that prediction in case and number. (2) and (3) are stubbed
as substrate-addition TODOs.

## Scope of the formalization

- Degree-side prediction: proven directly from substrate (`§ 1`).
- Case AAB attestation: stubbed with `sorry` and a TODO citing the
  paper's specific empirical witnesses (`§ 2`); requires reading
  §3.6's data tables to encode a representative pattern.
- Number AAB attestation: stubbed (`§ 3`); same TODO shape.
- Domain-based locality predicate: stubbed substrate addition (`§ 4`);
  this is the substrate refactor (3.7) the paper motivates and that
  would naturally land as a sibling of `Core/Morphology/Containment.lean`.
-/

namespace Phenomena.Allomorphy.Studies.SmithMoskalEtAl2019

open Core.Morphology.DegreeContainment
open Core.Case.Allomorphy
open Theories.Morphology.DegreeContainment

-- ============================================================================
-- § 1: Degree side — DM derivation excludes AAB unconditionally
-- ============================================================================

/-! The DM-flavored derivation of *ABA in `Theories/Morphology/DegreeContainment.lean`
forces CMPR-cell = SPRL-cell for any VI-generated root pattern (the
core theorem `vi_cmpr_eq_sprl`). This is strictly stronger than
contiguity: it excludes both *ABA *and* *AAB.

The two theorems below state the same content at two granularities:
the general "no VI-generable pattern has CMPR ≠ SPRL", and the
specific corollary "the AAB pattern is not VI-generable." Both are
direct consequences of `vi_cmpr_eq_sprl` from the migration's Phase 4
substrate. -/

/-- DM Vocabulary Insertion under root-out locality cannot generate
    any pattern whose CMPR cell differs from its SPRL cell. -/
theorem dm_excludes_cmpr_sprl_distinct
    (rules : List LocalVIRule) (defaultForm : Nat)
    (h : (viPattern rules defaultForm).cmpr ≠ (viPattern rules defaultForm).sprl) :
    False :=
  h (vi_cmpr_eq_sprl rules defaultForm)

/-- Specific corollary: the AAB pattern (POS = CMPR ≠ SPRL) cannot
    be VI-generated under DM root-out locality.

    `aab : DegreePattern := ⟨0, 0, 1⟩` lives in
    `Core/Morphology/DegreeContainment.lean`. -/
theorem dm_excludes_aab
    (rules : List LocalVIRule) (defaultForm : Nat) :
    viPattern rules defaultForm ≠ aab := by
  intro h
  apply dm_excludes_cmpr_sprl_distinct rules defaultForm
  rw [h]
  decide

-- ============================================================================
-- § 2: Case side — §3.6 attested AAB witnesses
-- ============================================================================

/-! @cite{smith-moskal-xu-kang-bobaljik-2019} §3.6 distinguishes two
kinds of AAB pattern in pronominal case suppletion:

- **Syncretic AAB** (Table 20: Aghul, Tsez, Hinuq, Archi 2SG): the
  ABS and ERG forms are identical (case syncretism), so the pattern
  is really `{A=A}B` — a 2-way contrast modeled by impoverishment
  rather than genuine 3-cell suppletion. The paper rejects these as
  evidence of true AAB.

- **Genuine AAB** (Tables 24, 25): ABS and ERG share a root *but
  remain morphologically distinct* (different suffix or stem-internal
  variation), and DAT is suppletive. These are real AAB witnesses.

We encode two genuine AAB witnesses:
- Wardaman 3SG (Table 25, @cite{merlan-1994}): ABS=*narnaj*,
  ERG=*narnaj-(j)i*, DAT=*gunga*. ABS and ERG share root *narnaj*
  with ERG bearing an additional ergative suffix; DAT is suppletive.
- Khinalugh 2SG (Table 24, Nakh-Daghestanian): ABS=*vi*, ERG=*va*,
  DAT=*oX(ir)*. ABS and ERG share a v-initial root with vowel
  alternation; DAT is suppletive.

Projecting onto the 3-cell ABS/ERG/DAT hierarchy, both patterns have
the shape `[0, 0, 1]` (positive and middle cells share root-class 0,
suppletive third cell takes root-class 1). -/

/-- Wardaman 3SG: ABS=*narnaj*, ERG=*narnaj-(j)i*, DAT=*gunga*.
    @cite{smith-moskal-xu-kang-bobaljik-2019} Table 25 (data from
    @cite{merlan-1994}). -/
def wardamanThirdSg : List Nat := [0, 0, 1]

/-- Khinalugh 2SG: ABS=*vi*, ERG=*va*, DAT=*oX(ir)*.
    @cite{smith-moskal-xu-kang-bobaljik-2019} Table 24. -/
def khinalughSecondSg : List Nat := [0, 0, 1]

/-- Both genuine-AAB witnesses are contiguous in the substrate sense
    (no *ABA violation): cells at positions 0 and 2 do not share a
    root they don't also share with position 1. -/
theorem wardaman_3sg_contiguous :
    Morphology.Containment.IsContiguous wardamanThirdSg := by decide

theorem khinalugh_2sg_contiguous :
    Morphology.Containment.IsContiguous khinalughSecondSg := by decide

/-- The defining AAB shape: cells 1 and 2 differ (suppletion in the
    third position but not the second). This is the structural feature
    that the DM derivation in `Theories/Morphology/DegreeContainment`
    excludes — `vi_cmpr_eq_sprl` forces the second and third cells to
    coincide for any VI-generated root pattern. -/
theorem wardaman_3sg_is_aab :
    wardamanThirdSg[1]? ≠ wardamanThirdSg[2]? := by decide

theorem khinalugh_2sg_is_aab :
    khinalughSecondSg[1]? ≠ khinalughSecondSg[2]? := by decide

/-- **§3.6 cross-domain divergence theorem.** The DM derivation in
    `Theories/Morphology/DegreeContainment.vi_cmpr_eq_sprl` predicts,
    for any VI-generable root pattern, that the second and third
    cells coincide. Lifted to case (where the 3-cell projection is
    UNMARKED–DEPENDENT–OBLIQUE, e.g. ABS–ERG–DAT in ergative
    languages), this prediction would exclude AAB cells `[A, A, B]`
    where the second cell equals the first but the third cell
    differs.

    @cite{smith-moskal-xu-kang-bobaljik-2019} §3.6 establishes that
    AAB is robustly attested in pronominal case suppletion (Table 9:
    10 instances, including Wardaman 3SG and the Nakh-Daghestanian
    2SG patterns). The existence of a contiguous AAB-shaped case
    pattern witnesses the falsification of the lifted DM derivation:
    no `vi_cmpr_eq_sprl`-style theorem can hold for case morphology.

    The paper's positive proposal (§3.7) is to weaken the locality
    predicate from structural adjacency (Bobaljik 2012) /
    linear adjacency (Embick 2010) to domain-based locality
    (@cite{moskal-2015}); see § 4 below. -/
theorem case_aab_attested_falsifies_dm :
    ∃ (cells : List Nat),
      Morphology.Containment.IsContiguous cells ∧
      cells[1]? ≠ cells[2]? :=
  ⟨wardamanThirdSg, wardaman_3sg_contiguous, wardaman_3sg_is_aab⟩

-- ============================================================================
-- § 3: Number side — §4 attested AAB witnesses (Table 46)
-- ============================================================================

/-! @cite{smith-moskal-xu-kang-bobaljik-2019} §4 surveys pronominal
number suppletion and finds the same AAB-attestation profile that
§3.6 reports for case: "we find extremely clear-cut examples of ABB,
ABC and AAB patterns, alongside AAA. We do not find any unambiguously
robust evidence of ABA patterns." Table 32 quantifies: 3 attested AAB
number paradigms (vs 48 ABB, 19 ABC, numerous AAA, 1 dubious ABA from
Yagua).

§4 Table 46 lists the three concrete AAB number witnesses:

- **Wambaya 1INCL** (@cite{nordlinger-1998}):
  SG=*ngawu(miji)*, PL=*ngurruwani*, DL=*mrindiyani*
- **Yagua 2** (@cite{payne-payne-1990}):
  SG=*jiy*, PL=*jiry-éy*, DL=*sáada*
- **Dehu 3M** (Smith 2011):
  SG=*angeice*, PL=*angate*, DL=*nyido*

We encode Yagua 2 — the cleanest morphological case: PL *jiryéy*
transparently contains the SG root *jiy* plus a plural suffix *-éy*,
while DL *sáada* is suppletive (no shared formative). This projects
to `[0, 0, 1]` over the SG/PL/DL hierarchy: positions 0 (SG) and 1
(PL) share root-class 0 (the *jiy* root); position 2 (DL) takes
root-class 1 (the *sáada* root).

The number paradigms are 3-cell over SG/PL/DL; the cell-ordering
reflects the containment structure SG–PL–DL or SG–DL–PL depending on
the language (the paper notes both orderings are attested, motivating
the §4.3.1 reanalysis of number representation that connects to
Harbour's @cite{harbour-2014} feature recursion). For Yagua, the
SG–PL–DL ordering matches the table caption directly. -/

/-- Yagua 2nd person number paradigm: SG=*jiy*, PL=*jiry-éy*,
    DL=*sáada*. @cite{smith-moskal-xu-kang-bobaljik-2019} Table 46
    (data from @cite{payne-payne-1990}). The PL is transparently
    *jiy* + *-éy*; the DL is suppletive. Projects to `[0, 0, 1]`
    over SG/PL/DL. -/
def yaguaSecond : List Nat := [0, 0, 1]

theorem yagua_2_contiguous :
    Morphology.Containment.IsContiguous yaguaSecond := by decide

theorem yagua_2_is_aab :
    yaguaSecond[1]? ≠ yaguaSecond[2]? := by decide

/-- §4 number-side analog of `case_aab_attested_falsifies_dm`. Same
    structural divergence: AAB is attested in pronominal number
    suppletion (3 instances per Table 32, with Wambaya / Yagua / Dehu
    listed in Table 46), falsifying the DM derivation lifted to number.
    The Yagua 2 witness is morphologically transparent — PL = SG +
    suffix; DL is suppletive — exactly the AAB shape that
    `vi_cmpr_eq_sprl` would predict cannot arise. -/
theorem number_aab_attested_falsifies_dm :
    ∃ (cells : List Nat),
      Morphology.Containment.IsContiguous cells ∧
      cells[1]? ≠ cells[2]? :=
  ⟨yaguaSecond, yagua_2_contiguous, yagua_2_is_aab⟩

-- ============================================================================
-- § 4: §3.7 — Domain-based locality (substrate addition)
-- ============================================================================

/-! @cite{smith-moskal-xu-kang-bobaljik-2019} §3.7 proposes that the
locality predicate driving suppletion contiguity is *not* structural
adjacency (@cite{bobaljik-2012}) or linear adjacency (@cite{embick-2010}),
but *domain-based* (@cite{moskal-2015}). Under domain locality, the
relevant locality unit is a phase / spellout domain, not a head-to-head
structural distance.

Architecturally this would land as a substrate addition in
`Core/Morphology/` parallel to `Containment.lean`'s `violatesABA` —
something like a domain-relativized `violatesABA_within_domain` whose
projection back to the universal `violatesABA` recovers Bobaljik's
stronger predicate, but which permits AAB across domain boundaries.
The DM derivation in `Theories/Morphology/DegreeContainment.lean`
would then be a domain-locality instantiation that happens to coincide
with the universal predicate when the degree paradigm fits in one
domain.

TODO: design the domain-relativized substrate, hoist into
`Core/Morphology/DomainLocality.lean`, prove the equivalence to
`Containment.violatesABA` under the single-domain assumption, then
apply to case + number suppletion to derive the AAB-attestation gap
non-vacuously.
-/

end Phenomena.Allomorphy.Studies.SmithMoskalEtAl2019
