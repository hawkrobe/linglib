import Linglib.Morphology.DegreeContainment
import Linglib.Morphology.Case.Allomorphy
import Linglib.Syntax.Case.Order
import Linglib.Morphology.DM.ContainmentVI

/-!
# Smith, Moskal, Xu, Kang & Bobaljik (2019) — Case and Number Suppletion in Pronouns
[smith-moskal-xu-kang-bobaljik-2019]

[smith-moskal-xu-kang-bobaljik-2019] extend `[bobaljik-2012]`'s
structural-containment account of *ABA in adjectival degree suppletion
(`good–better–best` / `*good–better–goodest`) to two further empirical
domains: pronominal case suppletion (using `[caha-2009]`'s case
hierarchy as the structural backbone) and pronominal number suppletion
(using `[harbour-2008]` / `[noyer-1992]` for the number-feature
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
   adjacency.** The locality predicate from [bobaljik-2012] (and
   [embick-2010]) is too restrictive once AAB is admitted. The
   paper proposes the weaker domain-based locality from
   [moskal-2015].

3. **§4.3.1 — markedness × suppletion.** Cross-linguistic variation
   in pronominal number suppletion correlates with independent
   evidence for variation in the internal complexity / markedness of
   the number head — connecting suppletion theory to the feature
   recursion of [harbour-2014] (already substrate in this
   codebase, see `Syntax/Minimalist/Phi/Recursion.lean`).

This file formalizes (1) directly: the DM-derivation in
`Morphology/DM/ContainmentVI.lean` predicts AAB exclusion in
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
  would naturally land as a sibling of `Morphology/Containment.lean`.
-/

namespace SmithMoskalEtAl2019

open Morphology.DegreeContainment
open Morphology.Case.Allomorphy
open Morphology.DM.ContainmentVI.Degree

-- ============================================================================
-- § 1: Degree side — DM derivation excludes AAB unconditionally
-- ============================================================================

/-! The DM-flavored derivation of *ABA in `Morphology/DM/ContainmentVI.lean`
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
    `Morphology/DegreeContainment.lean`. -/
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

/-! [smith-moskal-xu-kang-bobaljik-2019] §3.6 distinguishes two
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
- Wardaman 3SG (Table 25, [merlan-1994]): ABS=*narnaj*,
  ERG=*narnaj-(j)i*, DAT=*gunga*. ABS and ERG share root *narnaj*
  with ERG bearing an additional ergative suffix; DAT is suppletive.
- Khinalugh 2SG (Table 24, Nakh-Daghestanian): ABS=*vi*, ERG=*va*,
  DAT=*oX(ir)*. ABS and ERG share a v-initial root with vowel
  alternation; DAT is suppletive.

Projecting onto the 3-cell ABS/ERG/DAT hierarchy, both patterns have
the shape `[0, 0, 1]` (positive and middle cells share root-class 0,
suppletive third cell takes root-class 1). -/

/-- Wardaman 3SG: ABS=*narnaj*, ERG=*narnaj-(j)i*, DAT=*gunga*.
    [smith-moskal-xu-kang-bobaljik-2019] Table 25 (data from
    [merlan-1994]). -/
def wardamanThirdSg : List Nat := [0, 0, 1]

/-- Khinalugh 2SG: ABS=*vi*, ERG=*va*, DAT=*oX(ir)*.
    [smith-moskal-xu-kang-bobaljik-2019] Table 24. -/
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
    that the DM derivation in `Morphology/DM/ContainmentVI`
    excludes — `vi_cmpr_eq_sprl` forces the second and third cells to
    coincide for any VI-generated root pattern. -/
theorem wardaman_3sg_is_aab :
    wardamanThirdSg[1]? ≠ wardamanThirdSg[2]? := by decide

theorem khinalugh_2sg_is_aab :
    khinalughSecondSg[1]? ≠ khinalughSecondSg[2]? := by decide

/-- **§3.6 cross-domain divergence theorem.** The DM derivation in
    `Degree.vi_cmpr_eq_sprl` (PART II of `Morphology/DM/ContainmentVI.lean`) predicts,
    for any VI-generable root pattern, that the second and third
    cells coincide. Lifted to case (where the 3-cell projection is
    UNMARKED–DEPENDENT–OBLIQUE, e.g. ABS–ERG–DAT in ergative
    languages), this prediction would exclude AAB cells `[A, A, B]`
    where the second cell equals the first but the third cell
    differs.

    [smith-moskal-xu-kang-bobaljik-2019] §3.6 establishes that
    AAB is robustly attested in pronominal case suppletion (Table 9:
    10 instances, including Wardaman 3SG and the Nakh-Daghestanian
    2SG patterns). The existence of a contiguous AAB-shaped case
    pattern witnesses the falsification of the lifted DM derivation:
    no `vi_cmpr_eq_sprl`-style theorem can hold for case morphology.

    The paper's positive proposal (§3.7) is to weaken the locality
    predicate from structural adjacency (Bobaljik 2012) /
    linear adjacency (Embick 2010) to domain-based locality
    ([moskal-2015]); see § 4 below. -/
theorem case_aab_attested_falsifies_dm :
    ∃ (cells : List Nat),
      Morphology.Containment.IsContiguous cells ∧
      cells[1]? ≠ cells[2]? :=
  ⟨wardamanThirdSg, wardaman_3sg_contiguous, wardaman_3sg_is_aab⟩

-- ============================================================================
-- § 3: Number side — §4 attested AAB witnesses (Table 46)
-- ============================================================================

/-! [smith-moskal-xu-kang-bobaljik-2019] §4 surveys pronominal
number suppletion and finds the same AAB-attestation profile that
§3.6 reports for case: "we find extremely clear-cut examples of ABB,
ABC and AAB patterns, alongside AAA. We do not find any unambiguously
robust evidence of ABA patterns." Table 32 quantifies: 3 attested AAB
number paradigms (vs 48 ABB, 19 ABC, numerous AAA, 1 dubious ABA from
Yagua).

§4 Table 46 lists the three concrete AAB number witnesses:

- **Wambaya 1INCL** ([nordlinger-1998]):
  SG=*ngawu(miji)*, PL=*ngurruwani*, DL=*mrindiyani*
- **Yagua 2** ([payne-payne-1990]):
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
Harbour's [harbour-2014] feature recursion). For Yagua, the
SG–PL–DL ordering matches the table caption directly. -/

/-- Yagua 2nd person number paradigm: SG=*jiy*, PL=*jiry-éy*,
    DL=*sáada*. [smith-moskal-xu-kang-bobaljik-2019] Table 46
    (data from [payne-payne-1990]). The PL is transparently
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
-- § 4: §3.7 — Domain-based locality (case + number partitions)
-- ============================================================================

/-! [smith-moskal-xu-kang-bobaljik-2019] §3.7 proposes that the
locality predicate driving suppletion contiguity is *not* structural
adjacency ([bobaljik-2012]) or linear adjacency
([embick-2010]), but *domain-based*
([moskal-2015a-dissertation]). The substrate for this lives in
`Morphology/DM/DomainLocality.lean` (`DomainPartition`,
`SameDomain`, `ViolatesABAWithin`, `IsContiguousWithin`,
`DomainPartition.trivial`).

This section instantiates the substrate for the case and number
domains the paper discusses. The partitions are anchored on
independently-motivated linguistic content (per `mathlib-reviewer`
audit recommendation: "must derive from an independently-motivated
case-hierarchy split, not threshold-on-cell-index"):

- **Case partition (`caseDomainPartition`)**: positions 0 (ABS) and 1
  (ERG) in the **non-oblique** domain; position 2 (DAT) in the
  **oblique** domain. The boundary is the [caha-2009]
  Unmarked-Dependent vs Oblique split (the same containment
  hierarchy the paper itself adopts at §3.1; [smith-moskal-xu-kang-bobaljik-2019]
  §3.7 does not pin down the boundary location explicitly but the
  Caha hierarchy is the natural one given the paper's case-side
  framework).

- **Number partition (`numberDomainPartition`)**: positions 0 (SG)
  and 1 (PL) in the **non-dual** domain; position 2 (DL) in the
  **dual** domain. The boundary corresponds to [harbour-2014]'s
  feature-recursion split where dual is the marked extension over
  the SG/PL base.

## Scope of the formalization

The substrate's converse-direction theorem — "domain-aware DM
generates AAB patterns when positions are split" — requires
extending `LocalVIRule` (`Morphology.DM.ContainmentVI.Degree`)
with a domain field so that a rule's locality bound becomes
partition-aware rather than the unconditional Bobaljik bound
`condGrade.rank ≤ DegreeGrade.cmpr.rank`. That's a separate substrate
addition deferred to a follow-up.

What this section ships:
- The two partition definitions above, with citations
- Structural facts about the partitions (cells 1 and 2 lie in
  different domains under both)
- Documentation of where the converse-direction theorem would land
-/

open Morphology.DomainLocality

/-- The 3-cell ergative case paradigm SMSE 2019 analyses: position 0 is
    ABS, position 1 is ERG, position 2 is DAT. Positions outside this
    range have no case interpretation (`none`); they default to the
    non-oblique domain in `caseDomainPartition`. -/
def caseAtPos : Nat → Option Case
  | 0 => some .abs
  | 1 => some .erg
  | 2 => some .dat
  | _ => none

/-- Case partition: derived from `Case.IsOblique` via `caseAtPos`.
    ABS and ERG are off-hierarchy in `containmentRank` (`IsOblique` is
    `False` for them); DAT contains GEN's representation in the Caha
    order so `IsOblique .dat` is `True`. The boundary thus corresponds
    to [caha-2009]'s Unmarked-Dependent vs Oblique split — *as a
    consequence* of the order substrate, not as a stipulated threshold. -/
def caseDomainPartition : DomainPartition Bool := λ i =>
  (caseAtPos i).elim false (λ c => decide (Case.IsOblique c))

/-- Number partition: SG (position 0) + PL (position 1) in domain
    `false` (non-dual); DL (position 2) in domain `true` (dual).
    The boundary corresponds to [harbour-2014]'s feature-recursion
    split where dual is the marked extension over SG/PL. -/
def numberDomainPartition : DomainPartition Bool := λ i => i ≥ 2

/-- Under the case partition, ERG and DAT (positions 1 and 2) lie in
    DIFFERENT domains. This is the structural feature that makes the
    partition admit AAB patterns like Wardaman 3SG `[0, 0, 1]`. -/
theorem case_partition_splits_erg_dat :
    ¬ SameDomain caseDomainPartition 1 2 := by decide

/-- Under the number partition, PL and DL (positions 1 and 2) lie in
    DIFFERENT domains. -/
theorem number_partition_splits_pl_dl :
    ¬ SameDomain numberDomainPartition 1 2 := by decide

/-- The case AAB witness (Wardaman 3SG) is contiguous under the case
    partition. (Trivially so — `[0, 0, 1]` is *ABA-contiguous in the
    universal sense, and `IsContiguousWithin` is strictly weaker.
    The substantive claim — that domain-aware DM generates this
    pattern — requires the deferred `LocalVIRule` extension.) -/
theorem wardaman_3sg_within_case_domain :
    IsContiguousWithin caseDomainPartition wardamanThirdSg := by decide

/-- The number AAB witness (Yagua 2) is contiguous under the number
    partition. Same caveat as the case-side. -/
theorem yagua_2_within_number_domain :
    IsContiguousWithin numberDomainPartition yaguaSecond := by decide

/-! ## What's deferred

The substrate above sets up the partition + the structural facts
that the partitions split the relevant cells. The substantive
converse-direction theorem — "under the case partition, there exist
domain-aware VI rule lists generating Wardaman 3SG-shape patterns"
— requires `Morphology.DM.ContainmentVI.Degree.LocalVIRule` to
be extended with a domain field so its locality bound becomes
partition-relativized. The current `LocalVIRule.locality` field is structurally Bobaljik-style
(`condGrade.rank ≤ cmpr.rank`, unconditional) and forces `vi_cmpr_eq_sprl`
regardless of partition. A domain-aware variant requires a
partition-aware cap-refinement on the rule type itself, sketched below.

A concrete `DomainLocalVIRule` shape for that follow-up:

```
structure DomainLocalVIRule {Tag : Type*} [DecidableEq Tag]
    (π : DomainPartition Tag) where
  formClass : Nat
  condGrade : DegreeGrade
  specificity : Nat
  domainLocality : ∃ targetGrade : DegreeGrade,
    SameDomain π condGrade.rank targetGrade.rank
```

with `viWinner_eq_within_domain` proving the conditional analog of
`vi_cmpr_eq_sprl` and a constructive `domain_locality_admits_aab`
showing AAB rule lists exist when positions are split.
-/

end SmithMoskalEtAl2019
