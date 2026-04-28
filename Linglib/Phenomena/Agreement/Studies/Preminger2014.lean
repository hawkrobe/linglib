import Linglib.Theories.Syntax.Minimalist.Agree
import Linglib.Theories.Syntax.Minimalist.PersonGeometry
import Linglib.Theories.Interfaces.SyntaxPhonology.Minimalist.Spellout
import Linglib.Fragments.Mayan.Kaqchikel.Agreement

/-!
# Preminger 2014 — Agreement and Its Failures @cite{preminger-2014}
@cite{bejar-rezac-2003} @cite{halle-marantz-1993} @cite{harley-ritter-2002}
@cite{stiebels-2006} @cite{halpert-2012}

@cite{preminger-2014}, *Agreement and Its Failures* (MIT Press, LI
Monographs 68), applies @cite{bejar-rezac-2003}'s relativized-probing
mechanism (with the Person Licensing Condition) to the Kichean Agent
Focus construction (Ch. 4) and uses the resulting failure cases to
argue for an "obligatory operations" model of φ-Agree (Ch. 5). The
fragment in `Fragments/Mayan/Kaqchikel/Agreement.lean` carries the
typology-neutral data (paradigm exponents, person-number cells,
argument positions, the empirical AF table); this file adds the
analytical apparatus.

## Attribution discipline

Per Preminger's own framing:

- The **feature geometry** [φ] → [PERSON] → [participant] → [author]
  traces to @cite{harley-ritter-2002}; @cite{preminger-2014} adopts it.
- The **relativized-probing mechanism** and the **Person Licensing
  Condition (PLC)** are @cite{bejar-rezac-2003}'s; Preminger §4.1 is
  titled "Background: The Person Case Constraint, and Béjar and
  Rezac's (2003) Account of It" and §4.4 is "Applying Béjar and
  Rezac's (2003) Account to Kichean".
- **DM Vocabulary insertion** for setAVocab/setBVocab follows
  @cite{halle-marantz-1993}'s Distributed Morphology framework.
- What is **distinctively Preminger 2014**:
  - Application of @cite{bejar-rezac-2003} to Kichean AF specifically
    (Ch 4), with a Kichean-specific structural priority of π⁰ over
    #⁰ deriving the surface "overflow" pattern.
  - Arguments against direct salience-hierarchy primitives (Ch 7),
    targeted at @cite{stiebels-2006} and similar accounts.
  - The "obligatory operations" model of φ-Agree (Ch 5): φ-Agree is
    obligatory but failure-tolerant; failed Agree surfaces as the
    Elsewhere (3SG ∅) entry rather than crashing the derivation.

## Two-probe relativized probing

§4.4 derives the Kichean AF agreement target from two independently
relativized probes:

- **π⁰** seeks [participant]: targets 1st/2nd person DPs, skips 3rd.
- **#⁰** seeks [plural]: targets plural DPs, skips singulars.

The single AF marker reflects π⁰'s output if it succeeds (clitic
doubling of the [participant]-bearing argument); otherwise #⁰'s
output (the 3PL marker *e-* by direct exponence); otherwise the
Elsewhere (3SG ∅) entry. Person and number probes are applied
*independently* — there is no salience scale.

## Why not a hierarchy

A surface-equivalent hierarchy `[+participant] > [+plural] > default`
would predict the same outputs on the table-(22) cells, but Ch 7
provides **five** arguments against it (§7.3 summary, p. 127):

1. **Restrictedness** (§7.1, p. 124): "salience" effects surface
   nowhere else in the language — cognitive salience would predict
   them in regular transitives too.
2. **K'ichee' formal addressee *la*** (p. 124–125): a 2nd-person
   pronoun that behaves morphosyntactically as 3rd person under
   AF, contrary to a hierarchy that ranks 2nd ≫ 3rd.
3. **AF person restriction asymmetry** (p. 125): hierarchies don't
   predict why two 1st/2nd persons are blocked but two 3rd plurals
   are licit.
4. **Morphophonological 1st/2nd vs 3rd asymmetry** ("perhaps
   strongest", §3.4 + p. 125–126, table (148)): 1st/2nd ABS markers
   stand in the relation `<agreement marker> = <strong pronoun>
   – <initial approximant>` (eq. 149) — a clitic-doubling signature.
   3rd-person markers don't. A hierarchy can't capture this.
5. **Zulu cross-linguistic parallel** (§7.2, p. 127):
   @cite{halpert-2012}'s analysis of Zulu augmentless nominals uses
   the same machinery, but operating over augmented/augmentless
   instead of person/number — substantively different categories
   that have no plausible "salience" interpretation. The same
   logic applying to a salience-irrelevant feature contrast
   undermines the cognitive-salience grounding entirely.

Theorems below verify (3) on the fragment data; (4) is encoded as
a smoke check (the fragment carries ABS markers but not strong
pronouns, so the genuine eq.-149 relation cannot be verified
without extending the fragment); (1), (2), (5) are documented in
prose and would require additional fragment data (regular
transitives + K'ichee' fragment + Zulu fragment) to formalize.

## Cross-references

- `Theories/Syntax/Minimalist/PersonGeometry.lean` — the substrate:
  `decomposePerson`, `probeResolutionRank`, multi-cited
  (@cite{harley-ritter-2002}, @cite{bejar-rezac-2003},
  @cite{preminger-2014}, @cite{pancheva-zubizarreta-2018}).
- `Theories/Interfaces/SyntaxPhonology/Minimalist/Spellout.lean` —
  the substrate: `Vocabulary`, `VocabEntry`, `makePersonVocab`.
- `Phenomena/Agreement/Studies/Scott2023.lean` — parallel
  application of the same DM/Agree machinery to Mam (where Infl's
  φ-probe is blocked in transitives).
- `Phenomena/Ergativity/Studies/CoonMateoPedroPreminger2014.lean` —
  Voice/case-flavor side of the same author cluster's Mayan work.
-/

namespace Phenomena.Agreement.Studies.Preminger2014

open Fragments.Mayan.Kaqchikel
open Minimalist

-- ============================================================================
-- § 1: Feature Decomposition (grounded in PersonGeometry.lean)
-- ============================================================================

/-- Bears [+participant]? Derived from @cite{harley-ritter-2002}'s
    feature geometry via `decomposePerson` (PersonGeometry.lean). -/
def IsParticipant (pn : PersonNumber) : Prop :=
  (decomposePerson pn.person).hasParticipant = true

instance : DecidablePred IsParticipant := fun pn =>
  inferInstanceAs (Decidable ((decomposePerson pn.person).hasParticipant = true))

/-- Bears [+author]? -/
def IsAuthor (pn : PersonNumber) : Prop :=
  (decomposePerson pn.person).hasAuthor = true

instance : DecidablePred IsAuthor := fun pn =>
  inferInstanceAs (Decidable ((decomposePerson pn.person).hasAuthor = true))

/-- Convert a person-number cell to a PhiFeature list for the Agree
    infrastructure. -/
def toPhiFeatures : PersonNumber → List PhiFeature
  | .p1sg => [.person .first, .number .sg]
  | .p2sg => [.person .second, .number .sg]
  | .p3sg => [.person .third, .number .sg]
  | .p1pl => [.person .first, .number .pl]
  | .p2pl => [.person .second, .number .pl]
  | .p3pl => [.person .third, .number .pl]

-- ============================================================================
-- § 2: DM Vocabulary Insertion (@cite{halle-marantz-1993})
-- ============================================================================

/-- Set A as DM Vocabulary entries, contextualized to Voice/v.
    Built via the shared `makePersonVocab` helper. -/
def setAVocab : Vocabulary :=
  makePersonVocab personNumbers toPhiFeatures setAExponent (some .v)

/-- Set B as DM Vocabulary entries, contextualized to Infl/T. -/
def setBVocab : Vocabulary :=
  makePersonVocab personNumbers toPhiFeatures setBExponent (some .T)

-- ============================================================================
-- § 3: Two-Probe Relativized Probing (@cite{bejar-rezac-2003}, applied per §4.4)
-- ============================================================================

/-- Probe-resolution rank for a Kaqchikel person-number cell under the
    two-probe (π⁰ ≫ #⁰) system. Computed via `probeResolutionRank`
    on the cell's person + number features. NOT a salience scale —
    see module docstring. -/
def afRank (pn : PersonNumber) : Nat :=
  probeResolutionRank pn.person pn.isPlural

/-- Person restriction (@cite{preminger-2014} (25)): at most one core
    argument can bear [+participant]. Derives from the Person
    Licensing Condition (PLC, @cite{bejar-rezac-2003}; cf.
    @cite{preminger-2014} §4.4 (75)): a [+participant] argument
    requires an Agree relation with π⁰ to be licensed. Two
    [+participant] arguments compete for π⁰'s single Agree relation;
    only one can be licensed; the derivation crashes if both occur.
    This is the syntactic licensing story, not the morphological
    clitic-slot competition. -/
def PersonRestrictionOk (subj obj : PersonNumber) : Prop :=
  ¬(IsParticipant subj ∧ IsParticipant obj)

instance (subj obj : PersonNumber) : Decidable (PersonRestrictionOk subj obj) :=
  inferInstanceAs (Decidable (¬(IsParticipant subj ∧ IsParticipant obj)))

/-- Compute the AF agreement target: the higher-ranked argument under
    the two-probe system. When both have equal rank, the subject is
    chosen (yielding the same marker either way). Returns `none` if
    the person restriction is violated. -/
def afAgreementTarget (subj obj : PersonNumber) : Option PersonNumber :=
  if PersonRestrictionOk subj obj then
    if afRank subj ≥ afRank obj then some subj else some obj
  else none

/-- The AF agreement marker for a given subject-object combination:
    Set B exponent of the resolved target, or `none` for restriction
    violations. -/
def afMarker (subj obj : PersonNumber) : Option String :=
  (afAgreementTarget subj obj).map setBExponent

-- ============================================================================
-- § 4: Verification — Grounding in PersonGeometry
-- ============================================================================

/-- Compact grounding check covering the four key cells of
    feature-decomposition + probe-rank + author-implies-participant.
    Replaces what would otherwise be ~6 separate single-cell rfl
    theorems (per-cell-rfl-inflation anti-pattern). -/
theorem feature_decomposition_correct :
    -- IsParticipant matches H&R 2002 + B&R 2003 expectations
    IsParticipant .p1sg ∧
    IsParticipant .p2sg ∧
    ¬IsParticipant .p3sg ∧
    ¬IsParticipant .p3pl ∧
    -- author entails participant (H&R 2002 containment)
    (∀ pn ∈ personNumbers, IsAuthor pn → IsParticipant pn) ∧
    -- two-probe ranks: [+participant] → 2, [+plural,−participant] → 1, 3SG → 0
    afRank .p1sg = 2 ∧ afRank .p2sg = 2 ∧
    afRank .p3pl = 1 ∧ afRank .p3sg = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals decide

-- ============================================================================
-- § 5: Verification — AF Paradigm (@cite{preminger-2014} table (22))
-- ============================================================================

/-- The full AF paradigm (table 22) is correctly predicted: each
    empirical datum in the fragment's `afParadigm` matches `afMarker`. -/
theorem af_paradigm_correct :
    afParadigm.all (λ d => afMarker d.subject d.object == d.marker) = true := by
  decide

/-- AF agreement is commutative: swapping subject and object yields
    the same marker for ALL person-number combinations
    (@cite{preminger-2014} §3.3, (67)). Falls out of two-probe
    relativized probing — the probes see both arguments
    symmetrically. -/
theorem af_commutative :
    personNumbers.all (λ s => personNumbers.all (λ o =>
      afMarker s o == afMarker o s)) = true := by
  decide

/-- π⁰ output suppresses #⁰ when both have a target: when one
    argument is 1st/2nd and the other is 3PL, the marker reflects
    the participant (clitic-doubling output of π⁰), not the plural. -/
theorem participant_over_plural :
    afMarker .p1sg .p3pl = some "in-" ∧
    afMarker .p3pl .p2sg = some "at-" :=
  ⟨rfl, rfl⟩

/-- PLC violation: two [+participant] arguments are blocked. Default
    3SG: when both arguments are 3SG, both probes fail to find a
    target and the Elsewhere entry (∅) surfaces — the empirical
    signature of obligatory-but-failure-tolerant Agree
    (@cite{preminger-2014} Ch. 5). -/
theorem restriction_and_default :
    afMarker .p1sg .p2sg = none ∧
    afMarker .p2sg .p1sg = none ∧
    afMarker .p3sg .p3sg = some "∅" :=
  ⟨rfl, rfl, rfl⟩

/-- Person restriction is symmetric on the cells. -/
theorem person_restriction_symmetric (s o : PersonNumber) :
    PersonRestrictionOk s o ↔ PersonRestrictionOk o s := by
  unfold PersonRestrictionOk
  exact ⟨fun h ⟨h₁, h₂⟩ => h ⟨h₂, h₁⟩, fun h ⟨h₁, h₂⟩ => h ⟨h₂, h₁⟩⟩

-- ============================================================================
-- § 6: Verification — Ch 7 Anti-Hierarchy Arguments (3 of 5)
-- ============================================================================

/-- @cite{preminger-2014} Ch 7 arg 3 (p. 125): a salience hierarchy
    `[+participant] > [+plural] > default` predicts symmetric
    blocking — if 1+2 (two participants) is bad, then 3pl+3pl (two
    plurals) should also be bad by the same logic. The data shows
    1+2 IS blocked (PLC violation) but 3pl+3pl is FINE. The
    two-probe + PLC analysis derives this asymmetry: π⁰ targets
    [participant] under PLC (single Agree relation → restriction);
    #⁰ targets [plural] without a parallel licensing condition (no
    competition for 3pl+3pl). -/
theorem ch7_arg3_participant_vs_plural_asymmetry :
    -- 1+2 is blocked (PLC violation)
    afMarker .p1sg .p2sg = none ∧
    -- but 3pl+3pl is fine (no parallel licensing condition for #⁰)
    afMarker .p3pl .p3pl = some "e-" :=
  ⟨rfl, rfl⟩

/-- @cite{preminger-2014} Ch 7 arg 4 smoke-check (p. 125–126,
    table (148), eq. (149)): 1st/2nd ABS markers stand in the
    relation `<agreement marker> = <strong pronoun> – <initial
    approximant>` (e.g., 1sg `i(n)-` from *yïn*, 1pl `oj-` from
    *röj*). 3rd-person markers don't have this property — pointing
    to clitic doubling for 1st/2nd vs direct exponence for 3rd.

    UNVERIFIED: this theorem only checks that 1st/2nd and 3rd ABS
    markers are *distinct in form*, which is necessary but not
    sufficient for arg 4. The genuine eq.-(149) relation requires
    strong-pronoun forms (yïn, rat, röj, rïx, rja', rje') which the
    fragment does not currently carry. A faithful arg-4 theorem
    awaits extending the fragment with strong pronouns and a
    suffix-stripping bridge function. -/
theorem ch7_arg4_form_distinctness_smoke_check :
    setBExponent .p1sg = "in-" ∧
    setBExponent .p2sg = "at-" ∧
    setBExponent .p1pl = "oj-" ∧
    setBExponent .p2pl = "ix-" ∧
    setBExponent .p3pl = "e-" ∧
    setBExponent .p1sg ≠ setBExponent .p3pl ∧
    setBExponent .p2sg ≠ setBExponent .p3pl ∧
    setBExponent .p1pl ≠ setBExponent .p3pl ∧
    setBExponent .p2pl ≠ setBExponent .p3pl :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩

end Phenomena.Agreement.Studies.Preminger2014
