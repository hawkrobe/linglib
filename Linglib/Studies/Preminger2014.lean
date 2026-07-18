import Linglib.Syntax.Minimalist.Phi.Geometry
import Linglib.Syntax.Minimalist.Probe.Phi
import Linglib.Morphology.DM.VocabSimple
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Studies.Halpert2012
import Linglib.Studies.BejarRezac2003

/-!
# Preminger 2014 — Agreement and Its Failures [preminger-2014]
[bejar-rezac-2003] [halle-marantz-1993] [harley-ritter-2002]
[nevins-2011] [stiebels-2006] [halpert-2012]

[preminger-2014], *Agreement and Its Failures* (MIT Press, LI
Monographs 68), applies [bejar-rezac-2003]'s split-probe system and
Person Licensing Condition — with relativized probing, Preminger's
own addition (§4.2) — to the Kichean Agent Focus
construction (Ch. 4) and uses the resulting failure cases to argue
for an "obligatory operations" model of φ-Agree (Ch. 5). The
fragment in `Fragments/Mayan/Kaqchikel/Agreement.lean` carries the
theory-neutral data; this file adds the analytical apparatus.
Section and example numbers below were verified against the
monograph manuscript; page numbers are omitted (draft and published
pagination differ).

## Attribution discipline

Per Preminger's own framing:

- The **feature geometry** [φ] → [PERSON] → [participant] → [author]
  traces to [harley-ritter-2002]; [preminger-2014] adopts a
  simplified version.
- The **split π/# probes** (person probing first) and the **Person
  Licensing Condition (PLC)** are [bejar-rezac-2003]'s (§4.1, §4.4).
  **Relativized probing** is Preminger's own addition (§4.2,
  recalling [rizzi-1990]) — B&R's π-probe is explicitly NOT
  relativized (see `Studies/BejarRezac2003.lean` and
  `ch4_relativization_contrast`). The separate-heads implementation
  (π⁰ merged below #⁰, probing first; B&R put both probes on one
  head) is also Preminger's; what surfaces is decided by a single
  morphological slot in which a clitic beats out the exponence of
  π⁰/#⁰.
- **Omnivorous agreement** as the name for the surface pattern is
  [nevins-2011]'s term, which Preminger adopts.
- **DM Vocabulary insertion** for `setAVocab`/`setBVocab` follows
  [halle-marantz-1993]. The Elsewhere ∅ entry is this
  formalization's DM rendering: Preminger's own statement is that
  the absolutive paradigm has no overt 3rd-person-singular
  exponence, so failed probing leaves the slot empty.
- What is **distinctively Preminger 2014**: relativizing π⁰ to
  [participant] and #⁰ to [plural] for Kichean AF (Ch. 4); the
  "obligatory operations" model of φ-Agree (Ch. 5) — φ-Agree is
  obligatory but failure-tolerant, with failed Agree surfacing as
  default morphology rather than crashing the derivation; and the
  Ch. 7 case against salience-hierarchy primitives (the Mayanist
  hierarchy tradition: Dayley, Smith-Stark, Norman & Campbell,
  Mondloch; and constraint-based recastings such as
  [stiebels-2006]).

## Two-probe relativized probing

§4.4 derives the Kichean AF agreement target from two independently
relativized probes:

- **π⁰** seeks [participant]: targets 1st/2nd person DPs, skips 3rd.
- **#⁰** seeks [plural]: targets plural DPs, skips singulars.

The single AF marker reflects π⁰'s output if it succeeds (clitic
doubling of the [participant]-bearing argument); otherwise #⁰'s
output (the 3PL marker *e-* by direct exponence); otherwise the slot
is empty (∅). This slot competition is `Probe.cascade` over the two
probes, definitionally: `afAgreementTarget` IS the cascade, the ∅
row is failed Agree realized by the DM Elsewhere entry, and the rank
comparison is the derived form (`afAgreementTarget_eq_rank`).
There is no salience scale, and `personRestrictionOk_iff_plc`
derives the person restriction from the PLC via `Probe/Phi.lean`'s
search-licensing substrate.

## Why not a hierarchy

A surface-equivalent hierarchy `[+participant] > [+plural] > default`
would predict the same outputs on the table-(22) cells, but Ch. 7
gives five arguments against hierarchy accounts:

1. **Restrictedness** (§7.1): "salience" effects surface nowhere
   else in the language (prose only — needs regular-transitive data).
2. **K'ichee' formal addressee *la***: a 2nd-person pronoun that is
   morphosyntactically 3rd person under AF, contrary to 2 ≫ 3
   (prose only — needs a K'ichee' fragment).
3. **Co-occurrence asymmetry**: a hierarchy is silent on
   co-occurrence — nothing about it explains why two 1st/2nd-person
   arguments cannot co-occur while two 3rd-plurals can. The
   two-probe + PLC account derives both the agreement pattern and
   the restriction; the hierarchy derives only the former
   (`ch7_arg3_participant_vs_plural_asymmetry`).
4. **Morphophonology of the markers** ("perhaps strongest" per
   §7.1; the morphophonology is detailed in §3.4):
   1st/2nd ABS markers stand in the relation `<agreement marker> =
   <strong pronoun> − <initial approximant>` (149) — a
   clitic-doubling signature that 3rd-person markers lack
   (smoke check only — the fragment lacks strong-pronoun forms).
5. **Zulu parallel** (§7.2): [halpert-2012]'s analysis of Zulu
   augmentless nominals uses the same machinery over
   augmented/augmentless — categories with no plausible "salience"
   reading (`ch7_arg5_zulu_parallel`, via `Studies/Halpert2012.lean`).

## Cross-references

- `Syntax/Minimalist/Phi/Geometry.lean` — `decomposePerson`,
  `probeVisible`, `probeResolutionRank`.
- `Syntax/Minimalist/Probe/Basic.lean` — `Probe`, `Probe.Licensed`,
  `Probe.outcome`/`Probe.Outcome` (the Ch. 5 valued/unvalued result of an
  obligatory probe); `Probe/Phi.lean` — `PLC`: the search-and-licensing layer
  the derivations below consume. Failed Agree = an `unvalued` probe outcome
  that is *tolerated* (no crash) and spells out as the Elsewhere entry.
- `Morphology/DM/VocabSimple.lean` — `Vocabulary`,
  `Agreement.Cell.toPhiFeatures`, `makePersonVocab`, `spellout`.
- `Studies/Scott2023.lean` — the same DM/Agree machinery applied to
  Mam (where Infl's φ-probe is blocked in transitives).
- `Studies/CoonMateoPedroPreminger2014.lean` — Voice/case-flavor
  side of the same author cluster's Mayan work.
-/

namespace Preminger2014

open Kaqchikel
open Minimalist
open Agreement

/-! ### Feature decomposition (grounded in `Phi/Geometry.lean`) -/

/-- Bears [+participant]? Visibility to π⁰ under relativized probing
    ([bejar-rezac-2003] via `Agreement.Cell.visibleTo`); derives from
    [harley-ritter-2002]'s feature geometry through `decomposePerson`. -/
def IsParticipant (c : Agreement.Cell) : Prop :=
  c.visibleTo .participant = true

instance : DecidablePred IsParticipant := fun c =>
  inferInstanceAs (Decidable (c.visibleTo .participant = true))

/-- Bears [+author]? -/
def IsAuthor (c : Agreement.Cell) : Prop :=
  (decomposePerson c.toPerson).hasAuthor = true

instance : DecidablePred IsAuthor := fun c =>
  inferInstanceAs (Decidable ((decomposePerson c.toPerson).hasAuthor = true))

/-- [author] entails [participant]: the [harley-ritter-2002] geometric
    containment, inherited from `decomposePerson`. -/
theorem isParticipant_of_isAuthor (c : Agreement.Cell) :
    IsAuthor c → IsParticipant c := by
  unfold IsAuthor IsParticipant Agreement.Cell.visibleTo
  simp only [probeVisible]
  cases c.toPerson <;> decide

/-! ### DM Vocabulary insertion ([halle-marantz-1993]) -/

/-- The valued feature bundle a probe carries after agreeing with a
    DP in cell `c`. -/
private def cellBundle (c : Agreement.Cell) : FeatureBundle :=
  .ofGramFeatures (c.toPhiFeatures.map (λ p => .valued (.phi p)))

/-- Set A as DM Vocabulary entries, contextualized to Voice/v.
    All six cells have overt exponents. -/
def setAVocab : Vocabulary :=
  makePersonVocab Agreement.Cell.pnCells Agreement.Cell.toPhiFeatures
    (fun c => (((setAExponent .consonant).realize c).map
      Morphology.Exponent.toString).getD "") (some .v)

/-- Set B as DM Vocabulary entries, contextualized to Infl/T: specific
    entries for the five overt cells, plus the Elsewhere ∅ entry
    realizing 3SG and failed agreement (see the module docstring on
    this DM rendering vs. Preminger's own formulation). -/
def setBVocab : Vocabulary :=
  makePersonVocab (Agreement.Cell.pnCells.filter (· != .pn .third .Sing))
    Agreement.Cell.toPhiFeatures
    (fun c => ((setBExponent.realize c).map
      Morphology.Exponent.toString).getD "") (some .T) ++
  [{ features := ⊥, exponent := "∅", context := some .T }]

/-- Vocabulary insertion recovers the fragment's paradigms: spelling
    out each cell's valued bundle yields the fragment's exponent — for
    Set B, the 3SG cell via the Elsewhere entry, the rest via their
    specific entries. -/
theorem spellout_matches_paradigm :
    ∀ c ∈ Agreement.Cell.pnCells,
      spellout setAVocab (cellBundle c) (some .v) =
        ((setAExponent .consonant).realize c).map Morphology.Exponent.toString ∧
      spellout setBVocab (cellBundle c) (some .T) =
        (setBExponent.realize c).map Morphology.Exponent.toString := by
  decide

/-! ### Two-probe relativized probing ([bejar-rezac-2003], applied per §4.4) -/

/-- Probe-resolution rank for a Kaqchikel person-number cell under the
    two-probe (π⁰ before #⁰) system. Computed via `probeResolutionRank`
    on the cell's person + number features. NOT a salience scale —
    `afAgreementTarget_eq_rank` derives the rank comparison from the
    probe cascade. -/
def afRank (c : Agreement.Cell) : Nat :=
  probeResolutionRank c.toPerson c.isPlural

/-- Person restriction ([preminger-2014] (25)): at most one core
    argument can bear [+participant]. The empirical generalization;
    it DERIVES from the Person Licensing Condition — see
    `personRestrictionOk_iff_plc`. This is the syntactic licensing
    story, not the morphological clitic-slot competition. -/
def PersonRestrictionOk (subj obj : Agreement.Cell) : Prop :=
  ¬(IsParticipant subj ∧ IsParticipant obj)

instance : DecidableRel PersonRestrictionOk := fun subj obj =>
  inferInstanceAs (Decidable ¬(IsParticipant subj ∧ IsParticipant obj))

/-- The person restriction derives from the PLC ([bejar-rezac-2003];
    [preminger-2014] §4.4 (75)): with the AF clause's agent and
    patient as π⁰'s goal tokens, the PLC holds iff at most one bears
    [+participant]. A [+participant] argument requires an Agree
    relation with π⁰ to be licensed; π⁰'s single search licenses at
    most one token (`Probe.allLicensed_iff`), so two [+participant]
    arguments cannot both be licensed and the derivation crashes. -/
theorem personRestrictionOk_iff_plc (s o : Agreement.Cell) :
    PersonRestrictionOk s o ↔
      PLC Prod.snd ([(.A, s), (.P, o)] : List (ArgPosition × Agreement.Cell)) := by
  unfold PersonRestrictionOk PLC
  rw [Probe.allLicensed_iff]
  constructor
  · intro h a ha b hb hva hvb
    rcases List.mem_pair.mp ha with rfl | rfl <;>
      rcases List.mem_pair.mp hb with rfl | rfl
    · rfl
    · exact absurd ⟨hva, hvb⟩ h
    · exact absurd ⟨hvb, hva⟩ h
    · rfl
  · rintro h ⟨hs, ho⟩
    exact nomatch congrArg Prod.fst
      (h (.A, s) (.head _) (.P, o) (.tail _ (.head _)) hs ho)

/-- [preminger-2014] Ch. 4's move (§4.2), made formal:
    [bejar-rezac-2003]'s ⊤-visible π-probe is absorbed by an
    F-licensed 3rd-person dative, stranding a participant below it —
    the PCC. The Kichean π⁰, relativized to [participant], skips the
    same 3rd-person goal and licenses the lower participant.
    Relativization to exactly the licensing-needy class is what
    converts absorption into omnivorous licensing. -/
theorem ch4_relativization_contrast :
    ¬ BejarRezac2003.PLCOk [[⟨.third, true⟩, ⟨.first, false⟩]]
        [⟨.third, true⟩, ⟨.first, false⟩] ∧
    PLC Prod.snd ([(.A, .pn .third .Sing), (.P, .pn .first .Sing)] :
        List (ArgPosition × Agreement.Cell)) := by
  decide

/-- π⁰: the person probe — the denotation of the substrate's
    `Probe.Target.participant` specification. -/
def piProbe : Probe Agreement.Cell := Probe.Target.participant.toProbe

/-- #⁰: the number probe — the denotation of `Probe.Target.plural`. -/
def numProbe : Probe Agreement.Cell := Probe.Target.plural.toProbe

/-- The two AF probes in slot order: π⁰'s clitic output beats #⁰'s
    direct exponence in the single morphological slot
    ([preminger-2014] §4.4). -/
def afProbes : List (Probe Agreement.Cell) := [piProbe, numProbe]

/-- The AF agreement target, by probe cascade: π⁰'s goal if it finds
    one, else #⁰'s, else `none` — both probes failed (3SG × 3SG) and
    the slot stays empty. Pure Agree: grammaticality (the PLC) is
    checked at `afMarker`. When both arguments are visible to the
    winning probe it takes the closer one (the subject) — immaterial
    for the marker (`afMarker_comm`). -/
def afAgreementTarget (subj obj : Agreement.Cell) : Option Agreement.Cell :=
  Probe.cascade afProbes [subj, obj]

/-- The AF agreement marker: the Set B exponent of the cascade's
    target; the Elsewhere ∅ via DM insertion from the unvalued bundle
    when both probes failed; `none` (ungrammatical) when the PLC
    fails on the clause's goal tokens (equivalently, when the surface
    person restriction is violated: `personRestrictionOk_iff_plc`). -/
def afMarker (subj obj : Agreement.Cell) : Option String :=
  if PLC Prod.snd ([(.A, subj), (.P, obj)] : List (ArgPosition × Agreement.Cell)) then
    ((afAgreementTarget subj obj).bind
      (fun t => (setBExponent.realize t).map Morphology.Exponent.toString)) <|>
      spellout setBVocab ⊥ (some .T)
  else none

/-- The rank encoding (`probeResolutionRank`, [bejar-rezac-2003]
    convenience form) is derived from the cascade: on the φ-cell
    inventory the cascade's target is the higher-ranked argument —
    except that double rank-0 (both probes fail) is an honest `none`
    rather than a default target. -/
theorem afAgreementTarget_eq_rank :
    ∀ s ∈ Agreement.Cell.pnCells, ∀ o ∈ Agreement.Cell.pnCells,
      afAgreementTarget s o =
        if afRank s = 0 ∧ afRank o = 0 then none
        else if afRank s ≥ afRank o then some s else some o := by
  decide

/-! ### Verification: grounding in `Phi.Geometry` -/

/-- Smoke check: feature decomposition and probe ranks on the key
    cells match the [harley-ritter-2002] + [bejar-rezac-2003]
    expectations — [+participant] → rank 2, [+plural, −participant]
    → rank 1, 3SG → rank 0. -/
theorem feature_decomposition_cells :
    IsParticipant (.pn .first .Sing) ∧
    IsParticipant (.pn .second .Sing) ∧
    ¬IsParticipant (.pn .third .Sing) ∧
    ¬IsParticipant (.pn .third .Plur) ∧
    afRank (.pn .first .Sing) = 2 ∧ afRank (.pn .second .Sing) = 2 ∧
    afRank (.pn .third .Plur) = 1 ∧ afRank (.pn .third .Sing) = 0 := by
  decide

/-! ### The AF paradigm data ([preminger-2014] §3.2, table (22)) -/

/-- An AF agreement datum: subject φ, object φ, and the observed single
    agreement marker — `none` for person-restriction violations, where
    AF is impossible and the plain full-agreement transitive surfaces
    instead (his (27)). -/
structure AFAgreementDatum where
  subject : Cell
  object : Cell
  marker : Option String
  deriving Repr

/-- The empirical AF agreement paradigm: the 11 unordered cells of
    table (22) (§3.2), oriented subject-first — the table pools
    subject/object φ as unordered sets `{φ₁, φ₂}` (its note a);
    order-invariance is the theorem `afMarker_comm`, not extra data —
    plus one person-restriction gap ((25): at most one core argument
    may be 1st/2nd person). -/
def afParadigm : List AFAgreementDatum :=
  [ -- rows 1–3: both 3rd person, number determines the marker
    ⟨.pn .third .Sing, .pn .third .Sing, some "∅"⟩         -- default: 3SG×3SG → ∅
  , ⟨.pn .third .Plur, .pn .third .Sing, some "e-"⟩        -- [+plural] outranks default
  , ⟨.pn .third .Plur, .pn .third .Plur, some "e-"⟩        -- [+plural] both → 3PL
    -- rows 4–7: one [+participant] argument with 3SG
  , ⟨.pn .first .Sing, .pn .third .Sing, some "in-"⟩       -- 1SG [+participant]
  , ⟨.pn .second .Sing, .pn .third .Sing, some "at-"⟩      -- 2SG [+participant]
  , ⟨.pn .first .Plur, .pn .third .Sing, some "oj-"⟩       -- 1PL [+participant]
  , ⟨.pn .second .Plur, .pn .third .Sing, some "ix-"⟩      -- 2PL [+participant]
    -- rows 8–11: [+participant] outranks [+plural]
  , ⟨.pn .first .Sing, .pn .third .Plur, some "in-"⟩       -- 1SG participant > 3PL plural
  , ⟨.pn .second .Sing, .pn .third .Plur, some "at-"⟩      -- 2SG participant > 3PL plural
  , ⟨.pn .first .Plur, .pn .third .Plur, some "oj-"⟩       -- 1PL participant > 3PL plural
  , ⟨.pn .second .Plur, .pn .third .Plur, some "ix-"⟩      -- 2PL participant > 3PL plural
    -- person restriction ((25)): *two [+participant] arguments
  , ⟨.pn .first .Sing, .pn .second .Sing, none⟩
  ]

/-! ### Verification: AF paradigm -/

/-- The full AF paradigm (table (22)) is correctly predicted: each
    empirical datum in `afParadigm` matches `afMarker`. -/
theorem af_paradigm_correct :
    ∀ d ∈ afParadigm, afMarker d.subject d.object = d.marker := by
  decide

/-- AF agreement is commutative: swapping subject and object yields
    the same marker (empirical statement: §3.2, table (22), which
    pools subject/object φ as unordered sets; derived as a prediction
    of the clitic-doubling account in §4.4, representative pair
    (67a–b)). Of the 36 ordered pairs, the 11 unordered cells of
    table (22) are empirical; pairs of two participants are
    unattestable for independent binding-theoretic reasons and are
    vacuously symmetric (both orders yield `none`). -/
theorem afMarker_comm :
    ∀ s ∈ Agreement.Cell.pnCells, ∀ o ∈ Agreement.Cell.pnCells,
      afMarker s o = afMarker o s := by
  decide

/-- π⁰ output suppresses #⁰ when both have a target: when one
    argument is 1st/2nd and the other is 3PL, the marker reflects
    the participant (clitic-doubling output of π⁰), not the plural. -/
theorem participant_over_plural :
    afMarker (.pn .first .Sing) (.pn .third .Plur) = some "in-" ∧
    afMarker (.pn .third .Plur) (.pn .second .Sing) = some "at-" :=
  ⟨rfl, rfl⟩

/-- PLC violation: two [+participant] arguments are blocked, in
    either order. Both arguments 3SG: both probes fail to find a
    target (`afAgreementTarget` is `none`) and ∅ surfaces from the
    Elsewhere entry (see `failed_agree_tolerated` for the Ch. 5
    reading). -/
theorem restriction_and_default :
    afMarker (.pn .first .Sing) (.pn .second .Sing) = none ∧
    afMarker (.pn .second .Sing) (.pn .first .Sing) = none ∧
    afMarker (.pn .third .Sing) (.pn .third .Sing) = some "∅" :=
  ⟨rfl, rfl, rfl⟩

/-- The person restriction is symmetric. -/
theorem personRestrictionOk_comm (s o : Agreement.Cell) :
    PersonRestrictionOk s o ↔ PersonRestrictionOk o s :=
  not_congr and_comm

/-! ### Obligatory operations ([preminger-2014] Ch. 5) -/

/-- π⁰'s outcome on the AF clause's goal pair: each probe is
    independently obligatory ([preminger-2014] Ch. 5). -/
def piOutcome (subj obj : Agreement.Cell) : Probe.Outcome :=
  piProbe.outcome [subj, obj]

/-- #⁰'s outcome on the AF clause's goal pair. -/
def numOutcome (subj obj : Agreement.Cell) : Probe.Outcome :=
  numProbe.outcome [subj, obj]

/-- Joint outcome of the AF probes: `unvalued` only when both probes
    fail (i.e., both arguments are 3SG). -/
def afProbe.Outcome (subj obj : Agreement.Cell) : Probe.Outcome :=
  match piOutcome subj obj, numOutcome subj obj with
  | .unvalued, .unvalued => .unvalued
  | _, _ => .valued

/-- The cascade comes back empty exactly when the joint probe outcome
    is `unvalued` — Agree-level failure and outcome-level failure are
    the same fact, for arbitrary φ-cells. -/
theorem afAgreementTarget_eq_none_iff (subj obj : Agreement.Cell) :
    afAgreementTarget subj obj = none ↔ afProbe.Outcome subj obj = .unvalued := by
  have hmatch : afProbe.Outcome subj obj = .unvalued ↔
      piOutcome subj obj = .unvalued ∧ numOutcome subj obj = .unvalued := by
    unfold afProbe.Outcome
    cases piOutcome subj obj <;> cases numOutcome subj obj <;> decide
  rw [hmatch]
  unfold afAgreementTarget piOutcome numOutcome
  rw [Probe.cascade_eq_none_iff, Probe.outcome_eq_unvalued_iff,
      Probe.outcome_eq_unvalued_iff]
  simp [afProbes]

/-- Failed Agree is tolerated, not crashing ([preminger-2014] Ch. 5):
    when both probes find no goal (3SG × 3SG), each probe ends
    unvalued, the derivation converges under the
    obligatory-operations model, PF realizes the Elsewhere entry, and
    the observed marker is ∅ — recovered by Vocabulary insertion from
    the unvalued (empty) bundle. Contrast the PLC case in
    `restriction_and_default`: failed *licensing* crashes (`none`);
    failed *Agree* does not. -/
theorem failed_agree_tolerated :
    afAgreementTarget (.pn .third .Sing) (.pn .third .Sing) = none ∧
    piOutcome (.pn .third .Sing) (.pn .third .Sing) = .unvalued ∧
    numOutcome (.pn .third .Sing) (.pn .third .Sing) = .unvalued ∧
    afProbe.Outcome (.pn .third .Sing) (.pn .third .Sing) = .unvalued ∧
    spellout setBVocab ⊥ (some .T) = some "∅" ∧
    afMarker (.pn .third .Sing) (.pn .third .Sing) = some "∅" := by
  decide

/-! ### Verification: Ch. 7 anti-hierarchy arguments (3 of 5) -/

/-- [preminger-2014] Ch. 7 arg 3: a salience hierarchy
    `[+participant] > [+plural] > default` is silent on co-occurrence
    — nothing about it explains why two 1st/2nd-person arguments
    cannot co-occur while two 3rd plurals can. The two-probe + PLC
    analysis derives both: π⁰ targets [participant] under the PLC
    (single Agree relation → restriction); #⁰ targets [plural] with
    no parallel licensing condition (no competition for 3PL + 3PL). -/
theorem ch7_arg3_participant_vs_plural_asymmetry :
    -- 1+2 is blocked (PLC violation)
    afMarker (.pn .first .Sing) (.pn .second .Sing) = none ∧
    -- but 3pl+3pl is fine (no parallel licensing condition for #⁰)
    afMarker (.pn .third .Plur) (.pn .third .Plur) = some "e-" :=
  ⟨rfl, rfl⟩

/-- [preminger-2014] Ch. 7 arg 4 smoke check (§3.4, table (148),
    relation (149)): 1st/2nd ABS markers stand in the relation
    `<agreement marker> = <strong pronoun> − <initial approximant>`
    (e.g., 1sg `i(n)-` from *yïn*, 1pl `oj-` from *röj*; the
    observation traces to Kaufman 1977). 3rd-person markers lack
    this property — pointing to clitic doubling for 1st/2nd vs.
    direct exponence for 3rd.

    UNVERIFIED: this theorem only checks that 1st/2nd ABS markers
    are *distinct in form* from the 3rd-person ones, which is
    necessary but not sufficient for arg 4. The genuine
    relation (149) requires strong-pronoun forms (yïn, rat, röj,
    rïx, rja', rje') which the fragment does not currently carry.
    A faithful arg-4 theorem awaits extending the fragment with
    strong pronouns and a suffix-stripping bridge function. -/
theorem ch7_arg4_form_distinctness :
    ∀ c ∈ [Agreement.Cell.pn .first .Sing, .pn .second .Sing,
           .pn .first .Plur, .pn .second .Plur],
      setBExponent.realize c ≠ setBExponent.realize (.pn .third .Plur) ∧
      setBExponent.realize c ≠ setBExponent.realize (.pn .third .Sing) := by
  decide

/-- [preminger-2014] Ch. 7 arg 5 (§7.2, via Ch. 6): [halpert-2012]'s
    Zulu runs the same search-and-licensing substrate over a
    salience-irrelevant contrast. Kichean is the diagonal instance
    (diagonal `Probe.AllLicensed`: π⁰ relativized to exactly the
    licensing-needy [participant] cells), so a needy argument is
    licensed even from object position — the probe skips non-bearers.
    Zulu's L⁰ is the off-diagonal instance (`Probe.indiscriminate`:
    indiscriminate probe, augmentless = needy), so an augmented
    subject intervenes and a lower augmentless nominal goes
    unlicensed. Same machinery, opposite skippability — and there is
    little plausible salience grounding for augmented/augmentless,
    a contrast sensitive to purely structural relations such as
    c-command, undermining the cognitive-salience grounding of
    hierarchy accounts. Both systems realize failed probing as
    default morphology (Kichean covert ∅, Zulu overt *ya-*). -/
theorem ch7_arg5_zulu_parallel :
    -- Kichean: π⁰ skips a 3SG subject and licenses a 1SG object
    PLC Prod.snd ([(.A, .pn .third .Sing), (.P, .pn .first .Sing)] :
      List (ArgPosition × Agreement.Cell)) ∧
    -- Zulu: an augmented subject intervenes; the augmentless object
    -- is unlicensed
    ¬ Halpert2012.LicensingOk [⟨1, true⟩, ⟨5, false⟩] ∧
    -- both probes' failures converge with default morphology
    afMarker (.pn .third .Sing) (.pn .third .Sing) = some "∅" ∧
    Halpert2012.lSpellout [] = "ya-" := by
  decide

end Preminger2014
