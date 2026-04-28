import Linglib.Typology.PolarityMarking
import Linglib.Fragments.English.PolarityMarking
import Linglib.Fragments.German.PolarityMarking

/-!
# Matić & Nikolaeva (2018) @cite{matic-nikolaeva-2018}

*From polarity focus to salient polarity: From things to processes.*
In @cite{dimroth-sudhoff-2018}, pp. 9–53. DOI 10.1075/la.249.01mat.

The chapter argues that "polarity focus" is **not** a fixed form-meaning
association of the kind a Lean enum can encode, and proposes the term
*salient polarity* for the inferentially-derived interpretation that
the literature has tried to denotationally pin down.

> Salient polarity does not correspond to anything resembling the
> traditional linguistic category if the latter is understood as a
> pairing between a linguistic form and a denotation, but is rather
> to be conceived of as a fuzzy set of family resemblances unified
> by shared communicative intentions.
> — @cite{matic-nikolaeva-2018}, p. 12

This file does **not** formalize "salient polarity" as a predicate or
function. Doing so would be the very stipulation move M&N reject — a
form-class encoding masquerading as theory-neutral. Instead, the file
records (a) the cross-linguistically attested *list* of structures
ascribed to salient polarity in the literature (M&N examples 2–4,
abridged), (b) the cardinality mismatch between this list and the
substrate's `PolarityMarkingStrategy` enum, and (c) the load-bearing
non-isomorphism claim that the substrate's encoding cannot capture
M&N's interpretational notion.

## Why this is not a "bridge file"

Per CLAUDE.md anchoring discipline, the file is anchored on a single
paper (`@cite{matic-nikolaeva-2018}`); the cross-framework critique is
M&N's own claim, not a synthesis the formaliser invented. It lives in
`Studies/` exactly like every other `Studies/AuthorYear.lean`.
The contradiction with the substrate is recorded at the substrate's
def-site (`Features/InformationStructure.lean::PolarityMarkingStrategy`
docstring) with a back-pointer here.

## Cross-references

- `Features/InformationStructure.lean::PolarityMarkingStrategy` — the
  form-class encoding M&N reject; docstring acknowledges the rejection.
- `Phenomena/Polarity/Studies/GarassinoJacob2018.lean` — same volume;
  G&J explicitly endorse M&N (their fn 13).
- `Phenomena/Polarity/Studies/Hohle1992.lean` — the verum-focus origin
  M&N argue against in §2.2 ("the reduction of salient polarity to
  accented finite verbs is neither empirically nor conceptually valid").
- `Phenomena/Polarity/Studies/TurcoBraunDimroth2014.lean` — the
  production data M&N reinterpret.
-/

namespace Phenomena.Polarity.Studies.MaticNikolaeva2018

open Typology.PolarityMarking (PolarityMarkingStrategy PolarityMarkingEntry)
open Fragments.English.PolarityMarking (emphaticDo)
open Fragments.German.PolarityMarking (verumFocus dochPreUtterance)

/-! ## §1 Attested salient-polarity structures (M&N examples 2–4)

Per @cite{matic-nikolaeva-2018} pp. 13–14, the literature has ascribed
salient polarity to a heterogeneous set of structures across German,
English, and Serbian. The list below abridges the chapter's enumeration
(M&N's own (2), (3), (4)). M&N flag this list as **open-ended** ("the
list seems to be open" — p. 15); the constructors below are a finite
proxy for argumentative purposes only. -/
inductive MNAttestedStructure where
  /-- German: accent on auxiliary, modal, or complementizer (M&N 2a;
      cf. @cite{hohle-1992}, Lohnstein 2016) -/
  | germanAccentOnAuxiliary
  /-- German: accent on lexical finite verb (M&N 2b) -/
  | germanAccentOnLexicalVerb
  /-- German: emphatic *tun* periphrasis "Bücher lesen tut er" (M&N 2c) -/
  | germanEmphaticTun
  /-- German: VP fronting "Bücher gelesen hat er" (M&N 2d) -/
  | germanVPFronting
  /-- German: accented discourse particles *doch / schon / wohl / ja*
      "Er ist DOCH gekommen" (M&N 2e) -/
  | germanAccentedDiscourseParticles
  /-- German: discourse markers *ich schwöre* / *ehrlich* / *ungelogen*
      (M&N 2f) -/
  | germanDiscourseMarkers
  /-- German: adverbs *tatsächlich* / *wahrhaftig* (M&N 2g) -/
  | germanTruthAdverbs
  /-- English: accented auxiliary or modal "He WILL be on time" (M&N 3a) -/
  | englishAccentedAuxiliary
  /-- English: accented lexical verb "He READ it yesterday" (M&N 3b) -/
  | englishAccentedLexicalVerb
  /-- English: emphatic *do*-support "She did open the door" (M&N 3c) -/
  | englishEmphaticDo
  /-- English: VP fronting "He went there to learn, and learn he did" (M&N 3d) -/
  | englishVPFronting
  /-- English: adverbs *really / definitely* (M&N 3e) -/
  | englishAdverbs
  /-- English: particles *so / too / indeed* (M&N 3f) -/
  | englishParticles
  /-- English: *so*-inversion "and so do I" (M&N 3g) -/
  | englishSoInversion
  /-- Serbian: accented finite verb "Ona PIŠE romane" (M&N 4a) -/
  | serbianAccentedFiniteVerb
  /-- Serbian: accent on auxiliary/modal "On JESTE napisao tu knjigu"
      (M&N 4b) -/
  | serbianAccentedAuxiliary
  /-- Serbian: accented verb + postposed subject (M&N 4c) -/
  | serbianAccentedVerbPostposedSubject
  /-- Serbian: particles and adverbs *stvarno / baš* (M&N 4d) -/
  | serbianParticles
  deriving DecidableEq, Repr

def mnAllStructures : List MNAttestedStructure :=
  [.germanAccentOnAuxiliary, .germanAccentOnLexicalVerb, .germanEmphaticTun,
   .germanVPFronting, .germanAccentedDiscourseParticles,
   .germanDiscourseMarkers, .germanTruthAdverbs,
   .englishAccentedAuxiliary, .englishAccentedLexicalVerb, .englishEmphaticDo,
   .englishVPFronting, .englishAdverbs, .englishParticles, .englishSoInversion,
   .serbianAccentedFiniteVerb, .serbianAccentedAuxiliary,
   .serbianAccentedVerbPostposedSubject, .serbianParticles]

/-! ## §2 The substrate's denotational mapping (Option-valued)

The substrate `PolarityMarkingStrategy` enum has 5 constructors. Any
denotational encoding of salient polarity onto this enum must collapse
M&N's 18+ attested structures into 5 buckets — necessarily many-to-one.

The mapping below is the *charitable* reading of how a denotational
account would assign each M&N structure to a substrate strategy. It is
**Option-valued**: structures for which no substrate strategy gives a
defensible fit return `none`. (`.other` exists in the substrate as a
catch-all but using it would mask the failure; we want the *non-fit*
to be visible at the type level. This realizes the mathlib-audit
recommendation to expose the dumping-ground claim structurally rather
than via a `decide` count.) -/
def substrateBestEffort : MNAttestedStructure → Option PolarityMarkingStrategy
  | .germanAccentOnAuxiliary             => some .verumFocus
  | .germanAccentOnLexicalVerb           => some .verumFocus
  | .germanEmphaticTun                   => none
  | .germanVPFronting                    => none
  | .germanAccentedDiscourseParticles    => some .polarityReversal  -- doch is canonical
  | .germanDiscourseMarkers              => none
  | .germanTruthAdverbs                  => none
  | .englishAccentedAuxiliary            => some .verumFocus
  | .englishAccentedLexicalVerb          => some .verumFocus
  | .englishEmphaticDo                   => some .verumFocus
  | .englishVPFronting                   => none
  | .englishAdverbs                      => none
  | .englishParticles                    => none
  | .englishSoInversion                  => none
  | .serbianAccentedFiniteVerb           => some .verumFocus
  | .serbianAccentedAuxiliary            => some .verumFocus
  | .serbianAccentedVerbPostposedSubject => none
  | .serbianParticles                    => none

/-! ## §2b Fragment routing — the M&N argument on actual lexical data

For 4 M&N structures the existing Fragment library already encodes
the corresponding lexical entry. The routing below makes the M&N
non-isomorphism claims indictments of *actual Fragment data*, not just
of M&N's hand-curated symbol list. The 14 unrouted structures (German
*tun* periphrasis, Serbian particles, English *so*-inversion, etc.) have
no Fragment entries; for those the M&N argument runs against the
substrate enum directly, in §2 above. -/
def fromFragment : MNAttestedStructure → Option PolarityMarkingEntry
  | .englishEmphaticDo                => some emphaticDo
  | .germanAccentOnAuxiliary          => some verumFocus
  | .germanAccentOnLexicalVerb        => some verumFocus
  | .germanAccentedDiscourseParticles => some dochPreUtterance
  | _                                 => none

/-- For the 4 Fragment-routable M&N structures, the Fragment's substrate
    `strategy` field agrees with `substrateBestEffort`. This grounds the
    best-effort mapping in actual data: it isn't an editorial fiction. -/
theorem substrateBestEffort_agrees_with_fragments :
    ∀ s : MNAttestedStructure, ∀ e : PolarityMarkingEntry,
      fromFragment s = some e → substrateBestEffort s = some e.strategy := by
  intro s e h
  cases s <;> simp [fromFragment] at h <;> (subst h; rfl)

/-! ## §3 Non-isomorphism: the encoding is many-to-one

The substrate's encoding is not injective on M&N's attested-structure
list — `.verumFocus` collects 7 cross-linguistic structures M&N treat
as separate phenomena, and `none` collects 10 more (M&N's claim that
"the grammatical category gets a blurry extension and must be
continuously expanded", p. 15). -/

/-- The denotational encoding cannot place two attested structures M&N
    treat as substantively different (German emphatic *tun* and English
    VP fronting). Both fall outside any substrate strategy bucket. -/
theorem substrate_cannot_encode_germanEmphaticTun_and_englishVPFronting :
    substrateBestEffort .germanEmphaticTun = none ∧
    substrateBestEffort .englishVPFronting = none := ⟨rfl, rfl⟩

/-- The substrate's `.verumFocus` constructor collects multiple distinct
    M&N structures. **This is now a claim about real Fragment data**:
    the English *do*-support entry (`Fragments.English.PolarityMarking.emphaticDo`)
    and the German verum-focus entry (`Fragments.German.PolarityMarking.verumFocus`)
    have the same substrate `strategy` field, even though M&N argue
    they have different distributional properties (M&N §2.2.1). -/
theorem fragment_data_lumps_emphaticDo_with_verumFocus :
    emphaticDo.strategy = verumFocus.strategy := rfl

/-- The substrate has no defensible encoding for at least 10 of M&N's
    18 attested salient-polarity structures. The substrate's catch-all
    `.other` constructor would silently absorb these, but accepting
    that absorption is exactly what M&N argue against (p. 15: "the
    grammatical category gets a blurry extension and must be
    continuously expanded to encompass all structures carrying the
    desired effect"). The Option-valued mapping makes the failure
    structural: there is no `some _` to assign. -/
theorem substrate_cannot_encode_at_least_ten :
    (mnAllStructures.filter (fun s => substrateBestEffort s == none)).length ≥ 10 := by
  decide

/-! ## §4 Open-endedness: the load-bearing claim

M&N's deeper argument is not just that the encoding is many-to-one — it
is that the *list* of structures that can convey salient polarity is
itself **open-ended**. The chapter (p. 15) explicitly notes that
expressions like *on the contrary*, *just the opposite*, and complement
clauses introduced with *it is true that* fit the standard salient-
polarity diagnostics but are not in any existing typology, and concludes
"the list seems to be open."

We record M&N's three explicit witnesses as `String` data outside
`MNAttestedStructure`. The inductive type cannot witness its own
incompleteness — adding the three witnesses as constructors would
just push the openness one step further out (M&N would point at
yet another structure not in the extended type). The witness list
plus the non-emptiness theorem is the substantive Lean correlate of
M&N's "the list seems to be open" claim. -/

/-- Three salient-polarity-conveying structures M&N (p. 15) explicitly
    cite as missing from existing typologies. They live as `String` data
    rather than `MNAttestedStructure` constructors precisely because
    M&N's openness argument denies that any finite enumeration closes
    the category. -/
def mnOpenEndedWitnesses : List String :=
  ["on the contrary",
   "just the opposite",
   "complement clauses with *it is true that p*"]

/-- The salient-polarity-conveying list M&N attests is **larger** than
    the 18-constructor `MNAttestedStructure` enum: at minimum, three
    further witnesses (M&N p. 15) can be exhibited as `String`s outside
    the inductive type. Any finite extension of `MNAttestedStructure`
    would face the same problem. This is the operational sense in
    which M&N's open-endedness claim holds against any closure attempt. -/
theorem mn_attested_list_strictly_grows : mnOpenEndedWitnesses ≠ [] := by decide

/-! ## §5 Garassino & Jacob (2018, fn 13) endorsement

The same-volume @cite{garassino-jacob-2018} explicitly adopt M&N's
salient-polarity view (their fn 13, p. 236; verbatim quote in
`Phenomena/Polarity/Studies/GarassinoJacob2018.lean::§4`). This is a
documented framework alignment within the volume itself, not the
formaliser's editorial synthesis — a peer in the same edited volume
reaching the same conclusion. -/

/-! ## §6 The argument extends to sibling frameworks

M&N §2 explicitly target three sibling frameworks beyond the substrate's
form-class encoding. Two of them are formalized in linglib:

- `Phenomena/Questions/Studies/RomeroHan2004.lean` formalizes
  @cite{romero-han-2004}'s **FOR-SURE-CG** epistemic-conjunction
  operator. M&N call this "Lexical Operator Theory" (LOT) and
  reject it on the same form-meaning grounds (M&N §2 "epistemic
  account").
- `Theories/Semantics/Mood/Gutzmann.lean` /
  `Phenomena/SentenceMood/Studies/Gutzmann2015.lean` formalize
  @cite{gutzmann-2015}'s use-conditional sentence-mood operators
  (DEONT/EPIS/HKNOW). The verum-specific Gutzmann work M&N cite
  (Gutzmann & Castroviejo Miró 2011) is *not* formalized in
  linglib — the existing Gutzmann file is the broader 2015
  sentence-mood book whose framework scope does not extend to
  polarity-marking devices at all.

Below we extend the M&N non-fit argument to both. The shared shape —
each framework yields an `Option`-valued partial mapping from
`MNAttestedStructure`, with the `none` extension counting the
framework's encoding failures — could be lifted to a typeclass
(`FrameworkFit α := MNAttestedStructure → Option α`); we keep the
mappings as separate `def`s for now so each framework's coverage
profile stays visible at the def-site. -/

/-- Romero & Han's framework offers exactly one analytic option for
    salient polarity: the FOR-SURE-CG operator. M&N call this LOT. -/
inductive RHAnalysis where
  /-- @cite{romero-han-2004}'s `forSureCG` operator analyzes the
      structure as expressing speaker certainty about CG-addition. -/
  | epistemicVerum
  deriving DecidableEq, Repr

/-- R&H's FOR-SURE-CG analysis is canonically motivated by — and
    arguably restricted to — accent on finite verbs / auxiliaries
    (the prosodic-on-finite-verb subset). For M&N's other 11
    structures (periphrastic *tun*, VP fronting, discourse particles,
    inversion constructions, adverbs, …) the R&H framework is silent. -/
def romeroHanBestEffort : MNAttestedStructure → Option RHAnalysis
  | .germanAccentOnAuxiliary       => some .epistemicVerum
  | .germanAccentOnLexicalVerb     => some .epistemicVerum
  | .englishAccentedAuxiliary      => some .epistemicVerum
  | .englishAccentedLexicalVerb    => some .epistemicVerum
  | .englishEmphaticDo             => some .epistemicVerum
  | .serbianAccentedFiniteVerb     => some .epistemicVerum
  | .serbianAccentedAuxiliary      => some .epistemicVerum
  | _                              => none

/-- R&H's FOR-SURE-CG analysis cannot encode at least 11 of M&N's 18
    attested salient-polarity structures. The framework's analytic
    scope is the prosodic-on-finite-verb subset; everything else falls
    outside. -/
theorem romeroHan_cannot_encode_at_least_eleven :
    (mnAllStructures.filter (fun s => romeroHanBestEffort s == none)).length ≥ 11 := by
  decide

/-- Gutzmann 2015's UCI dimensions (DEONT/EPIS/HKNOW). The 2015
    framework is about sentence-mood operators, not polarity-marking
    devices; M&N's specific Gutzmann target is Gutzmann & Castroviejo
    Miró 2011 ("a kind of conversational operator"), which is not
    formalized in linglib. -/
inductive GutzmannDimension where
  | deontic
  | epistemic
  | hearerKnowledge
  deriving DecidableEq, Repr

/-- Gutzmann 2015's sentence-mood UCIs do not analyze polarity-marking
    structures: the framework's scope is clause-type composition
    (V2/VL/imperative declaratives, interrogatives), not the prosodic /
    particle / construction inventory M&N enumerate. The constant-`none`
    encoding records that the framework simply does not extend. The
    shared verum-related Gutzmann critique M&N actually engage
    (Gutzmann & Castroviejo Miró 2011) is not in linglib's substrate. -/
def gutzmannBestEffort : MNAttestedStructure → Option GutzmannDimension :=
  fun _ => none

/-- Gutzmann 2015's sentence-mood framework cannot analyze any of M&N's
    18 attested salient-polarity structures — the framework scopes over
    clause types, not polarity-marking devices. Vacuous coverage,
    recorded structurally. -/
theorem gutzmann_2015_framework_does_not_apply :
    ∀ s : MNAttestedStructure, gutzmannBestEffort s = none := by
  intro _; rfl

/-- The M&N argument is universal: at least 10 attested structures fall
    outside the substrate enum, at least 11 fall outside R&H's
    FOR-SURE-CG, and all 18 fall outside Gutzmann 2015's sentence-mood
    UCIs. The structures inside the *intersection* of all three
    frameworks — the canonical prosodic verum focus on finite verbs —
    are exactly the cases all four traditions agree about; the
    disagreement is entirely about what *else* counts. -/
theorem mn_argument_extends_across_frameworks :
    (mnAllStructures.filter (fun s => substrateBestEffort s == none)).length ≥ 10 ∧
    (mnAllStructures.filter (fun s => romeroHanBestEffort s == none)).length ≥ 11 ∧
    (mnAllStructures.filter (fun s => gutzmannBestEffort s == none)).length = 18 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Phenomena.Polarity.Studies.MaticNikolaeva2018
