import Linglib.Theories.Syntax.ArgumentStructure.Alternation
import Linglib.Theories.Semantics.Causation.Morphological
import Linglib.Phenomena.ArgumentStructure.VoiceSystem
import Linglib.Theories.Syntax.Minimalist.Applicative

/-!
# Creissels (2025): Transitivity, Valency, and Voice
@cite{creissels-2025}

Formalization of key results from @cite{creissels-2025}, a comprehensive
typological reference on transitivity, valency, and voice across the world's
languages. The book proposes a unified framework based on:

- **TR-roles** (A, P, S, X): constructional categories defined by coding
  properties relative to prototypical transitive verbs (§1.3.3)
- **Nucleativization/denucleativization**: the two fundamental operations
  underlying all voice alternations (§8.1.3)
- **Alignment and the Obligatory Coding Principle**: A-alignment vs P-alignment
  as the fundamental typological parameter (§1.3.4)
- **Voice marker polysemy**: systematic cross-linguistic co-expression patterns
  where the same morpheme marks multiple voice alternation types (§8.2)

This study file bridges @cite{creissels-2025}'s framework (formalized in
`Core/Alternation.lean`) to existing linglib infrastructure:

- `MorphologicalCausation.lean`: causativization and decausativization
- `Phenomena/ArgumentStructure/VoiceSystem.lean`: pivot-based voice system typology
- `Minimalism/Applicative.lean`: Pylkkänen's high/low applicatives
- `Core/RootDimensions.lean`: Levin's diathesis alternation diagnostics
-/

namespace Creissels2025

open Syntax.ArgumentStructure.Alternation
open Semantics.Causation.Morphological
  (IntransitivizationType CausativeComplexity CausativeConstruction
   CausativizabilityData)
open Interfaces (VoiceSystemProfile VoiceSystemSymmetry VoiceEntry PivotTarget)

-- ════════════════════════════════════════════════════
-- § 1. Bridge: Decausativization ↔ IntransitivizationType
-- ════════════════════════════════════════════════════

/-! §8.3.1.2: "Decausativization suppresses the referent
of the initial A from participant structure and converts the initial P into
the S term of an intransitive construction."

This corresponds to `IntransitivizationType.anticausative` in linglib's
existing causation typology. Creissels prefers "decausativization" because
the prefix *de-* transparently marks removal of the causation component,
while "anticausative" misleadingly suggests a parallel with "antipassive"
that doesn't hold (§8.3.1.2). -/

/-- Decausativization suppresses A from participant structure — same
    structural effect as anticausative intransitivization. -/
theorem decausativization_matches_anticausative :
    decausativization.fateOfA = .suppressed ∧
    IntransitivizationType.anticausative.isBieventive = false :=
  ⟨rfl, rfl⟩

/-- Reflexive intransitivization is NOT decausativization: the causer is
    coidentified with the causee (bieventive), not removed. In Creissels'
    terms, reflexive intransitives are a different structural operation. -/
theorem reflexive_not_decausativization :
    IntransitivizationType.reflexive.isBieventive = true ∧
    decausativization.involvesCumulation = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Bridge: Causativization ↔ CausativeConstruction
-- ════════════════════════════════════════════════════

/-! §8.3.1.1 defines causativization as "the
nucleativization of a participant (the causer) that instigates the event
denoted by the initial construction or controls its realization."

The existing `CausativeConstruction` type adds the fine structure:
morphological complexity (lexical/morphological/periphrastic) and
semantic mediation (direct/indirect). Creissels' causativization is the
structural frame; linglib's `CausativeConstruction` fills in the parameters.

§12.1.4 gives the tripartite morphological distinction:
- Synthetic (affixal): most common cross-linguistically
- Analytic (auxiliary + nonfinite): European passives, 'make/let' causatives
- Periphrastic (light verb): borderline voice/biclausal -/

/-- Every `CausativeConstruction` instantiates the structural pattern of
    causativization: a new participant (causer) in A role. -/
theorem causative_construction_nucleativizes :
    causativization.involvesNucleativization = true ∧
    causativization.newParticipant = some .A :=
  ⟨rfl, rfl⟩

/-- Causativization and decausativization are inverse operations on the
    causality chain (§8.3.1): causativization adds a causer in A,
    decausativization suppresses A from participant structure. -/
theorem causativization_decausativization_inverse :
    causativization.newParticipant = some .A ∧
    decausativization.fateOfA = .suppressed :=
  ⟨rfl, rfl⟩

/-- The three morphological complexity levels of @cite{comrie-1989} map to
    §12.1.4's synthetic/analytic/periphrastic
    distinction. Lexical = synthetic (most compact). -/
theorem complexity_alignment :
    (CausativeComplexity.lexical < CausativeComplexity.morphological) ∧
    (CausativeComplexity.morphological < CausativeComplexity.periphrastic) :=
  ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Bridge: Applicativization ↔ Pylkkänen's ApplType
-- ════════════════════════════════════════════════════

/-! §14.1 distinguishes three varieties:
- P-applicativization (§14.1.1): applied phrase fills P role
- D-applicativization (§14.1.3): applied phrase is dative oblique
- X-applicativization (§14.1.4): applied phrase is ordinary oblique

Pylkkänen (2008)'s high/low distinction is orthogonal to Creissels' P/D/X
distinction. High applicatives introduce event-level participants
(benefactives); low applicatives introduce transfer participants (recipients,
sources). In Creissels' terms, high applicatives tend to produce
P-applicativization (the applied phrase gets P coding), while low
applicatives tend to produce D-applicativization (dative coding). -/

/-- All three applicativization types nucleativize a new participant. -/
theorem all_applicativizations_nucleativize :
    pApplicativization.involvesNucleativization = true ∧
    dApplicativization.involvesNucleativization = true ∧
    xApplicativization.involvesNucleativization = true :=
  ⟨rfl, rfl, rfl⟩

/-- P-applicativization is valency-increasing (the applied phrase becomes
    a new core term). -/
theorem p_applicativization_valency_increasing :
    pApplicativization.isValencyIncreasing = true := rfl

-- ════════════════════════════════════════════════════
-- § 4. Bridge: Symmetrical Voices ↔ VoiceSystemProfile
-- ════════════════════════════════════════════════════

/-! §8.5: symmetrical voice systems are those in which
verb morphology marks the selection of a participant as the privileged
syntactic term (pivot) WITHOUT AFFECTING TRANSITIVITY. This is a fundamentally
different type of voice system from A/P-prominent systems (§1.3.3.3).

The existing `VoiceSystemProfile` captures this with `.symmetrical` vs
`.asymmetrical`, but doesn't encode Creissels' key insight: symmetrical
voices are NOT instances of passivization, causativization, etc. — they are
a distinct type that doesn't fit the nucleativization/denucleativization
framework at all.

Example Toba Batak voice profiles illustrate that symmetrical systems
have 2+ voices with equal morphological complexity (equipollent marking). -/

/-- An A/P-prominent transitive construction (e.g., English active/passive)
    maps to an asymmetrical voice system. -/
def englishVoiceSystem : VoiceSystemProfile :=
  { language := "English"
  , voices := [ { name := "active", promotes := .agent }
              , { name := "passive", promotes := .patient } ]
  , symmetry := .asymmetrical }

theorem english_is_asymmetrical :
    englishVoiceSystem.symmetry = .asymmetrical := rfl

theorem english_is_active_passive :
    englishVoiceSystem.isActivePassive := by decide

-- ════════════════════════════════════════════════════
-- § 5. Passivization vs Decausativization (§8.3.1.2 vs §8.3.2.1)
-- ════════════════════════════════════════════════════

/-! §8.3.2.1: "The maintenance of the initial A in
participant structure is essential to distinguish passivization from
decausativization."

Both operations denucleativize A and yield an intransitive construction,
but they differ in whether A remains in participant structure:
- **Passivization**: A is `.denucleativized` (oblique or unexpressed, but
  still semantically present — can appear as oblique agent phrase)
- **Decausativization**: A is `.suppressed` (removed from participant
  structure entirely — no agent phrase possible)

This distinction is now directly encoded in `ParticipantFate`. -/

/-- Passivization and decausativization are structurally distinct despite
    both yielding intransitive constructions: they differ in whether A
    remains in participant structure. -/
theorem passive_decausative_distinct :
    passivization.fateOfA ≠ decausativization.fateOfA := by
  simp [passivization, decausativization]

-- ════════════════════════════════════════════════════
-- § 6. Bridge: Passivization ↔ Antipassivization structural symmetry
-- ════════════════════════════════════════════════════

/-! §8.3.2: passivization, antipassivization, and
S-denucleativization form a natural class — all three denucleativize a core
term without nucleativizing any other participant, and the denucleativized
participant remains in participant structure. They differ only in which
core term is targeted:
- Passivization: A denucleativized
- Antipassivization: P denucleativized
- S-denucleativization: S denucleativized -/

/-- Passivization and antipassivization are structural mirrors: both
    denucleativize exactly one core term without nucleativizing any other. -/
theorem passive_antipassive_mirror :
    passivization.isValencyDecreasing = true ∧
    antipassivization.isValencyDecreasing = true ∧
    passivization.fateOfA = .denucleativized ∧
    antipassivization.fateOfP = .denucleativized :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- S-denucleativization completes the paradigm: all three target different
    TR-roles. -/
theorem denucleativization_paradigm :
    passivization.fateOfA = .denucleativized ∧
    antipassivization.fateOfP = .denucleativized ∧
    sDenucleativization.fateOfS = .denucleativized :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Bridge: Reflexivization/Reciprocalization ↔ existing data
-- ════════════════════════════════════════════════════

/-! §8.3.3: reflexivization and reciprocalization
cumulate two participant roles (A and P) into a single participant (S).
They differ in whether S refers to a single individual (reflexive) or
a group whose members mutually fill both roles (reciprocal).

Both are classified as valency-decreasing in Creissels' framework —
the derived construction has fewer core terms. The existing WALS Ch 106 data
in `Typology.lean` captures the cross-linguistic formal relationship between
reflexive and reciprocal markers. -/

/-- Reflexivization and reciprocalization have identical structural effects
    on core terms — they differ only in the semantic interpretation of
    cumulation (individual vs. group). -/
theorem refl_recip_same_structure :
    reflexivization.fateOfA = reciprocalization.fateOfA ∧
    reflexivization.fateOfP = reciprocalization.fateOfP ∧
    reflexivization.involvesCumulation = true ∧
    reciprocalization.involvesCumulation = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Voice Marker Stacking (§8.4)
-- ════════════════════════════════════════════════════

/-! §8.4: voice markers can be stacked compositionally.
Example from Tswana (§8.4.1, ex. 38):
- write-CAUS-APPL: causativize then applicativize
- write-APPL-PASS: applicativize then passivize
- write-CAUS-PASS: causativize then passivize
- write-CAUS-APPL-PASS: all three composed

The compositional stacking means we can model multi-marker verb forms as
sequential application of `ValencyAlternation` operations. -/

/-- A stacked voice derivation: a sequence of alternations applied in order. -/
abbrev VoiceStack := List ValencyAlternation

/-- Example Tswana stacking patterns (§8.4.1). -/
def tswana_caus_appl : VoiceStack := [causativization, pApplicativization]
def tswana_appl_pass : VoiceStack := [pApplicativization, passivization]
def tswana_caus_pass : VoiceStack := [causativization, passivization]
def tswana_caus_appl_pass : VoiceStack :=
  [causativization, pApplicativization, passivization]

-- ════════════════════════════════════════════════════
-- § 9. Portative Derivation (§8.3.7)
-- ════════════════════════════════════════════════════

/-! §8.3.7 identifies portative derivation as a distinct
voice alternation type that cannot be reduced to either causativization or
applicativization, although it shares features with both:

- Like causativization: the derived construction has a prototypical agent in A
- Like applicativization: a new participant is introduced as P
- Unlike either: the A of the derived construction corresponds to the S of the
  initial construction (not a new causer), and the new P is the carried entity

Example: Caddo *Ci-ʔa=d(ih)-ʔaʔ* 'I will go' → *Ci-ni-ʔa=d(ih)-ʔaʔ*
'I will take it' (§8.3.7, ex. 33). -/

/-- Portative derivation is valency-increasing but structurally distinct from
    both causativization and applicativization. -/
theorem portative_distinct_from_causativization :
    portativeDerivation.isValencyIncreasing = true ∧
    portativeDerivation.initialTransitive = some false ∧
    -- Causativization adds A; portative adds P (different new role)
    causativization.newParticipant = some .A ∧
    portativeDerivation.newParticipant = some .P :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. Alignment Profiles (§1.3.4)
-- ════════════════════════════════════════════════════

/-! §1.3.4.2: most languages have a clear preference
for either A-alignment (S codes like A) or P-alignment (S codes like P).
Some languages (e.g., Basque, Georgian) show split-S patterns. -/

def russian : ObligatoryCodingProfile :=
  { language := "Russian"
  , defaultAlignment := .A_alignment }

def avar : ObligatoryCodingProfile :=
  { language := "Avar"
  , defaultAlignment := .P_alignment }

def basque : ObligatoryCodingProfile :=
  { language := "Basque"
  , defaultAlignment := .P_alignment
  , violationsExist := true
  , splitS := true }

def mandinka : ObligatoryCodingProfile :=
  { language := "Mandinka"
  , defaultAlignment := .A_alignment
  , violationsExist := true }

-- ════════════════════════════════════════════════════
-- § 11. Russian -sja polysemy (§8.2, ex. 8)
-- ════════════════════════════════════════════════════

/-! The Russian verbal suffix *-sja / -s'* is a paradigmatic example of voice
marker polysemy. It marks at least four different voice alternation types:

(8a) reflexivization: *Ivan mo-et-sja* 'Ivan washes (himself)'
(8b) reciprocalization: *Paren' i devuška celuj-ut-sja* 'The boy and the girl were kissing'
(8c) passivization: *Lekcija čita-et-sja professor-om* 'The course is delivered by the professor'
(8d) antipassivization: *Sobaka kusa-et-sja* 'The dog bites (people)' -/

def russian_sja : VoiceMarkerProfile :=
  { language := "Russian"
  , marker := "-sja / -s'"
  , alternations := [reflexivization, reciprocalization,
                      passivization, antipassivization] }

/-- Russian *-sja* is polysemous across four voice alternation types. -/
theorem russian_sja_polysemy :
    russian_sja.alternations.length = 4 := rfl

-- ════════════════════════════════════════════════════
-- § 12. Tswana -el polysemy (§8.2)
-- ════════════════════════════════════════════════════

/-! The Tswana voice suffix *-el* (traditionally called "applicative") marks
both P-nucleativization (applicativization) and A-nucleativization of
obliques (non-causative A/S-nucleativization). Example:

(12) *Ki-tłàà-kwál-él-á Kítsó lò-kwâːlɔ̀* 'I'll write the letter to/for Kitso'
     (P-nucleativization of recipient)
(13b) *Nàmà í-ʃáb-él-à bò-χɔ́ːbɛ̀* 'Meat gives flavor to the porridge'
     (A-nucleativization of instrument → A) -/

def tswana_el : VoiceMarkerProfile :=
  { language := "Tswana"
  , marker := "-el"
  , alternations := [pApplicativization, asNucleativizationOfObliques] }

-- ════════════════════════════════════════════════════
-- § 13. Causativizability and Voice Alternations
-- ════════════════════════════════════════════════════

/-! Ch 12 discusses restrictions on causativization.
@cite{krejci-2012}'s hierarchy (already formalized in
`MorphologicalCausation.lean`) describes which verb classes can be
causativized: unaccusatives > middles/ingestives > unergatives >
simple transitives. This hierarchy predicts that causativization
of transitive verbs (§12.3.5) often requires antipassivization to
create an intransitive base first. -/

/-- Causativization of transitives may require prior antipassivization
    to create an intransitive base (§12.3.5). This is an instance of
    compositional voice marker stacking. -/
def causativization_via_antipassive : VoiceStack :=
  [antipassivization, causativization]

end Creissels2025
