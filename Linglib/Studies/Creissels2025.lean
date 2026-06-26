import Linglib.Syntax.ArgumentStructure.Alternation
import Linglib.Semantics.Causation.Morphological
import Linglib.Syntax.Voice.Basic
import Linglib.Syntax.Minimalist.Verbal.Applicative
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Creissels (2025): Transitivity, Valency, and Voice
[creissels-2025]

Formalization of key results from [creissels-2025], a comprehensive
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

This study file bridges [creissels-2025]'s framework (formalized in
`Syntax/ArgumentStructure/Alternation.lean`) to existing linglib infrastructure:

- `Semantics/Causation/Morphological.lean`: causativization and decausativization
- `Typology/VoiceSystem.lean`: pivot-based voice system typology
- `Syntax/Minimalist/Applicative.lean`: Pylkkänen's high/low applicatives
-/

namespace Creissels2025

open Syntax.ArgumentStructure.Alternation
open Causation.Morphological
  (IntransitivizationType CausativeComplexity CausativeConstruction
   CausativizabilityData)
open Voice (VoiceSystemSymmetry VoiceEntry PivotTarget)

/-! ### Bridge: Decausativization ↔ IntransitivizationType -/

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

/-! ### Bridge: Causativization ↔ CausativeConstruction -/

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

/-- The three morphological complexity levels of [comrie-1989] map to
    §12.1.4's synthetic/analytic/periphrastic
    distinction. Lexical = synthetic (most compact). -/
theorem complexity_alignment :
    (CausativeComplexity.lexical < CausativeComplexity.morphological) ∧
    (CausativeComplexity.morphological < CausativeComplexity.periphrastic) :=
  ⟨by decide, by decide⟩

/-! ### Bridge: Applicativization ↔ Pylkkänen's ApplType -/

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

/-! ### Bridge: symmetrical voices ↔ the `Voice` substrate -/

/-! §8.5: symmetrical voice systems are those in which
verb morphology marks the selection of a participant as the privileged
syntactic term (pivot) WITHOUT AFFECTING TRANSITIVITY. This is a fundamentally
different type of voice system from A/P-prominent systems (§1.3.3.3).

The `Voice` substrate's `VoiceSystemSymmetry` captures this with `.symmetrical`
vs `.asymmetrical`, but doesn't encode Creissels' key insight: symmetrical
voices are NOT instances of passivization, causativization, etc. — they are
a distinct type that doesn't fit the nucleativization/denucleativization
framework at all.

Example Toba Batak voice profiles illustrate that symmetrical systems
have 2+ voices with equal morphological complexity (equipollent marking). -/

/-- An A/P-prominent transitive construction (e.g., English active/passive)
    is an asymmetrical voice system. -/
def englishVoices : List VoiceEntry :=
  [ { name := "active", promotes := .agent }
  , { name := "passive", promotes := .patient } ]

def englishSymmetry : VoiceSystemSymmetry := .asymmetrical

theorem english_is_asymmetrical : englishSymmetry = .asymmetrical := rfl

theorem english_is_active_passive : Voice.isActivePassive englishVoices := by decide

/-! ### Passivization vs Decausativization (§8.3.1.2 vs §8.3.2.1) -/

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

/-! ### Bridge: Passivization ↔ Antipassivization structural symmetry -/

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

/-! ### Bridge: Reflexivization/Reciprocalization ↔ existing data -/

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

/-! ### Voice Marker Stacking (§8.4) -/

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

/-! ### Portative Derivation (§8.3.7) -/

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

/-! ### Alignment Profiles (§1.3.4) -/

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

/-! ### Russian -sja polysemy (§1.2, ex. 8) -/

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

/-! ### Tswana -el polysemy (§8.2) -/

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

/-! ### Causativizability and Voice Alternations -/

/-! Ch 12 discusses restrictions on causativization.
[krejci-2012]'s hierarchy (already formalized in
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

/-! ### Cross-linguistic voice distribution (Bahrt 2021) -/

/-! §8.3.8 reports [bahrt-2021]'s survey of synthetic voice marking across
222 languages from all genera. -/

/-- Cross-linguistic prevalence of a voice alternation type: the share of
    languages with synthetic marking for it. -/
structure VoiceDistribution where
  alternation : ValencyAlternation
  /-- Fraction of languages with synthetic marking for this alternation. -/
  share : ℚ
  deriving Repr

/-- [bahrt-2021] distribution data, cited in §8.3.8: the fraction of the
    222 languages (all genera) with synthetic marking for each voice alternation
    type. Note (§8.3.8): Bahrt's "applicativization" conflates applicativization
    with non-causative A/S-nucleativization, so that row is broader than
    Creissels's `pApplicativization`. -/
def bahrt2021Distribution : List VoiceDistribution :=
  [ { alternation := causativization,       share := 739/1000 }
  , { alternation := reciprocalization,     share := 604/1000 }
  , { alternation := pApplicativization,    share := 459/1000 }  -- Bahrt's broader "applicativization" (see note)
  , { alternation := reflexivization,       share := 419/1000 }
  , { alternation := decausativization,     share := 360/1000 }
  , { alternation := passivization,         share := 360/1000 }
  , { alternation := antipassivization,     share := 185/1000 } ]

/-- Causativization is the most common voice alternation type
    cross-linguistically ([bahrt-2021]). -/
theorem causativization_most_common :
    (bahrt2021Distribution.head?.map (·.alternation.name)) =
    some "causativization" := rfl

/-! ### Compositional denotation of voice stacking (§8.4) -/

/-! §8.4: voice markers stack, and a combination "operates on its valency
properties exactly as it could operate on the valency of an underived verb form"
— compositional stacking (§8.4.1). We model an alternation as a *word* over
atomic coding-frame edits (the nucleativization/denucleativization atoms of
§8.1.3), composition as the free-monoid product, and meaning as a denotation
into partial transformations of coding frames. Two `MonoidHom`s — `denote` and
`valencyDelta` — make stacking and the valency grading hold by construction.

End-roles (the S→P of causativization, P→S of passivization) are *derived* by
`normalizeFrame` from the construction's transitivity, not stipulated — faithful
to §8.1.3 (whose only atoms are nucleativization/denucleativization; the role
changes are coding consequences, cf. footnote 5 §8.3.2.1).

This layer currently has a single consumer (this study), so per the project's
graduation discipline it lives here; the `FrameMap` partial-transformation
monoid (a Kleisli/`Function.End` analogue) and the `denote`/`valencyDelta`
apparatus would hoist to `Core/` and `Alternation.lean` once a second study
consumes them. -/

namespace Stacking

open FreeMonoid (lift of)

/-- A term's coding status in a construction (a *state*; `ParticipantFate` is the
    *transition*, derived below via `fateOf`). -/
inductive Coding
  | core (r : TRRole)
  | oblique
  | suppressed
  deriving DecidableEq

/-- A coding-frame entry: a stable identity (tracked through a derivation) and
    its current status. -/
structure CodedTerm where
  id : Nat
  coding : Coding
  deriving DecidableEq

/-- A coding frame (§1.3.3): the participants and their statuses. -/
abbrev CodingFrame := List CodedTerm

def coreCount (f : CodingFrame) : Nat :=
  f.countP (fun t => t.coding matches .core _)

/-- Recompute a term's role from transitivity: the sole core term is S; a
    `core S` alongside other cores becomes P (a transitive clause has A and P,
    an intransitive clause has S). -/
def rerole (cc : Nat) : Coding → Coding
  | .core r => if cc = 1 then .core .S else (match r with | .S => .core .P | _ => .core r)
  | c => c

/-- Normalize end-roles after an edit — this *derives* the S↔P relabellings a
    `relabel` atom would otherwise stipulate. -/
def normalizeFrame (f : CodingFrame) : CodingFrame :=
  let cc := coreCount f
  f.map (fun t => ⟨t.id, rerole cc t.coding⟩)

def freshId (f : CodingFrame) : Nat := f.foldl (fun m t => Nat.max m (t.id + 1)) 0

def setFirstCore (r : TRRole) (c : Coding) : CodingFrame → Option CodingFrame
  | [] => none
  | t :: ts =>
    if t.coding = .core r then some (⟨t.id, c⟩ :: ts)
    else (setFirstCore r c ts).map (t :: ·)

def removeFirstCore (r : TRRole) : CodingFrame → Option CodingFrame
  | [] => none
  | t :: ts =>
    if t.coding = .core r then some ts
    else (removeFirstCore r ts).map (t :: ·)

/-- Some core term in the frame bears role `r`. -/
def HasCore (r : TRRole) (f : CodingFrame) : Prop := ∃ t ∈ f, t.coding = .core r

instance (r : TRRole) (f : CodingFrame) : Decidable (HasCore r f) :=
  inferInstanceAs (Decidable (∃ t ∈ f, t.coding = .core r))

/-- The atomic voice operations: Creissels's nucleativization /
    denucleativization (§8.1.3) plus cumulation (reflexivization, §8.3.3). -/
inductive Atom
  | nucleativize (target : TRRole)  -- a non-core participant becomes core   (+1)
  | denucleativize (role : TRRole)  -- core role → oblique (kept)             (−1)
  | suppress (role : TRRole)        -- core role → suppressed (removed)       (−1)
  | cumulate (r1 r2 : TRRole)       -- merge two cores into one               (−1)
  deriving DecidableEq

/-- An alternation as a word over atoms; composition = the free-monoid product
    (= voice-marker stacking, §8.4). -/
abbrev Word := FreeMonoid Atom

/-- Partial transformations of coding frames under Kleisli composition; `f * g`
    is "apply `f` then `g`" (the `MulOpposite` of `Function.End`-style order).
    Kept a `def` (not `abbrev`) so this `Monoid` is keyed on `FrameMap` and does
    not leak to bare `_ → Option _`. Not `PFun`: `Part ≠ Option`, and the demos
    below rely on `Option`'s decidability. -/
def FrameMap := CodingFrame → Option CodingFrame

instance : Monoid FrameMap where
  mul f g := fun x => (f x).bind g
  one := fun x => some x
  mul_assoc f g h := by
    funext x
    show ((f x).bind g).bind h = (f x).bind (fun y => (g y).bind h)
    cases f x <;> rfl
  one_mul f := by funext x; rfl
  mul_one f := by
    funext x
    show (f x).bind (fun y => some y) = f x
    cases f x <;> rfl

def atomDenote : Atom → FrameMap
  | .nucleativize target => fun f => some (normalizeFrame (f ++ [⟨freshId f, .core target⟩]))
  | .denucleativize role => fun f => (setFirstCore role .oblique f).map normalizeFrame
  | .suppress role => fun f => (setFirstCore role .suppressed f).map normalizeFrame
  | .cumulate r1 r2 => fun f =>
      if HasCore r1 f then (removeFirstCore r2 f).map normalizeFrame else none

def atomDelta : Atom → ℤ
  | .nucleativize _ => 1
  | .denucleativize _ => -1
  | .suppress _ => -1
  | .cumulate _ _ => -1

/-- Denotation of a word as a partial coding-frame transformation. A `MonoidHom`,
    so `map_mul` gives compositional stacking (§8.4.1). -/
def denote : Word →* FrameMap := lift atomDenote

/-- The valency grading: net change in number of core terms. A `MonoidHom` into
    `Multiplicative ℤ`, so stacking *adds* deltas. -/
def valencyDelta : Word →* Multiplicative ℤ :=
  lift (fun a => Multiplicative.ofAdd (atomDelta a))

def netValency (w : Word) : ℤ := Multiplicative.toAdd (valencyDelta w)

@[simp] theorem denote_of (a : Atom) : denote (of a) = atomDenote a := by
  simp only [denote, FreeMonoid.lift_eval_of]

@[simp] theorem valencyDelta_of (a : Atom) :
    valencyDelta (of a) = Multiplicative.ofAdd (atomDelta a) := by
  simp only [valencyDelta, FreeMonoid.lift_eval_of]

theorem netValency_mul (x y : Word) : netValency (x * y) = netValency x + netValency y := by
  simp only [netValency, map_mul]; rfl

/-- The substrate `ParticipantFate`, derived from a status transition — reusing
    the comparative-concept enum rather than forking a new one. -/
def fateOf : Coding → Coding → ParticipantFate
  | .core _, .core _ => .maintained
  | .core _, .oblique => .denucleativized
  | .core _, .suppressed => .suppressed
  | _, .core t => .nucleativized t
  | _, _ => .maintained

/-- Id of the participant currently in core role `r` (frame-relative). -/
def roleHolder (r : TRRole) : CodingFrame → Option Nat
  | [] => none
  | t :: ts => if t.coding = .core r then some t.id else roleHolder r ts

/-! ### Named alternations as words (roles fall out of `normalizeFrame`) -/

namespace Word
def causativization : Word := of (.nucleativize .A)
def passivization : Word := of (.denucleativize .A)
def decausativization : Word := of (.suppress .A)
def antipassivization : Word := of (.denucleativize .P)
def applicativization : Word := of (.nucleativize .P)
def reflexivization : Word := of (.cumulate .A .P)
/-- §12.3.5: causativizing a transitive verb requires antipassivizing first to
    create an intransitive base. -/
def causativizationViaAntipassive : Word := antipassivization * causativization
end Word

/-! ### Forward bridges: the denotation reproduces the comparative-concept records

These prove the word denotations *agree with* the schema-level
`ValencyAlternation` records (`Alternation.lean`) where both are defined — the
legitimate direction, not a redefinition of the schema. -/

theorem netValency_causativization : netValency Word.causativization = 1 := by
  simp only [Word.causativization, netValency, valencyDelta_of, atomDelta]; decide

theorem netValency_passivization : netValency Word.passivization = -1 := by
  simp only [Word.passivization, netValency, valencyDelta_of, atomDelta]; decide

-- agree with the records' valency direction:
theorem causativization_record_increases : causativization.isValencyIncreasing = true := rfl
theorem passivization_record_decreases : passivization.isValencyDecreasing = true := rfl

/-- Passivization obliquifies the initial A (kept in participant structure);
    P becomes S by normalization. -/
theorem denote_passivization :
    denote Word.passivization [⟨0, .core .A⟩, ⟨1, .core .P⟩]
      = some [⟨0, .oblique⟩, ⟨1, .core .S⟩] := by
  simp only [Word.passivization, denote_of]; decide

/-- Decausativization suppresses the initial A (removed). Same net valency as
    passive, different A-fate — the headline §8.3.1.2 / §8.3.2.1 distinction. -/
theorem denote_decausativization :
    denote Word.decausativization [⟨0, .core .A⟩, ⟨1, .core .P⟩]
      = some [⟨0, .suppressed⟩, ⟨1, .core .S⟩] := by
  simp only [Word.decausativization, denote_of]; decide

-- the derived fates match the records' `fateOfA`:
theorem fate_passivization_agrees :
    fateOf (.core .A) .oblique = passivization.fateOfA := rfl
theorem fate_decausativization_agrees :
    fateOf (.core .A) .suppressed = decausativization.fateOfA := rfl

/-- Applicativization adds a new core P; on a transitive base this yields a
    double-P construction (§8.1.8) — no role relabelling required. -/
theorem denote_applicativization :
    denote Word.applicativization [⟨0, .core .A⟩, ⟨1, .core .P⟩]
      = some [⟨0, .core .A⟩, ⟨1, .core .P⟩, ⟨2, .core .P⟩] := by
  simp only [Word.applicativization, denote_of]; decide

/-- Reflexivization cumulates A and P into a single core term, which normalizes
    to S (§8.3.3). -/
theorem denote_reflexivization :
    denote Word.reflexivization [⟨0, .core .A⟩, ⟨1, .core .P⟩]
      = some [⟨0, .core .S⟩] := by
  simp only [Word.reflexivization, denote_of]; decide

/-! ### Real composition for voice stacking (§8.4) -/

/-- Stacking is genuine composition: a word product denotes the Kleisli
    composite of its parts (§8.4.1). This gives the denotational counterpart of
    the record-level, semantics-free `causativization_via_antipassive` (§13). -/
theorem denote_stack (x y : Word) (f : CodingFrame) :
    denote (x * y) f = (denote x f).bind (denote y) := by
  rw [map_mul]; rfl

/-- Under stacking, "the A" is frame-relative: after causativization of an
    intransitive, the participant in role A is the new causer (id 1), not the
    original (id 0, now P). So a fate must be read off the *current* frame's
    role-holder, not a frozen "initial A". -/
theorem caus_A_holder_is_causer :
    (denote Word.causativization [⟨0, .core .S⟩]).bind (roleHolder .A) = some 1 := by
  simp only [Word.causativization, denote_of]; decide

/-- §12.3.5: causativization via prior antipassivization is valency-neutral
    (antipassive −1 then causative +1), composed as one transformation. -/
theorem netValency_causativizationViaAntipassive :
    netValency Word.causativizationViaAntipassive = 0 := by
  show netValency (Word.antipassivization * Word.causativization) = 0
  rw [netValency_mul]
  simp only [Word.antipassivization, Word.causativization, netValency, valencyDelta_of, atomDelta]
  decide

end Stacking

end Creissels2025
