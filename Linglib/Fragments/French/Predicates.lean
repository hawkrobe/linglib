import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# French Predicate Lexicon Fragment
@cite{song-1996}

French causative predicates, centered on the *faire* causative.
@cite{song-1996} classifies *faire* as a COMPACT causative with free morpheme
realization: the causative and effect verbs form a tight syntactic unit
despite being separate words.

"Je ferai lire le livre à Nicole" = "I will make Nicole read the book"
(faire + infinitive = single predicate for case marking purposes)

-/

namespace Fragments.French.Predicates

open Core.Verbs
open NadathurLauer2020.Builder (CausativeBuilder)
open Semantics.Lexical.Verb.EntailmentProfile
  (EntailmentProfile kickSubjectProfile seeSubjectProfile runSubjectProfile)

/-- French verb entry: extends VerbCore with French inflectional paradigm. -/
structure FrenchVerbEntry extends VerbCore where
  /-- 3sg present -/
  form3sg : String
  /-- Passé simple -/
  formPasse : String
  /-- Participe passé -/
  formPartPasse : String
  /-- Participe présent -/
  formPartPres : String
  deriving Repr, BEq

/-- faire — COMPACT causative (free morpheme). -/
def faire : FrenchVerbEntry where
  form := "faire"
  form3sg := "fait"
  formPasse := "fit"
  formPartPasse := "fait"
  formPartPres := "faisant"
  complementType := .smallClause
  controlType := .objectControl
  causativeBuilder := some .make

/-- laisser — permissive causative ("let"). -/
def laisser : FrenchVerbEntry where
  form := "laisser"
  form3sg := "laisse"
  formPasse := "laissa"
  formPartPasse := "laissé"
  formPartPres := "laissant"
  complementType := .smallClause
  controlType := .objectControl
  causativeBuilder := some .enable

/-- French *faire* uses `.make` builder. -/
theorem faire_is_make :
    faire.causativeBuilder = some .make := rfl

/-- French *laisser* uses `.enable` builder (permissive). -/
theorem laisser_is_enable :
    laisser.causativeBuilder = some .enable := rfl

/-- *faire* and *laisser* have different builders (make vs enable). -/
theorem faire_laisser_different :
    faire.causativeBuilder ≠ laisser.causativeBuilder := by decide

-- ============================================================================
-- § Change-of-state verbs: property-change anticausative profile
-- @cite{martin-schaefer-kastner-2025} experiments 1a & 1b
-- ============================================================================

/-- Entailment profile for anticausative subjects of property-change verbs.
    Shared by both limited-control (*rougir*, *brunir*) and in-control
    (*durcir*, *refroidir*) property-change verbs — the control
    classification reflects world knowledge, not lexical entailments.
    Sentience is false: non-sentient subjects are possible (*le mur
    rougit* 'the wall reddened'). Stationary is false: Dowty's
    `stationary` is relative to another participant, not applicable
    to sole arguments of intransitive verbs. -/
def cosSubjectProfile : EntailmentProfile where
  volition := false; sentience := false; causation := false
  movement := false; independentExistence := true
  changeOfState := true; incrementalTheme := false
  causallyAffected := true; stationary := false
  dependentExistence := false

/-- brunir — 'turn brown(er)'. Limited-control ±se AC-verb. -/
def brunir : FrenchVerbEntry where
  form := "brunir"; form3sg := "brunit"; formPasse := "brunit"
  formPartPasse := "bruni"; formPartPres := "brunissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

/-- noircir — 'blacken, darken'. Limited-control ±se AC-verb. -/
def noircir : FrenchVerbEntry where
  form := "noircir"; form3sg := "noircit"; formPasse := "noircit"
  formPartPasse := "noirci"; formPartPres := "noircissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

/-- pâlir — 'get pale'. Limited-control ±se AC-verb. -/
def palir : FrenchVerbEntry where
  form := "pâlir"; form3sg := "pâlit"; formPasse := "pâlit"
  formPartPasse := "pâli"; formPartPres := "pâlissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

/-- rajeunir — 'get young(er), rejuvenate'. Limited-control ±se AC-verb. -/
def rajeunir : FrenchVerbEntry where
  form := "rajeunir"; form3sg := "rajeunit"; formPasse := "rajeunit"
  formPartPasse := "rajeuni"; formPartPres := "rajeunissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

/-- rougir — 'redden, blush'. Limited-control ±se AC-verb. -/
def rougir : FrenchVerbEntry where
  form := "rougir"; form3sg := "rougit"; formPasse := "rougit"
  formPartPasse := "rougi"; formPartPres := "rougissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

-- ============================================================================
-- § Change-of-state verbs: motion anticausative profile
-- @cite{martin-schaefer-kastner-2025} experiment 1b (motion verbs)
-- ============================================================================

/-- Entailment profile for anticausative subjects of motion/posture
    change-of-state verbs: like `cosSubjectProfile` but with `movement`
    (the change involves physical displacement or posture reconfiguration).
    Used for *approcher* 'get close' and *plier* 'bend', both in-control
    verbs. Non-motion in-control verbs (*durcir*, *refroidir*) use
    `cosSubjectProfile` instead. -/
def motionCosSubjectProfile : EntailmentProfile where
  volition := false; sentience := false; causation := false
  movement := true; independentExistence := true
  changeOfState := true; incrementalTheme := false
  causallyAffected := true; stationary := false
  dependentExistence := false

/-- approcher (de) — 'get close(r) to'. In-control ±se AC-verb (motion). -/
def approcher : FrenchVerbEntry where
  form := "approcher"; form3sg := "approche"; formPasse := "approcha"
  formPartPasse := "approché"; formPartPres := "approchant"
  complementType := .none
  subjectEntailments := some motionCosSubjectProfile

/-- durcir — 'harden'. In-control ±se AC-verb (property-change). -/
def durcir : FrenchVerbEntry where
  form := "durcir"; form3sg := "durcit"; formPasse := "durcit"
  formPartPasse := "durci"; formPartPres := "durcissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

/-- plier — 'bend, fold'. In-control ±se AC-verb (motion). -/
def plier : FrenchVerbEntry where
  form := "plier"; form3sg := "plie"; formPasse := "plia"
  formPartPasse := "plié"; formPartPres := "pliant"
  complementType := .none
  subjectEntailments := some motionCosSubjectProfile

/-- radoucir — 'get soft(er)'. In-control ±se AC-verb (property-change). -/
def radoucir : FrenchVerbEntry where
  form := "radoucir"; form3sg := "radoucit"; formPasse := "radoucit"
  formPartPasse := "radouci"; formPartPres := "radoucissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

/-- refroidir — 'get cold(er)'. In-control ±se AC-verb (property-change). -/
def refroidir : FrenchVerbEntry where
  form := "refroidir"; form3sg := "refroidit"; formPasse := "refroidit"
  formPartPasse := "refroidi"; formPartPres := "refroidissant"
  complementType := .none
  subjectEntailments := some cosSubjectProfile

-- ============================================================================
-- § Passive Agent preposition selection: par vs de
-- @cite{staps-rooryck-2024}
-- ============================================================================

/-- Prototypical transitive subject: V+S+C+M+IE (5 P-Ag).
    Identical to @cite{dowty-1991}'s canonical agent (`kickSubjectProfile`).
    Used for *laver*, *écrire*, *construire*, *tuer*, etc. -/
abbrev protoTransSubjectProfile := kickSubjectProfile

/-- Prototypical transitive object: CoS+CA (2 P-Pat).
    Used for *laver*, *tuer*, etc. -/
def protoTransObjectProfile : EntailmentProfile where
  volition := false; sentience := false; causation := false
  movement := false; independentExistence := false
  changeOfState := true; incrementalTheme := false
  causallyAffected := true; stationary := false
  dependentExistence := false

/-- Experiencer subject: S+IE (2 P-Ag).
    Identical to @cite{dowty-1991}'s perception profile (`seeSubjectProfile`).
    Used for *aimer*, *adorer*, *respecter*. -/
abbrev experiencerSubjectProfile := seeSubjectProfile

/-- Minimal participant: IE only (1 P-Ag, 0 P-Pat).
    The participant exists independently of the event but has no
    agentive involvement (no volition, causation, movement) and no
    patientive involvement (no change, affectedness).

    Used for:
    - Objects of psych verbs (*aimer*, *adorer*, *respecter*): the stimulus
    - Objects of accompaniment/following verbs (*accompagner*, *suivre*,
      *précéder*): the co-participant
    - Subjects of stative positional verbs (*précéder*, stative *suivre*):
      the entity in a fixed relation -/
def minimalParticipantProfile : EntailmentProfile where
  volition := false; sentience := false; causation := false
  movement := false; independentExistence := true
  changeOfState := false; incrementalTheme := false
  causallyAffected := false; stationary := false
  dependentExistence := false

/-- Stative positional subjects have the same profile as minimal
    participants: IE only. The subject of *précéder* and the object
    of *aimer* occupy the same proto-role space — both have no
    agentive or patientive entailments beyond independent existence. -/
abbrev stativePositionalSubjectProfile := minimalParticipantProfile

/-- Dynamic motion subject: V+S+M+IE (4 P-Ag).
    Identical to `runSubjectProfile` — volitional self-propelled motion
    without causing a change in another participant.
    Used for dynamic *suivre* ('follow' with volition). -/
abbrev dynamicFollowSubjectProfile := runSubjectProfile

/-- Accompany subject: S+M+IE (3 P-Ag).
    Used for *accompagner*. Movement without obligatory volition:
    the accompaniment may or may not be volitional (parents
    accompanying children may be passive observers). -/
def accompanySubjectProfile : EntailmentProfile where
  volition := false; sentience := true; causation := false
  movement := true; independentExistence := true
  changeOfState := false; incrementalTheme := false
  causallyAffected := false; stationary := false
  dependentExistence := false

-- laver — 'wash'. Prototypical transitive: par only.
def laver : FrenchVerbEntry where
  form := "laver"; form3sg := "lave"; formPasse := "lava"
  formPartPasse := "lavé"; formPartPres := "lavant"
  complementType := .np
  subjectEntailments := some protoTransSubjectProfile
  objectEntailments := some protoTransObjectProfile
  vendlerClass := some .accomplishment

-- écrire — 'write'. Creation verb: par only.
def ecrire : FrenchVerbEntry where
  form := "écrire"; form3sg := "écrit"; formPasse := "écrivit"
  formPartPasse := "écrit"; formPartPres := "écrivant"
  complementType := .np
  subjectEntailments := some protoTransSubjectProfile
  objectEntailments := some { protoTransObjectProfile with
    incrementalTheme := true, dependentExistence := true }
  vendlerClass := some .accomplishment

-- construire — 'build'. Creation verb: par only.
def construire : FrenchVerbEntry where
  form := "construire"; form3sg := "construit"; formPasse := "construisit"
  formPartPasse := "construit"; formPartPres := "construisant"
  complementType := .np
  subjectEntailments := some protoTransSubjectProfile
  objectEntailments := some { protoTransObjectProfile with
    incrementalTheme := true, dependentExistence := true }
  vendlerClass := some .accomplishment

-- tuer — 'kill'. Highly transitive: par only.
def tuer : FrenchVerbEntry where
  form := "tuer"; form3sg := "tue"; formPasse := "tua"
  formPartPasse := "tué"; formPartPres := "tuant"
  complementType := .np
  subjectEntailments := some protoTransSubjectProfile
  objectEntailments := some { protoTransObjectProfile with
    dependentExistence := true }
  vendlerClass := some .achievement

-- aimer — 'love'. Psych stative: both par and de.
def aimer : FrenchVerbEntry where
  form := "aimer"; form3sg := "aime"; formPasse := "aima"
  formPartPasse := "aimé"; formPartPres := "aimant"
  complementType := .np
  subjectEntailments := some experiencerSubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .state

-- adorer — 'adore, worship'. Psych stative: both par and de.
def adorer : FrenchVerbEntry where
  form := "adorer"; form3sg := "adore"; formPasse := "adora"
  formPartPasse := "adoré"; formPartPres := "adorant"
  complementType := .np
  subjectEntailments := some experiencerSubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .state

-- respecter — 'respect'. Psych stative: both par and de.
def respecter : FrenchVerbEntry where
  form := "respecter"; form3sg := "respecte"; formPasse := "respecta"
  formPartPasse := "respecté"; formPartPres := "respectant"
  complementType := .np
  subjectEntailments := some experiencerSubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .state

-- accompagner — 'accompany'. Par/de depending on involvement.
def accompagner : FrenchVerbEntry where
  form := "accompagner"; form3sg := "accompagne"; formPasse := "accompagna"
  formPartPasse := "accompagné"; formPartPres := "accompagnant"
  complementType := .np
  subjectEntailments := some accompanySubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .activity

-- suivre — 'follow' (dynamic reading). Par preferred.
def suivreDyn : FrenchVerbEntry where
  form := "suivre"; form3sg := "suit"; formPasse := "suivit"
  formPartPasse := "suivi"; formPartPres := "suivant"
  complementType := .np
  senseTag := .default
  subjectEntailments := some dynamicFollowSubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .activity

-- suivre — 'follow' (stative/positional reading). De preferred.
def suivreStat : FrenchVerbEntry where
  form := "suivre"; form3sg := "suit"; formPasse := "suivit"
  formPartPasse := "suivi"; formPartPres := "suivant"
  complementType := .np
  senseTag := .stative
  subjectEntailments := some stativePositionalSubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .state

-- précéder — 'precede'. Stative: de preferred.
def preceder : FrenchVerbEntry where
  form := "précéder"; form3sg := "précède"; formPasse := "précéda"
  formPartPasse := "précédé"; formPartPres := "précédant"
  complementType := .np
  subjectEntailments := some stativePositionalSubjectProfile
  objectEntailments := some minimalParticipantProfile
  vendlerClass := some .state

-- abandonner — 'abandon'. Telic: par; atelic: par/de.
def abandonner : FrenchVerbEntry where
  form := "abandonner"; form3sg := "abandonne"; formPasse := "abandonna"
  formPartPasse := "abandonné"; formPartPres := "abandonnant"
  complementType := .np
  subjectEntailments := some protoTransSubjectProfile
  objectEntailments := some protoTransObjectProfile
  vendlerClass := some .accomplishment

-- délaisser — 'abandon, neglect'. Similar to abandonner.
def delaisser : FrenchVerbEntry where
  form := "délaisser"; form3sg := "délaisse"; formPasse := "délaissa"
  formPartPasse := "délaissé"; formPartPres := "délaissant"
  complementType := .np
  subjectEntailments := some protoTransSubjectProfile
  objectEntailments := some protoTransObjectProfile
  vendlerClass := some .accomplishment

def allVerbs : List FrenchVerbEntry :=
  [faire, laisser,
   brunir, noircir, palir, rajeunir, rougir,
   approcher, durcir, plier, radoucir, refroidir,
   laver, ecrire, construire, tuer,
   aimer, adorer, respecter, accompagner,
   suivreDyn, suivreStat, preceder,
   abandonner, delaisser]

def lookup (form : String) : Option FrenchVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.French.Predicates
