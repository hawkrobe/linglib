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
open Semantics.Lexical.Verb.EntailmentProfile (EntailmentProfile)

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

def allVerbs : List FrenchVerbEntry :=
  [faire, laisser,
   brunir, noircir, palir, rajeunir, rougir,
   approcher, durcir, plier, radoucir, refroidir]

def lookup (form : String) : Option FrenchVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.French.Predicates
