import Linglib.Syntax.Reciprocal

/-!
# Siloni (2012): Reciprocal verbs and symmetry

Beyond periphrastic reciprocals (*each other*), languages have reciprocal
*verbs* — predicates that express reciprocity without an anaphoric object.
[siloni-2012] (building on [siloni-2008]) splits them by where
reciprocalization applies — the `Formation` parameter of
`Syntax/Reciprocal.lean`, an instance of [reinhart-siloni-2005]'s lex-syn
parameter. **Lexical** formation (Hebrew *hitnašek*, English intransitive
*kiss*) bundles θ-roles in the lexicon and yields symmetric verbs whose
reciprocity is a singular atomic event; **syntactic** formation (French
*s'embrasser*, Czech *se políbit*) is a productive clitic operation whose
reciprocity accumulates sub-events. Nine empirical properties cluster along
this divide (`PropertyCluster`, with the two predicted clusters complementary
on every property, `properties_complementary`). The paper's sample is
recorded per-language (`hebrew` … `bulgarian`): lexical in Hebrew, Russian,
Hungarian, and English; syntactic in French, Italian, Spanish, Romanian,
Czech, Serbo-Croatian, and Bulgarian (fn. 13 extends the split family-wide:
East Slavic lexical, West and South Slavic syntactic).

Both verb types disallow the "I" reading of embedded reciprocals
([higginbotham-1980]) because both associate the subject with two θ-roles,
while the two types fail different necessary conditions along the way; the
derivation chain (§3.5 → §4.3) culminates in `no_I_reading_either_formation`.
-/

namespace Siloni2012

open Reciprocal

/-! ### Three-way reciprocal classification (§2.4) -/

/-- The three classes of reciprocal constructions (§2.4). -/
inductive Construction where
  /-- Reciprocal anaphor in object position (*each other*, *l'un l'autre*);
      the subject bears one θ-role. -/
  | periphrastic
  /-- Reciprocal verb formed in the lexicon by θ-role bundling (§4.1); the
      subject bears a complex [Agent-Theme] role and the verb is symmetric. -/
  | lexicalVerb
  /-- Reciprocal verb formed in the syntax by a clitic (§4.2); the subject
      bears two θ-roles via parasitic assignment. -/
  | syntacticVerb
  deriving DecidableEq, Repr

/-- The reciprocal-verb class determined by formation locus. -/
def Construction.ofFormation : Formation → Construction
  | .lexical   => .lexicalVerb
  | .syntactic => .syntacticVerb

/-- Number of θ-roles associated with the subject: one for periphrastic
    reciprocals (Theme sits on the anaphoric object), two for both verb
    types (bundled or parasitic). -/
def Construction.subjectRoleCount : Construction → Nat
  | .periphrastic  => 1
  | .lexicalVerb   => 2
  | .syntacticVerb => 2

/-- Whether reciprocity is built from sub-events (§2.2): true except for
    lexical reciprocal verbs, whose singular atomic event has no accessible
    sub-events. -/
def Construction.allowsSubEventReading : Construction → Bool
  | .periphrastic  => true
  | .lexicalVerb   => false
  | .syntacticVerb => true

/-! ### The nine-property cluster (§§2–7) -/

/-- The nine empirical properties that distinguish lexical from syntactic
    reciprocal verbs, in the order of the paper's concluding enumeration.
    Each `Bool` records whether the property holds for a formation type. -/
structure PropertyCluster where
  /-- (i) Reciprocity involves a singular atomic event: count adverbials
      (*five times*) yield N mutual events, not 2N directional sub-events
      (§2.2–2.3). -/
  singularEvent : Bool
  /-- (ii) The reciprocalization operation applies productively to
      transitive verbs (§3.5, §5). -/
  productive : Bool
  /-- (iii) ECM reciprocal verbs are possible — reciprocalization spans a
      clause boundary (§5.2). -/
  ecmReciprocals : Bool
  /-- (iv) Can be formed from a frozen lexical entry, one without a
      transitive alternate in the vocabulary (§5.3). -/
  frozenInput : Bool
  /-- (v) Can undergo semantic drift — acquire a meaning not shared by the
      transitive alternate (§5.3). -/
  semanticDrift : Bool
  /-- (vi) Can head phrasal idioms unavailable for the transitive
      alternate (§5.3). -/
  phrasalIdioms : Bool
  /-- (vii) Can retain an accusative argument when reciprocalization
      suppresses the dative rather than the accusative (§5.1). -/
  retainsAccOnDativeSuppression : Bool
  /-- (viii) Can derive reciprocal event nominals (§6). Exception: Czech
      reciprocal event nominals exist despite the syntactic setting —
      Czech nominalization is a lexical operation ([hron-2005]), and the
      nominals arise by syntactic reciprocalization of the transitive
      nominal, available because the Czech clitic, unlike the strictly
      verbal Romance clitic, attaches to nouns. -/
  eventNominals : Bool
  /-- (ix) Allows the discontinuous reciprocal construction — subject plus
      comitative *with*-phrase (§7). Language-level availability; English
      *kiss* and *hug* resist it despite the lexical setting (fn. 32). -/
  discontinuous : Bool
  deriving DecidableEq, Repr

/-- Pointwise complement of a property cluster. -/
def PropertyCluster.compl (p : PropertyCluster) : PropertyCluster where
  singularEvent := !p.singularEvent
  productive := !p.productive
  ecmReciprocals := !p.ecmReciprocals
  frozenInput := !p.frozenInput
  semanticDrift := !p.semanticDrift
  phrasalIdioms := !p.phrasalIdioms
  retainsAccOnDativeSuppression := !p.retainsAccOnDativeSuppression
  eventNominals := !p.eventNominals
  discontinuous := !p.discontinuous

/-- Predicted cluster for lexically-formed reciprocal verbs: a closed class
    of symmetric verbs that can be frozen or drifted, head idioms, derive
    event nominals, and license discontinuity, but form no ECM reciprocals
    and retain no accusative on dative suppression. Property (ix) calls the
    substrate classifier `Formation.allowsDiscontinuous`, so the two agree
    by construction. -/
def lexicalProperties : PropertyCluster where
  singularEvent := true
  productive := false
  ecmReciprocals := false
  frozenInput := true
  semanticDrift := true
  phrasalIdioms := true
  retainsAccOnDativeSuppression := false
  eventNominals := true
  discontinuous := Formation.lexical.allowsDiscontinuous

/-- Predicted cluster for syntactically-formed reciprocal verbs: productive,
    with sub-events, ECM reciprocals, and accusative retention, but no
    frozen inputs, drift, idioms, event nominals, or discontinuity. -/
def syntacticProperties : PropertyCluster where
  singularEvent := false
  productive := true
  ecmReciprocals := true
  frozenInput := false
  semanticDrift := false
  phrasalIdioms := false
  retainsAccOnDativeSuppression := true
  eventNominals := false
  discontinuous := Formation.syntactic.allowsDiscontinuous

/-- The predicted property cluster of a formation locus. [nordlinger-2023]'s
    later per-language profiles check the discontinuity prediction against
    attested judgments in `Studies/Nordlinger2023.lean`. -/
def predictedProperties : Formation → PropertyCluster
  | .lexical   => lexicalProperties
  | .syntactic => syntacticProperties

/-- The two predicted clusters are complementary on every property. -/
theorem properties_complementary :
    syntacticProperties = lexicalProperties.compl := rfl

/-! ### Symmetric verbs (§2.3, §4.1) -/

/-- Lexically-formed reciprocal verbs are symmetric verbs: both participants
    are identically involved in a singular atomic event (§2.3), as with
    intransitive *kiss* and *collide*. -/
def IsSymmetricVerb (f : Formation) : Prop := f = .lexical

instance : DecidablePred IsSymmetricVerb :=
  fun f => inferInstanceAs (Decidable (f = .lexical))

/-- A formation yields symmetric verbs iff it predicts a singular event. -/
theorem symmetric_iff_singular (f : Formation) :
    IsSymmetricVerb f ↔ (predictedProperties f).singularEvent := by
  cases f <;> decide

/-! ### The "I" reading (§2.1, §4.3)

In "John and Paul said they defeated each other in the final"
([higginbotham-1980]), the "I" reading — John said he defeated Paul, and
Paul said he defeated John — requires both that the embedded verb allow
the sub-event reading and that its subject bear exactly one θ-role
(§4.3, p. 287). -/

/-- The "I" reading requires both sub-event availability and a sole θ-role
    on the subject (§4.3). -/
def Construction.allowsIReading (c : Construction) : Bool :=
  c.allowsSubEventReading && (c.subjectRoleCount == 1)

/-- The "I" reading is available only in the periphrastic class; syntactic
    reciprocal verbs have sub-events yet still lack it, because the
    sole-role requirement fails. -/
theorem I_reading_iff_periphrastic (c : Construction) :
    c.allowsIReading ↔ c = .periphrastic := by
  cases c <;> decide

/-! ### Cross-linguistic sample (§2.4, §5, §7) -/

/-- The formation locus of a language's reciprocal verbs. -/
structure LangRecipVerb where
  language : String
  iso : String
  formation : Formation
  deriving DecidableEq, Repr

def hebrew    : LangRecipVerb := ⟨"Hebrew",    "heb", .lexical⟩
def russian   : LangRecipVerb := ⟨"Russian",   "rus", .lexical⟩
def hungarian : LangRecipVerb := ⟨"Hungarian", "hun", .lexical⟩

/-- English reciprocal verbs (intransitive *kiss*, *meet*, *collide*) are
    lexicon-formed symmetric verbs, though the language's primary reciprocal
    strategy is the periphrastic *each other* (hence the strategy-level
    classification in `Studies/Nordlinger2023.lean` differs); fn. 32 notes
    that *kiss* and *hug* nonetheless resist the discontinuous
    construction. -/
def english : LangRecipVerb := ⟨"English", "eng", .lexical⟩

def french        : LangRecipVerb := ⟨"French",         "fra", .syntactic⟩
def italian       : LangRecipVerb := ⟨"Italian",        "ita", .syntactic⟩
def spanish       : LangRecipVerb := ⟨"Spanish",        "spa", .syntactic⟩
def czech         : LangRecipVerb := ⟨"Czech",          "ces", .syntactic⟩
def romanian      : LangRecipVerb := ⟨"Romanian",       "ron", .syntactic⟩
def serboCroatian : LangRecipVerb := ⟨"Serbo-Croatian", "hbs", .syntactic⟩
def bulgarian     : LangRecipVerb := ⟨"Bulgarian",      "bul", .syntactic⟩

/-- The paper's language sample. The abstract announces ten languages;
    eleven are named with data across the paper, so all are recorded. -/
def sample : List LangRecipVerb :=
  [hebrew, russian, hungarian, english,
   french, italian, spanish, czech, romanian, serboCroatian, bulgarian]

/-! ### Derivation: formation locus → no "I" reading (§3.5 → §4.3)

Generalization (29): "Plural events are not part of the lexicon's
inventory." Lexical reciprocalization therefore yields symmetric verbs
with no sub-events, failing the first condition on the "I" reading;
syntactic reciprocal verbs have sub-events but fail the sole-role
condition. Both paths end at `no_I_reading_either_formation`. -/

/-- Both reciprocal verb types associate the subject with two θ-roles:
    bundling in the lexicon (§4.1), parasitic assignment in the syntax
    (§4.2). -/
theorem recip_verb_dual_role (f : Formation) :
    (Construction.ofFormation f).subjectRoleCount = 2 := by
  cases f <;> rfl

/-- Singular-event verbs lack the sub-event reading (§2.2–2.3). -/
theorem singular_event_no_subevents (f : Formation)
    (h : (predictedProperties f).singularEvent = true) :
    (Construction.ofFormation f).allowsSubEventReading = false := by
  cases f
  · rfl
  · exact nomatch h

/-- Sub-event availability is necessary for the "I" reading (§4.3). -/
theorem subevents_necessary_for_I (c : Construction)
    (h : c.allowsSubEventReading = false) :
    c.allowsIReading = false := by
  simp [Construction.allowsIReading, h]

/-- A sole θ-role on the subject is necessary for the "I" reading (§4.3). -/
theorem sole_role_necessary_for_I (c : Construction)
    (h : c.subjectRoleCount ≠ 1) :
    c.allowsIReading = false := by
  cases c
  exacts [absurd rfl h, rfl, rfl]

/-- Lexical derivation: singular event → no sub-events → no "I" reading
    (§3.5 → §2.2 → §4.3). -/
theorem lexical_no_I_reading :
    (Construction.ofFormation .lexical).allowsIReading = false :=
  subevents_necessary_for_I _ (singular_event_no_subevents _ rfl)

/-- Syntactic derivation: dual role → no "I" reading (§4.2 → §4.3), despite
    the sub-event reading being available. -/
theorem syntactic_no_I_reading :
    (Construction.ofFormation .syntactic).allowsIReading = false :=
  sole_role_necessary_for_I _ (by decide)

/-- Neither reciprocal verb type allows the "I" reading. -/
theorem no_I_reading_either_formation (f : Formation) :
    (Construction.ofFormation f).allowsIReading = false := by
  cases f
  exacts [lexical_no_I_reading, syntactic_no_I_reading]

end Siloni2012
