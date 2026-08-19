import Linglib.Syntax.Reciprocal
import Mathlib.Order.Irreducible

/-!
# Siloni (2012): Reciprocal verbs and symmetry

Beyond periphrastic reciprocals (*each other*), languages have reciprocal
*verbs* — predicates that express reciprocity without an anaphoric object.
[siloni-2012] (building on [siloni-2008]) splits them by where
reciprocalization applies — the `Formation` parameter of
`Syntax/Reciprocal.lean`, an instance of [reinhart-siloni-2005]'s lex-syn
parameter — and derives nine clustering properties from that split alone:
"the distinctions all follow from the fact that the two types of verbs are
formed in different components of the grammar."

The file formalizes the reduction, not just its output. A `Component`
records four architectural facts about a locus of application: whether
plural events are available (generalization (29) denies them to the
lexicon), whether the operation works over listed entries, whether it sees
the θ-roles of two distinct predicates, and whether it must reduce
accusative case ([reinhart-siloni-2005]). `Component.properties` computes
the nine-property cluster from these affordances; the paper's concluding
table is then a theorem (`predictedProperties_lexical`), and the perfect
complementarity of the two clusters follows from the components differing
on every affordance (`Component.lexicon_compl`) via a polarity-preserving
reduction (`Component.properties_compl`). The event-semantic content of
the singular-event column is order-theoretic: an atomic (sup-irreducible)
event admits no decomposition into directional sub-events
(`SubEventReading.not_supIrred`). Both verb types disallow the "I" reading
of embedded reciprocals ([higginbotham-1980]): reciprocalization cumulates
both core roles onto the subject (`Voice.reciprocalization`), and the two
types fail different necessary conditions along the way
(`no_I_reading_either_formation`). The paper's eleven-language sample is
recorded per-language (`hebrew` … `bulgarian`).
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

/-! ### The lex-syn architecture (§3.5, §§5–6) -/

/-- What a component of the grammar affords an arity operation applying
    there: the four architectural facts from which the nine properties of
    reciprocal verbs derive. -/
structure Component where
  /-- Plural events are available. Generalization (29) — "plural events are
      not part of the lexicon's inventory" — denies them to the lexicon
      (§3.5), so its outputs denote atomic events. -/
  pluralEvents : Bool
  /-- The operation works within the stored inventory: its inputs may be
      frozen entries, and its outputs are listed — so they can drift, head
      idioms, and feed lexical nominalization (§5.3, §6); listing also caps
      productivity. -/
  listedEntries : Bool
  /-- The θ-roles of two distinct predicates are visible, as in ECM
      configurations (§5.2); a lexical operation sees a single entry. -/
  spansPredicates : Bool
  /-- An arity operation here must reduce accusative case whichever
      argument it suppresses ([reinhart-siloni-2005]); the syntactic clitic
      instead absorbs the suppressed argument's own case (§5.1). -/
  reducesAccusative : Bool
  deriving DecidableEq, Repr

/-- Pointwise complement of a component's affordances. -/
def Component.compl (c : Component) : Component where
  pluralEvents := !c.pluralEvents
  listedEntries := !c.listedEntries
  spansPredicates := !c.spansPredicates
  reducesAccusative := !c.reducesAccusative

/-- The lexicon: listed entries and obligatory accusative reduction, but no
    plural events and no cross-predicate visibility. -/
def Component.lexicon : Component where
  pluralEvents := false
  listedEntries := true
  spansPredicates := false
  reducesAccusative := true

/-- The syntactic derivation: plural events and cross-predicate visibility,
    with a case-indiscriminate clitic and nothing listed. -/
def Component.derivation : Component where
  pluralEvents := true
  listedEntries := false
  spansPredicates := true
  reducesAccusative := false

/-- The two components differ on every affordance. -/
theorem Component.lexicon_compl :
    Component.lexicon.compl = Component.derivation := rfl

/-- The component where a construction's reciprocity is composed: in the
    lexicon only for lexical reciprocal verbs; periphrastic reciprocity is
    composed by the anaphor's plural operator in the syntax (§2.4). -/
def Construction.component : Construction → Component
  | .lexicalVerb => .lexicon
  | .periphrastic | .syntacticVerb => .derivation

open Voice in
/-- Number of θ-roles borne by the subject. Both verb types realize
    [creissels-2025]'s `Voice.reciprocalization`, which cumulates the two
    core roles onto the derived subject (bundling in the lexicon §4.1,
    parasitic assignment in the syntax §4.2); the periphrastic subject
    keeps the transitive frame's single external role. -/
def Construction.subjectRoleCount : Construction → Nat
  | .periphrastic => 1
  | .lexicalVerb | .syntacticVerb =>
      [reciprocalization.fateOfA, reciprocalization.fateOfP].count .cumulated

/-- Whether reciprocity is built from sub-events: plural events must be
    available where it is composed (§2.2, generalization (29)). -/
def Construction.allowsSubEventReading (k : Construction) : Bool :=
  k.component.pluralEvents

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
      comitative *with*-phrase (§7). A property of symmetric verbs (§7.5),
      with verb-level exceptions in both directions: English *kiss* and
      *hug* resist it (fn. 32), while listed lexical entries in
      syntax-setting languages (French *se battre* 'fight') allow it
      (§7.2). -/
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

/-- The property cluster an arity operation's outputs display, computed
    from the component's affordances: the paper's reduction of the nine
    properties to the locus of formation. -/
def Component.properties (c : Component) : PropertyCluster where
  singularEvent := !c.pluralEvents
  productive := !c.listedEntries
  ecmReciprocals := c.spansPredicates
  frozenInput := c.listedEntries
  semanticDrift := c.listedEntries
  phrasalIdioms := c.listedEntries
  retainsAccOnDativeSuppression := !c.reducesAccusative
  eventNominals := c.listedEntries
  discontinuous := !c.pluralEvents

/-- The reduction is polarity-preserving: complementary affordances yield
    complementary property clusters. -/
theorem Component.properties_compl (c : Component) :
    c.compl.properties = c.properties.compl := rfl

/-- The predicted property cluster of a formation locus. [nordlinger-2023]'s
    later per-language profiles check the discontinuity prediction against
    attested judgments in `Studies/Nordlinger2023.lean`. -/
def predictedProperties (f : Formation) : PropertyCluster :=
  (Construction.ofFormation f).component.properties

/-- The derived lexical cluster matches the paper's concluding table. -/
theorem predictedProperties_lexical :
    predictedProperties .lexical =
      { singularEvent := true, productive := false, ecmReciprocals := false,
        frozenInput := true, semanticDrift := true, phrasalIdioms := true,
        retainsAccOnDativeSuppression := false, eventNominals := true,
        discontinuous := true } := rfl

/-- The two predicted clusters are complementary on every property — by
    `Component.lexicon_compl` and `Component.properties_compl`. -/
theorem properties_complementary :
    predictedProperties .syntactic = (predictedProperties .lexical).compl := rfl

/-- The derived discontinuity prediction agrees with the substrate
    classifier `Formation.allowsDiscontinuous`. -/
theorem discontinuous_eq_allowsDiscontinuous (f : Formation) :
    (predictedProperties f).discontinuous = f.allowsDiscontinuous := by
  cases f <;> rfl

/-! ### Symmetric verbs (§2.3, §7.5) -/

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

/-- "The discontinuous construction is a property of symmetric verbs"
    (§7.5). -/
theorem discontinuous_iff_symmetric (f : Formation) :
    (predictedProperties f).discontinuous ↔ IsSymmetricVerb f := by
  cases f <;> decide

/-! ### Atomic events and the sub-event reading (§2.2–2.3, §3.5)

The event-semantic content of the singular-event column: generalization
(29) means lexicon-formed reciprocals denote atomic — sup-irreducible —
events, and such an event admits no decomposition into directional
sub-events; reciprocity composed in the syntax sums directional
sub-events, which license the reading when neither contains the other. -/

section Events

variable {α E : Type*} [SemilatticeSup E] {R : α → α → E → Prop} {x y : α}

/-- The sub-event reading of a reciprocal event (§2.2): the event
    decomposes into two proper parts, one realizing each direction. -/
def SubEventReading (R : α → α → E → Prop) (x y : α) (e : E) : Prop :=
  ∃ e₁ e₂, e₁ < e ∧ e₂ < e ∧ R x y e₁ ∧ R y x e₂ ∧ e = e₁ ⊔ e₂

/-- An event with the sub-event reading is not atomic: symmetric verbs,
    denoting sup-irreducible events, lack the reading (§2.2–2.3). -/
theorem SubEventReading.not_supIrred {e : E} :
    SubEventReading R x y e → ¬ SupIrred e :=
  fun ⟨_, _, h₁, h₂, _, _, he⟩ hs => (hs.2 he.symm).elim h₁.ne h₂.ne

/-- The sum of incomparable directional sub-events has the sub-event
    reading: reciprocity by accumulation (§4.2). -/
theorem subEventReading_sup {e₁ e₂ : E} (h₁ : ¬ e₂ ≤ e₁) (h₂ : ¬ e₁ ≤ e₂)
    (hxy : R x y e₁) (hyx : R y x e₂) : SubEventReading R x y (e₁ ⊔ e₂) :=
  ⟨e₁, e₂, left_lt_sup.2 h₁, right_lt_sup.2 h₂, hxy, hyx, rfl⟩

end Events

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

/-! ### Derivation: formation locus → no "I" reading (§3.5 → §4.3)

The lexical path fails the sub-event condition (generalization (29): no
plural events in the lexicon); the syntactic path fails the sole-role
condition (cumulation). Both end at `no_I_reading_either_formation`. -/

/-- Both reciprocal verb types associate the subject with two θ-roles:
    `Voice.reciprocalization` cumulates both core roles (§4.1, §4.2). -/
theorem recip_verb_dual_role (f : Formation) :
    (Construction.ofFormation f).subjectRoleCount = 2 := by
  cases f <;> rfl

/-- Singular-event verbs lack the sub-event reading: both are projections
    of the same affordance, `Component.pluralEvents` (§2.2–2.3). -/
theorem singular_event_no_subevents (f : Formation)
    (h : (predictedProperties f).singularEvent = true) :
    (Construction.ofFormation f).allowsSubEventReading = false := by
  simpa [predictedProperties, Component.properties,
    Construction.allowsSubEventReading] using h

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

end Siloni2012
