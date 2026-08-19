import Linglib.Syntax.Reciprocal
import Linglib.Semantics.ArgumentStructure.RoleList
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

The reciprocalization operation itself acts on argument structure:
`reciprocalize` takes a transitive `RoleList` and returns an intransitive
one whose subject bears the `bundle` of the two base profiles — the
pointwise join on `EntailmentProfile`, [reinhart-siloni-2005]'s complex
[θᵢ · θⱼ] role. The bundled subject retains the base subject's Proto-Agent
entailments and inherits the object's Proto-Patient entailments
(`pAgentDominates_bundle_left`, `pPatientDominates_bundle_right` — the
depictive and comparative-ellipsis diagnostics of §3.1–3.2), so it bears
entailments from both clusters (`reciprocalize_isComplexRole`). Since the
"I" reading of embedded reciprocals ([higginbotham-1980]) requires a
sub-event reading plus a sole-role subject, both verb types lack it for
*any* transitive base with an agentive subject and an affected object
(`I_reading_iff_periphrastic`), each failing a different condition.

The nine surface properties derive from four affordances of the locus of
application (`pluralEventsAvailable` per generalization (29),
`storesOutputs`, `spansPredicates`, `reducesAccusative`): the paper's
concluding table is a theorem (`predictedProperties_lexical`), as is the
perfect complementarity of the two clusters. The event-semantic content of
the singular-event column is order-theoretic: an atomic (sup-irreducible)
event admits no decomposition into directional sub-events
(`SubEventReading.not_supIrred`). The paper's eleven-language sample is
recorded per-language (`hebrew` … `bulgarian`).
-/

namespace Siloni2012

open Reciprocal ArgumentStructure

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

/-! ### The lex-syn architecture (§3.5, §§5–6)

Four affordances of a locus of application, each carrying one of the
paper's mechanisms; the nine surface properties are computed from them in
`predictedProperties`. -/

/-- Generalization (29): "plural events are not part of the lexicon's
    inventory" (§3.5) — sub-event accumulation is available only in the
    syntactic derivation. -/
def pluralEventsAvailable : Formation → Bool
  | .lexical   => false
  | .syntactic => true

/-- Whether the operation's outputs are stored entries. Applying within the
    inventory, the lexical operation may also take frozen entries as input;
    stored outputs can drift, head idioms, and feed lexical nominalization,
    and listing caps productivity (§5.3, §6). -/
def storesOutputs : Formation → Bool
  | .lexical   => true
  | .syntactic => false

/-- Whether the operation sees the θ-roles of two distinct predicates, as
    in ECM configurations (§5.2); the lexical operation manipulates a
    single entry. -/
def spansPredicates : Formation → Bool
  | .lexical   => false
  | .syntactic => true

/-- Whether the operation must reduce accusative case whichever argument it
    suppresses ([reinhart-siloni-2005]); the syntactic clitic instead
    absorbs the suppressed argument's own case (§5.1). -/
def reducesAccusative : Formation → Bool
  | .lexical   => true
  | .syntactic => false

/-- The locus where a construction's reciprocity is composed: in the
    lexicon only for lexical reciprocal verbs; periphrastic reciprocity is
    composed by the anaphor's plural operator in the syntax (§2.4). -/
def Construction.compositionLocus : Construction → Formation
  | .lexicalVerb => .lexical
  | .periphrastic | .syntacticVerb => .syntactic

/-- Whether reciprocity is built from sub-events: plural events must be
    available where it is composed (§2.2, generalization (29)). -/
def Construction.allowsSubEventReading (c : Construction) : Bool :=
  pluralEventsAvailable c.compositionLocus

theorem compositionLocus_ofFormation (f : Formation) :
    (Construction.ofFormation f).compositionLocus = f := by
  cases f <;> rfl

/-! ### θ-role bundling on argument structure (§4.1–4.2)

Reciprocalization eliminates the internal argument position and associates
its θ-role with the subject — bundling in the lexicon, parasitic
assignment in the syntax; the resulting role state is the same. On the
Dowty substrate this is the pointwise join of entailment profiles, applied
to a transitive `RoleList`. -/

section Bundling

variable (p q : EntailmentProfile) {r : RoleList} {o : EntailmentProfile}

/-- [reinhart-siloni-2005]'s bundling `[θᵢ · θⱼ]`: the complex role imposing
    both components' entailments — the pointwise join on the Boolean cube
    of proto-role features. -/
def bundle : EntailmentProfile where
  volition := p.volition || q.volition
  sentience := p.sentience || q.sentience
  causation := p.causation || q.causation
  movement := p.movement || q.movement
  independentExistence := p.independentExistence || q.independentExistence
  changeOfState := p.changeOfState || q.changeOfState
  incrementalTheme := p.incrementalTheme || q.incrementalTheme
  causallyAffected := p.causallyAffected || q.causallyAffected
  stationary := p.stationary || q.stationary
  dependentExistence := p.dependentExistence || q.dependentExistence

/-- The bundled role retains the first component's Proto-Agent entailments:
    the reciprocal subject is still agentive. -/
theorem pAgentDominates_bundle_left : PAgentDominates (bundle p q) p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [bundle, h]

/-- The bundled role inherits the second component's Proto-Patient
    entailments: the reciprocal subject bears the base object's theme
    entailments — Czech depictives (§3.1) and comparative ellipsis (§3.2). -/
theorem pPatientDominates_bundle_right : PPatientDominates (bundle p q) q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [bundle, h]

theorem pAgentScore_le_bundle : p.pAgentScore ≤ (bundle p q).pAgentScore := by
  have H : ∀ a b : Bool, a.toNat ≤ (a || b).toNat := by decide
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (H .. ) (H ..)) (H ..)) (H ..)) (H ..)

theorem pPatientScore_le_bundle : q.pPatientScore ≤ (bundle p q).pPatientScore := by
  have H : ∀ a b : Bool, b.toNat ≤ (a || b).toNat := by decide
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (H ..) (H ..)) (H ..)) (H ..)) (H ..)

/-- A complex role in [reinhart-siloni-2005]'s sense: entailments from both
    proto-role clusters. The "sole role requirement" on the "I" reading
    (§4.3) is the negation of this. -/
def IsComplexRole (p : EntailmentProfile) : Prop :=
  0 < p.pAgentScore ∧ 0 < p.pPatientScore

instance : DecidablePred IsComplexRole :=
  fun p => inferInstanceAs (Decidable (0 < p.pAgentScore ∧ 0 < p.pPatientScore))

/-- Bundling an agentive profile with an affected one yields a complex
    role. -/
theorem bundle_isComplexRole (ha : 0 < p.pAgentScore) (hp : 0 < q.pPatientScore) :
    IsComplexRole (bundle p q) :=
  ⟨ha.trans_le (pAgentScore_le_bundle p q), hp.trans_le (pPatientScore_le_bundle p q)⟩

/-- Reciprocalization on argument structure: the internal position is
    eliminated and its profile bundled onto the subject. Realizes
    [creissels-2025]'s `Voice.reciprocalization` coding-frame operation —
    both core roles cumulated, derived construction intransitive. -/
def reciprocalize (r : RoleList) : RoleList where
  subjectProfile :=
    match r.objectProfile with
    | some o => bundle r.subjectProfile o
    | none   => r.subjectProfile

/-- Reciprocalization denucleativizes: no internal argument survives. -/
theorem reciprocalize_objectProfile (r : RoleList) :
    (reciprocalize r).objectProfile = none := rfl

theorem reciprocalize_subjectProfile (ho : r.objectProfile = some o) :
    (reciprocalize r).subjectProfile = bundle r.subjectProfile o := by
  simp [reciprocalize, ho]

/-- For any transitive base with an agentive subject and an affected
    object, the reciprocalized subject bears a complex role (§4.1). -/
theorem reciprocalize_isComplexRole (ho : r.objectProfile = some o)
    (ha : 0 < r.subjectProfile.pAgentScore) (hp : 0 < o.pPatientScore) :
    IsComplexRole (reciprocalize r).subjectProfile := by
  rw [reciprocalize_subjectProfile ho]
  exact bundle_isComplexRole _ _ ha hp

end Bundling

-- Reciprocalizing the manner-of-contact template (the surface-contact
-- *kiss*/*hug* family) yields a complex subject role.
example : IsComplexRole (reciprocalize mannerContact).subjectProfile := by decide

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

/-- The property cluster of a formation locus, computed from its four
    affordances: the paper's reduction of the nine properties to the locus
    of formation. [nordlinger-2023]'s later per-language profiles check the
    discontinuity prediction against attested judgments in
    `Studies/Nordlinger2023.lean`. -/
def predictedProperties (f : Formation) : PropertyCluster where
  singularEvent := !pluralEventsAvailable f
  productive := !storesOutputs f
  ecmReciprocals := spansPredicates f
  frozenInput := storesOutputs f
  semanticDrift := storesOutputs f
  phrasalIdioms := storesOutputs f
  retainsAccOnDativeSuppression := !reducesAccusative f
  eventNominals := storesOutputs f
  discontinuous := !pluralEventsAvailable f

/-- The derived lexical cluster matches the paper's concluding table. -/
theorem predictedProperties_lexical :
    predictedProperties .lexical =
      { singularEvent := true, productive := false, ecmReciprocals := false,
        frozenInput := true, semanticDrift := true, phrasalIdioms := true,
        retainsAccOnDativeSuppression := false, eventNominals := true,
        discontinuous := true } := rfl

/-- The two predicted clusters are complementary on every property: the two
    loci differ on every affordance and every property is a literal of one
    affordance. -/
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
    IsSymmetricVerb f ↔ (predictedProperties f).singularEvent = true := by
  cases f <;> decide

/-- "The discontinuous construction is a property of symmetric verbs"
    (§7.5). -/
theorem discontinuous_iff_symmetric (f : Formation) :
    (predictedProperties f).discontinuous = true ↔ IsSymmetricVerb f := by
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

section IReading

variable {r : RoleList} {o : EntailmentProfile} {c : Construction}

/-- The subject's entailment profile over a transitive base: the
    periphrastic subject bears the base subject role; both verb types bear
    the bundled complex role (§4.1–4.3). -/
def Construction.subjectProfile (r : RoleList) : Construction → EntailmentProfile
  | .periphrastic => r.subjectProfile
  | .lexicalVerb | .syntacticVerb => (reciprocalize r).subjectProfile

/-- The "I" reading over a transitive base (§4.3, p. 287): the sub-event
    reading must be available and the subject must bear a sole role — a
    profile that is not complex. -/
def Construction.allowsIReading (r : RoleList) (c : Construction) : Prop :=
  c.allowsSubEventReading ∧ ¬ IsComplexRole (c.subjectProfile r)

/-- Sub-event availability is necessary for the "I" reading (§4.3). -/
theorem subevents_necessary_for_I (h : c.allowsSubEventReading = false) :
    ¬ c.allowsIReading r :=
  fun hc => absurd hc.1 (by simp [h])

/-- A sole θ-role on the subject is necessary for the "I" reading (§4.3). -/
theorem complex_role_blocks_I (h : IsComplexRole (c.subjectProfile r)) :
    ¬ c.allowsIReading r :=
  fun hc => hc.2 h

/-- A periphrastic reciprocal over a non-complex subject role allows the
    "I" reading: sub-events from the anaphor's plural operator, sole role
    on the subject. -/
theorem periphrastic_allows_I (hs : ¬ IsComplexRole r.subjectProfile) :
    Construction.periphrastic.allowsIReading r :=
  ⟨rfl, hs⟩

/-- Lexical derivation: no plural events in the lexicon → no sub-events →
    no "I" reading (§3.5 → §2.2 → §4.3), for any base. -/
theorem lexical_no_I_reading (r : RoleList) :
    ¬ (Construction.ofFormation .lexical).allowsIReading r :=
  subevents_necessary_for_I rfl

/-- Syntactic derivation: the bundled subject is a complex role → no "I"
    reading (§4.2 → §4.3), despite the sub-event reading being available. -/
theorem syntactic_no_I_reading (ho : r.objectProfile = some o)
    (ha : 0 < r.subjectProfile.pAgentScore) (hp : 0 < o.pPatientScore) :
    ¬ (Construction.ofFormation .syntactic).allowsIReading r :=
  complex_role_blocks_I (reciprocalize_isComplexRole ho ha hp)

/-- Neither reciprocal verb type allows the "I" reading, over any
    transitive base with an agentive subject and an affected object. -/
theorem no_I_reading_either_formation (f : Formation)
    (ho : r.objectProfile = some o) (ha : 0 < r.subjectProfile.pAgentScore)
    (hp : 0 < o.pPatientScore) :
    ¬ (Construction.ofFormation f).allowsIReading r := by
  cases f
  exacts [lexical_no_I_reading r, syntactic_no_I_reading ho ha hp]

/-- Over any transitive base whose subject role is agentive but not
    complex and whose object is affected, the "I" reading is available in
    the periphrastic construction and only there. -/
theorem I_reading_iff_periphrastic (hs : ¬ IsComplexRole r.subjectProfile)
    (ho : r.objectProfile = some o) (ha : 0 < r.subjectProfile.pAgentScore)
    (hp : 0 < o.pPatientScore) :
    c.allowsIReading r ↔ c = .periphrastic := by
  cases c
  · exact iff_of_true (periphrastic_allows_I hs) rfl
  · exact iff_of_false (subevents_necessary_for_I rfl) (by decide)
  · exact iff_of_false
      (complex_role_blocks_I (reciprocalize_isComplexRole ho ha hp)) (by decide)

/-- Singular-event verbs lack the sub-event reading: both are the
    availability of plural events at the composition locus (§2.2–2.3). -/
theorem singular_event_no_subevents (f : Formation)
    (h : (predictedProperties f).singularEvent = true) :
    (Construction.ofFormation f).allowsSubEventReading = false := by
  simpa [predictedProperties, Construction.allowsSubEventReading,
    compositionLocus_ofFormation] using h

end IReading

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
