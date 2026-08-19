import Linglib.Syntax.Reciprocal
import Linglib.Syntax.Category.Verb.Reciprocal
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Semantics.Plurality.Groups

/-!
# Siloni (2012): Reciprocal verbs and symmetry

Beyond periphrastic reciprocals (*each other*), languages have reciprocal
*verbs* — predicates that express reciprocity without an anaphoric object,
carried as `Verb.Reciprocal` entries. [siloni-2012] (building on
[siloni-2008]) splits them by where reciprocalization applies — the
`Formation` parameter of `Syntax/Reciprocal.lean`, an instance of
[reinhart-siloni-2005]'s lex-syn parameter — and derives nine clustering
properties from that split alone: "the distinctions all follow from the
fact that the two types of verbs are formed in different components of the
grammar."

Reciprocalization acts on argument structure: `reciprocalize` takes a
transitive `RoleList` and returns an intransitive one whose subject bears
the join of the two base profiles — [reinhart-siloni-2005]'s complex
`[θᵢ · θⱼ]` role, `EntailmentProfile`'s `⊔`. The bundled subject retains
the base subject's Proto-Agent entailments and inherits the object's
Proto-Patient entailments (`reciprocalize_dominates` — the depictive and
comparative-ellipsis diagnostics of §3.1–3.2), so it is a complex role
(`EntailmentProfile.IsComplexRole`). Event-semantically, a symmetric verb
denotes a *group* event ([landman-2000]'s `up`, `Plurality.GroupStructure`):
`SymmetricEvent.down_eq` is the paper's (41) — dissolution recovers the
directional sub-events — while `SymmetricEvent.not_subEventReading`
delivers §2.2's observation that the atom itself never decomposes. Since
the "I" reading of embedded reciprocals ([higginbotham-1980]; the
LF-decomposed periphrastic arm is `Studies/HeimLasnikMay1991.lean`)
requires a sub-event reading plus a sole-role subject, both verb types
lack it for any transitive base with an agentive subject and an affected
object (`I_reading_iff_periphrastic`), each failing a different condition.

The nine surface properties derive from four affordances of the locus of
application (`pluralEventsAvailable` per generalization (29),
`storesOutputs`, `spansPredicates`, `reducesAccusative`): the paper's
concluding table is a theorem (`predictedProperties_lexical`), as is the
perfect complementarity of the two clusters. The paper's eleven-language
sample is recorded per-language (`hebrew` … `bulgarian`).
-/

namespace Siloni2012

open Reciprocal ArgumentStructure Semantics.Plurality

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
    syntactic derivation, so lexicon-formed reciprocals denote group atoms
    (`SymmetricEvent`), whose sub-events are recovered only by
    dissolution. -/
def pluralEventsAvailable : Formation → Bool
  | .lexical   => false
  | .syntactic => true

/-- Whether the operation's outputs are stored entries. Applying within the
    inventory, the lexical operation may also take frozen entries as input
    (`Verb.Reciprocal.IsFrozen`); stored outputs can drift, head idioms,
    and feed lexical nominalization, and listing caps productivity
    (§5.3, §6). -/
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

/-! ### Group events and the sub-event reading (§2.2–2.3, §4.1)

The event domain is a semilattice of events under sum; a symmetric verb
denotes a *group* event — [landman-2000]'s `up` applied to the sum of the
two directional sub-events. Dissolution recovers the sub-events (the
paper's (41)), but the group atom itself has no proper parts, so counting
and modification never see them. -/

section Events

variable {α E : Type*} [SemilatticeSup E] {R : α → α → E → Prop} {x y : α}
  {e : E}

/-- The sub-event reading of a reciprocal event (§2.2): the event
    decomposes into two proper parts, one realizing each direction. -/
def SubEventReading (R : α → α → E → Prop) (x y : α) (e : E) : Prop :=
  ∃ e₁ e₂, e₁ < e ∧ e₂ < e ∧ R x y e₁ ∧ R y x e₂ ∧ e = e₁ ⊔ e₂

/-- An event with the sub-event reading has proper parts, so it is not
    atomic (§2.2–2.3). -/
theorem SubEventReading.not_atom :
    SubEventReading R x y e → ¬ Mereology.Atom e :=
  fun ⟨_, _, h₁, _, _, _, _⟩ ha => h₁.ne (ha.eq h₁.le)

/-- The sum of incomparable directional sub-events has the sub-event
    reading: reciprocity by accumulation (§4.2). -/
theorem subEventReading_sup {e₁ e₂ : E} (h₁ : ¬ e₂ ≤ e₁) (h₂ : ¬ e₁ ≤ e₂)
    (hxy : R x y e₁) (hyx : R y x e₂) : SubEventReading R x y (e₁ ⊔ e₂) :=
  ⟨e₁, e₂, left_lt_sup.2 h₁, right_lt_sup.2 h₂, hxy, hyx, rfl⟩

/-- The symmetric-verb denotation ((36)'s SYM marking, (41a)): an atomic
    mutual event packing the two directional sub-events into a group
    event. "SYM is not a feature": it abbreviates the meaning postulate
    relating V_SYM to V, `SymmetricEvent.down_eq`. -/
def SymmetricEvent (G : GroupStructure E) (R : α → α → E → Prop)
    (x y : α) (e : E) : Prop :=
  ∃ e₁ e₂, R x y e₁ ∧ R y x e₂ ∧ e = G.up (e₁ ⊔ e₂)

/-- The paper's (41): a symmetric reciprocal event dissolves into
    underlying directional events — "John and Mary kissed" entails a
    kissing by John of Mary and one by Mary of John. -/
theorem SymmetricEvent.down_eq {G : GroupStructure E}
    (h : SymmetricEvent G R x y e) :
    ∃ e₁ e₂, G.down e = e₁ ⊔ e₂ ∧ R x y e₁ ∧ R y x e₂ := by
  obtain ⟨e₁, e₂, h₁, h₂, rfl⟩ := h
  exact ⟨e₁, e₂, G.down_up _, h₁, h₂⟩

/-- The symmetric event itself is atomic: count adverbials count it once,
    and the sub-event reading is unavailable for any directional relation
    (§2.2–2.3). -/
theorem SymmetricEvent.not_subEventReading {G : GroupStructure E}
    (h : SymmetricEvent G R x y e) {R' : α → α → E → Prop} {x' y' : α} :
    ¬ SubEventReading R' x' y' e := by
  obtain ⟨e₁, e₂, -, -, rfl⟩ := h
  exact fun hs => hs.not_atom (G.atom_up _)

end Events

/-! ### Reciprocalization on argument structure (§4.1–4.2)

Reciprocalization eliminates the internal argument position and associates
its θ-role with the subject — bundling in the lexicon, parasitic
assignment in the syntax; the resulting role state is the same. On the
Dowty substrate this is `EntailmentProfile`'s join, applied to a
transitive `RoleList`; realizes [creissels-2025]'s `Voice.reciprocalization`
coding-frame operation (both core roles cumulated, derived construction
intransitive). -/

section Reciprocalize

variable {r : RoleList} {o : EntailmentProfile}

/-- Reciprocalization ((35)): the internal position is eliminated and its
    profile bundled onto the subject; "the bundle [θᵢ - θⱼ] retains the
    thematic properties of [θᵢ] and [θⱼ]" (`reciprocalize_dominates`). -/
def reciprocalize (r : RoleList) : RoleList where
  subjectProfile :=
    match r.objectProfile with
    | some o => r.subjectProfile ⊔ o
    | none   => r.subjectProfile

/-- Reciprocalization denucleativizes: no internal argument survives. -/
theorem reciprocalize_objectProfile (r : RoleList) :
    (reciprocalize r).objectProfile = none := rfl

theorem reciprocalize_subjectProfile (ho : r.objectProfile = some o) :
    (reciprocalize r).subjectProfile = r.subjectProfile ⊔ o := by
  simp [reciprocalize, ho]

/-- The reciprocalized subject retains the base subject's Proto-Agent
    entailments and inherits the object's Proto-Patient entailments — the
    Czech depictive (§3.1) and comparative-ellipsis (§3.2) diagnostics. -/
theorem reciprocalize_dominates (ho : r.objectProfile = some o) :
    PAgentDominates (reciprocalize r).subjectProfile r.subjectProfile ∧
    PPatientDominates (reciprocalize r).subjectProfile o := by
  rw [reciprocalize_subjectProfile ho]
  exact ⟨pAgentDominates_sup_left .., pPatientDominates_sup_right ..⟩

/-- For any transitive base with an agentive subject and an affected
    object, the reciprocalized subject bears a complex role (§4.1). -/
theorem reciprocalize_isComplexRole (ho : r.objectProfile = some o)
    (ha : 0 < r.subjectProfile.pAgentScore) (hp : 0 < o.pPatientScore) :
    ((reciprocalize r).subjectProfile).IsComplexRole := by
  rw [reciprocalize_subjectProfile ho]
  exact EntailmentProfile.isComplexRole_sup ha hp

/-- A reciprocal verb entry's bundled subject role is the subject of its
    reciprocalized base grid: the entry-level and grid-level operations
    agree. -/
theorem bundledSubjectProfile_eq_reciprocalize (v : Verb.Reciprocal)
    {b : Verb} {ps po : EntailmentProfile} (hb : v.base = some b)
    (hs : b.subjectEntailments = some ps)
    (ho : b.objectEntailments = some po) :
    v.bundledSubjectProfile = some (reciprocalize ⟨ps, some po⟩).subjectProfile := by
  rw [Verb.Reciprocal.bundledSubjectProfile_eq hb hs ho]; rfl

variable {α E : Type*} [SemilatticeSup E] in
/-- Reciprocal bundling ((36)): `V(ACC) [θᵢ] [θⱼ] → V_SYM [θᵢ - θⱼ]` — one
    lexical operation, two components. On the grid, the accusative is
    reduced and the internal role bundled onto the subject
    (`reciprocalize`; `RoleList` carries no case slot, so the reduction
    surfaces as the loss of the object position, and its typological trace
    is `reducesAccusative`). On the denotation, SYM packs the base
    relation's directional events into group atoms (`SymmetricEvent`). -/
def reciprocalBundling (G : GroupStructure E) (grid : RoleList)
    (den : α → α → E → Prop) : RoleList × (α → α → E → Prop) :=
  (reciprocalize grid, SymmetricEvent G den)

variable {α E : Type*} [SemilatticeSup E] {den : α → α → E → Prop}
  {grid : RoleList} {x y : α} {e : E} in
/-- What SYM buys ((36), (41)): each event of the derived verb is a single
    atom — counting and modification see one event — yet entails a base
    event in each direction. -/
theorem reciprocalBundling_symmetric (G : GroupStructure E)
    (hden : (reciprocalBundling G grid den).2 x y e) :
    Mereology.Atom e ∧
      ∃ e₁ e₂, G.down e = e₁ ⊔ e₂ ∧ den x y e₁ ∧ den y x e₂ := by
  obtain ⟨e₁, e₂, h₁, h₂, rfl⟩ := hden
  exact ⟨G.atom_up _, e₁, e₂, G.down_up _, h₁, h₂⟩

end Reciprocalize

-- Reciprocalizing the manner-of-contact template (the surface-contact
-- *kiss*/*hug* family) yields a complex subject role.
example : ((reciprocalize mannerContact).subjectProfile).IsComplexRole := by
  decide

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

/-! ### The "I" reading (§2.1, §4.3)

In "John and Paul said they defeated each other in the final"
([higginbotham-1980]), the "I" reading — John said he defeated Paul, and
Paul said he defeated John — requires both that the embedded verb allow
the sub-event reading and that its subject bear exactly one θ-role
(§4.3, p. 287). The LF decomposition of the periphrastic side and the
full grain problem live in `Studies/HeimLasnikMay1991.lean`. -/

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
  c.allowsSubEventReading ∧ ¬ (c.subjectProfile r).IsComplexRole

/-- Sub-event availability is necessary for the "I" reading (§4.3). -/
theorem subevents_necessary_for_I (h : c.allowsSubEventReading = false) :
    ¬ c.allowsIReading r :=
  fun hc => absurd hc.1 (by simp [h])

/-- A sole θ-role on the subject is necessary for the "I" reading (§4.3). -/
theorem complex_role_blocks_I (h : (c.subjectProfile r).IsComplexRole) :
    ¬ c.allowsIReading r :=
  fun hc => hc.2 h

/-- A periphrastic reciprocal over a non-complex subject role allows the
    "I" reading: sub-events from the anaphor's plural operator, sole role
    on the subject. -/
theorem periphrastic_allows_I (hs : ¬ r.subjectProfile.IsComplexRole) :
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
theorem I_reading_iff_periphrastic (hs : ¬ r.subjectProfile.IsComplexRole)
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
