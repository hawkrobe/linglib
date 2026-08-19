import Linglib.Syntax.Reciprocal
import Linglib.Syntax.Category.Verb.Reciprocal
import Linglib.Syntax.Category.Verb.Symmetric
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
transitive `RoleList` and returns an intransitive one whose subject
carries both base profiles' entailments — as [reinhart-siloni-2005]'s
bundled complex `[θᵢ · θⱼ]` role in the lexicon ((35)–(36)), or as two
separately assigned roles via last-resort parasitic assignment in the
syntax ((43), the `Merger` ledger, which also derives the raising/passive
ban and the ECM derivation (63)). Event-semantically the two loci share
one mechanism, [landman-2000]'s group operators (`Plurality.GroupStructure`)
in both domains: a symmetric verb is a set of atomic events whose complex
role assigns the group atom over an unordered pair, related to its base
by fn. 17's meaning postulate (`Verb.SymmetricDenotation`, in
`Syntax/Category/Verb/Symmetric.lean`), from which (41) — the underlying
directional events — is derived (`underlying_of_symmetric`);
the syntactic reciprocal has the accumulation reading ((46b),
`AccumulationReading`) and the `up`-packed singular reading ((47),
`GroupEventReading`), whose content provably coincides with the symmetric
verb's (`GroupEventReading.underlyingReading`). Since the "I" reading of
embedded reciprocals ([higginbotham-1980]; the LF-decomposed periphrastic
arm is `Studies/HeimLasnikMay1991.lean`) requires a sub-event reading
plus a sole-role subject, both verb types lack it
(`I_reading_iff_periphrastic`).

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
    syntactic derivation, so lexicon-formed reciprocals denote atomic
    events (`Verb.SymmetricDenotation`), whose underlying events are
    recovered only by dissolution. -/
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

/-! ### Symmetric verbs and reciprocal readings (§2.2, §4.1–4.2)

Neo-Davidsonian format after [landman-2000]: verbs are sets of events,
θ-roles are functions from events to individuals, and both the individual
and the event domain are semilattices carrying the group operators.
fn. 17's lexical format of `V_SYM` is the substrate contract
`Verb.SymmetricDenotation`; here it meets Siloni's numbered readings and
the derivation of (41). -/

section Events

variable {D E : Type*} [SemilatticeSup E] {V : Set E} {ag th : E → D}
  {d₁ d₂ : D} {e : E} {GE : GroupStructure E}

/-- Two base-verb events realizing the two directions between `d₁` and
    `d₂` — the kernel shared by (41b), (46b), and (47). -/
def CrossedPair (V : Set E) (ag th : E → D) (d₁ d₂ : D) (e₁ e₂ : E) : Prop :=
  e₁ ∈ V ∧ e₂ ∈ V ∧ ag e₁ = d₁ ∧ th e₁ = d₂ ∧ ag e₂ = d₂ ∧ th e₂ = d₁

/-- The accumulation reading of a syntactic reciprocal ((46b)): the event
    is the plain sum of the two directional sub-events. -/
def AccumulationReading (V : Set E) (ag th : E → D) (d₁ d₂ : D) (e : E) :
    Prop :=
  ∃ e₁ e₂, e = e₁ ⊔ e₂ ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- The singular-event reading of a syntactic reciprocal ((47)): `up`
    packs the sum of the directional sub-events into an atomic group
    event. -/
def GroupEventReading (GE : GroupStructure E) (V : Set E) (ag th : E → D)
    (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, e = GE.up (e₁ ⊔ e₂) ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- The content of (41b): the event's dissolution is the sum of two
    directional base events. -/
def UnderlyingReading (GE : GroupStructure E) (V : Set E) (ag th : E → D)
    (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, GE.down e = e₁ ⊔ e₂ ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- The sub-event reading (§2.2): the event decomposes into two proper
    parts realizing the two directions. -/
def SubEventReading (V : Set E) (ag th : E → D) (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, e₁ < e ∧ e₂ < e ∧ e = e₁ ⊔ e₂ ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- An event with the sub-event reading has proper parts, so it is not
    atomic. -/
theorem SubEventReading.not_atom :
    SubEventReading V ag th d₁ d₂ e → ¬ Mereology.Atom e :=
  fun ⟨_, _, h₁, _, _, _⟩ ha => h₁.ne (ha.eq h₁.le)

/-- Incomparable crossed sub-events yield the sub-event reading — the
    accumulation reading makes sub-events visible ((46b)). -/
theorem subEventReading_of_crossedPair {e₁ e₂ : E} (h₁ : ¬ e₂ ≤ e₁)
    (h₂ : ¬ e₁ ≤ e₂) (hc : CrossedPair V ag th d₁ d₂ e₁ e₂) :
    SubEventReading V ag th d₁ d₂ (e₁ ⊔ e₂) :=
  ⟨e₁, e₂, left_lt_sup.2 h₁, right_lt_sup.2 h₂, rfl, hc⟩

/-- On the singular-event reading too, counting sees one event: group
    events are atoms. -/
theorem GroupEventReading.atom (h : GroupEventReading GE V ag th d₁ d₂ e) :
    Mereology.Atom e := by
  obtain ⟨_, _, rfl, -⟩ := h
  exact GE.atom_up _

/-- "The interpretation in (47) is identical to that of kiss_SYM (41b)":
    the group-event reading's dissolution content coincides with what the
    symmetric verb's postulate delivers. -/
theorem GroupEventReading.underlyingReading
    (h : GroupEventReading GE V ag th d₁ d₂ e) :
    UnderlyingReading GE V ag th d₁ d₂ e := by
  obtain ⟨e₁, e₂, rfl, hc⟩ := h
  exact ⟨e₁, e₂, GE.down_up _, hc⟩

variable [SemilatticeSup D] {GD : GroupStructure D} {Vsym : Set E}
  {agTh : E → D}

/-- (41): `∃e [kiss_SYM(e) ∧ [Ag-Th](e, John and Mary)]` entails two
    underlying directional kissings — `Verb.SymmetricDenotation`'s meaning
    postulate ((36)'s SYM marking, fn. 17) applied. -/
theorem underlying_of_symmetric
    [h : Verb.SymmetricDenotation GD GE V ag th Vsym agTh] (he : e ∈ Vsym)
    (hne : d₁ ≠ d₂) (hrole : agTh e = GD.up (d₁ ⊔ d₂)) :
    UnderlyingReading GE V ag th d₁ d₂ e := by
  obtain ⟨e₁, e₂, hd, h₁, h₂, ha₁, ht₁, ha₂, ht₂⟩ :=
    h.postulate e he d₁ d₂ hne hrole
  exact ⟨e₁, e₂, hd, h₁, h₂, ha₁, ht₁, ha₂, ht₂⟩

/-- A symmetric verb's events admit no sub-event reading for any predicate
    and roles whatsoever: the underlying events are invisible to counting
    and modification (§2.2). -/
theorem not_subEventReading_of_symmetric
    [h : Verb.SymmetricDenotation GD GE V ag th Vsym agTh] (he : e ∈ Vsym)
    {V' : Set E} {ag' th' : E → D} {d₁' d₂' : D} :
    ¬ SubEventReading V' ag' th' d₁' d₂' e :=
  fun hs => hs.not_atom (h.atomic e he)

end Events

/-! ### Reciprocalization on argument structure (§4.1–4.2)

Reciprocalization eliminates the internal argument position and leaves the
subject carrying both profiles' entailments — a bundled complex role in
the lexicon ((35)–(36)), two separately assigned roles in the syntax
((43)). On the Dowty substrate the profile content is `EntailmentProfile`'s
join over a transitive `RoleList`; realizes [creissels-2025]'s
`Voice.reciprocalization` coding-frame operation (both core roles
cumulated, derived construction intransitive). -/

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

end Reciprocalize

-- Reciprocalizing the manner-of-contact template (the surface-contact
-- *kiss*/*hug* family) yields a complex subject role.
example : ((reciprocalize mannerContact).subjectProfile).IsComplexRole := by
  decide

/-! ### Parasitic assignment (§4.2, (43); the ECM derivation (63))

The syntactic operation forms no complex role: se reduces case (43a), the
internal role is retained on the verbal projection, and a retained role is
assigned upon merger of another θ-argument — a last-resort step (43b).
Raising and passive subjects arrive by internal merge, which assigns no
role, so a retained role can never discharge on them: derived subjects
never reciprocalize ((45), §3.4). In the ECM derivation (63), the
embedded verb's unassigned Agent survives the EPP-deficient TP and rides
the matrix external merger: *Jean* ends θk+θi. -/

/-- Merger against the verbal projection's retained-role ledger ((43),
    (63)): canonical θ-merger discharges one role; se-marked parasitic
    merger discharges the merging role together with every retained role
    (last resort); internal merge (movement) discharges nothing. -/
inductive Merger : (seMarked : Bool) → (before : List ThetaRole) →
    (assigned : List ThetaRole) → (after : List ThetaRole) → Prop
  | canonical (m : Bool) (θ : ThetaRole) (rest : List ThetaRole) :
      Merger m (θ :: rest) [θ] rest
  | parasitic (θ : ThetaRole) (retained : List ThetaRole) :
      retained ≠ [] → Merger true (θ :: retained) (θ :: retained) []
  | internalMerge (m : Bool) (pending : List ThetaRole) :
      Merger m pending [] pending

section Merger

variable {m : Bool} {before assigned after : List ThetaRole}

/-- Without the morphology there is no parasitic assignment: no argument
    receives two roles — the marking requirement "rules out the sole
    potential case of overgeneration" (§4.3 end). -/
theorem Merger.length_le_one (h : Merger false before assigned after) :
    assigned.length ≤ 1 := by
  cases h <;> simp

/-- Two θ-roles land on one argument only via the marked last resort —
    §4.3's sole-role diagnosis, covering (63)'s ECM case, where both roles
    are agentive and profile mixture would not show. -/
theorem Merger.marked_of_two_roles (h : Merger m before assigned after)
    (h2 : 2 ≤ assigned.length) : m = true := by
  cases h <;> simp_all

/-- A merger that assigns no role is movement and leaves the ledger
    intact: derived subjects never discharge a retained role ((45),
    §3.4). -/
theorem Merger.eq_of_assigned_nil (h : Merger m before [] after) :
    after = before := by
  cases h; rfl

-- (63c): at the matrix TP, se-marked merger assigns the matrix external
-- role (θk, *entendre*) together with the retained embedded Agent (θi,
-- *chanter*): Jean_{θk+θi}.
example : Merger true [.experiencer, .agent] [.experiencer, .agent] [] :=
  .parasitic _ _ (by simp)

end Merger

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

/-- The subject's entailment profile over a transitive base. The
    periphrastic subject bears the base subject role; both verb types
    accumulate both profiles' entailments — as one bundled complex role in
    the lexicon ((36)), as two separately assigned roles in the syntax
    ((43), `Merger`) — "via bundling or parasitic assignment respectively"
    (§4.3). -/
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
