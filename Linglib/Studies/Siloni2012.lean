module

public import Linglib.Syntax.Reciprocal
public import Linglib.Studies.HeimLasnikMay1991
public import Linglib.Syntax.Category.Verb.Reciprocal
public import Linglib.Syntax.Category.Verb.Symmetric
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Semantics.ArgumentStructure.CaseRegion
public import Linglib.Semantics.Plurality.Groups

/-!
# Siloni (2012): Reciprocal Verbs and Symmetry

This file formalizes [siloni-2012]'s split of reciprocal verbs, the predicates expressing
reciprocity without an anaphoric object, by the locus of reciprocalization, the lexicon or the
syntax (`Reciprocal.Formation`, [reinhart-siloni-2005]'s lex-syn parameter, building on
[siloni-2008]), and its derivation of nine clustering properties from that split alone.
Reciprocalization eliminates the internal argument position and leaves the subject carrying
both profiles' entailments, as a bundled complex role in the lexicon ((35) and (36),
`reciprocalize`) or as two roles assigned separately by last-resort parasitic assignment in the
syntax ((43), `Merger`, which also derives the ban on derived subjects and the ECM derivation
(63)). Both loci share [landman-2000]'s group operators: a symmetric verb is a set of atomic
events whose complex role assigns the group atom over an unordered pair, related to its base by
the meaning postulate of footnote 17 (`Verb.SymmetricDenotation`), from which the underlying
directional events of (41) follow (`underlying_of_symmetric`); the syntactic reciprocal has the
accumulation reading (46b) and the packed singular reading (47), whose content coincides with
the symmetric verb's (`GroupEventReading.underlyingReading`). The "I" reading of embedded
reciprocals ([higginbotham-1980]) needs a sub-event reading and a sole-role subject, so both
verb types lack it (`I_reading_iff_periphrastic`); the periphrastic sub-event reading is derived
from [heim-lasnik-may-1991]'s LF (`accumulation_of_eachOtherLF`).

The nine properties of the conclusion are each a literal of one of four affordances of the
locus, plural events (generalization (29)), stored outputs, the roles of two predicates, and
obligatory accusative reduction (`Affordance.Available`, `Property.Holds`); the concluding
cluster and the complementarity of the two clusters are theorems (`lexical_properties`,
`holds_syntactic_iff`). The case against an object-clitic analysis of *se* (section 3) is three
diagnostics on which the transitive grid and the reciprocalized grid diverge and the data side
with reciprocalization: Czech depictive case (`depictive_diagnostic`), comparative-ellipsis
remnants (`ellipsis_diagnostic`) and [kayne-1975]'s causative causee (`causative_diagnostic`).
The count-adverbial contrast of (15) and (16) is modelled by five atomic mutual events with
inaccessible parts against five accumulation events with ten accessible directional parts
(`mutualEvent_not_subEventReading`, `accumulated_subEventReading`), and the discontinuous
construction is the dyadic realization of a symmetric entry (section 7.5, `DyadicReading`).

## Implementation notes

* Profiles are the Dowty substrate's `EntailmentProfile` over a transitive `RoleList`; the
  bundled complex role is the join of the subject's and the object's profiles, and a complex
  role is one with both Proto-Agent and Proto-Patient content.
* The affordances of a locus are the four parameters the paper's mechanisms turn on; the
  properties are derived from them and not recorded per formation. The exceptions the paper
  notes, Czech reciprocal event nominals ([hron-2005]) and English *kiss* and *hug* resisting
  the discontinuous construction (footnote 32), are recorded in the docstrings.
* The counting model takes events to be finite sets of markers, with a group atom for each
  round of kissing; the participants' roles are read off the parity of the marker.

## References

* [siloni-2012]
* [siloni-2008]
* [reinhart-siloni-2005]
* [landman-2000]
* [higginbotham-1980]
* [heim-lasnik-may-1991]
* [kayne-1975]
* [hron-2005]
-/

@[expose] public section

namespace Siloni2012

open Reciprocal ArgumentStructure Plurality

/-! ### Three-way reciprocal classification (section 2.4) -/

/-- The three classes of reciprocal constructions: the reciprocal anaphor in object position
(*each other*, *l'un l'autre*) with a subject bearing one θ-role; the reciprocal verb formed in
the lexicon by θ-role bundling (section 4.1), whose subject bears a complex [Agent-Theme] role;
and the reciprocal verb formed in the syntax by a clitic (section 4.2), whose subject bears two
θ-roles via parasitic assignment. -/
inductive Construction
  | periphrastic | lexicalVerb | syntacticVerb
  deriving DecidableEq

/-- The reciprocal-verb class determined by formation locus. -/
def Construction.ofFormation : Formation → Construction
  | .lexical => .lexicalVerb
  | .syntactic => .syntacticVerb

/-! ### The lex-syn architecture (sections 3.5 and 5 to 6) -/

/-- The four affordances of a locus of application, each carrying one of the paper's
mechanisms: plural events, which arise only upon syntactic merging (generalization (29)); stored
outputs, which may take frozen entries as input, drift, head idioms and feed lexical
nominalization while listing caps productivity (sections 5.3 and 6); the θ-roles of two distinct
predicates, as in ECM configurations (section 5.2); and the obligatory reduction of accusative
case whichever argument is suppressed ([reinhart-siloni-2005], section 5.1). -/
inductive Affordance
  | pluralEvents | storesOutputs | spansPredicates | reducesAccusative
  deriving DecidableEq, Fintype

/-- The affordances of a locus: the syntax has plural events and sees the roles of two
predicates, the lexicon stores its outputs and reduces accusative case. -/
def Affordance.Available : Affordance → Formation → Prop
  | .pluralEvents, f | .spansPredicates, f => f = .syntactic
  | .storesOutputs, f | .reducesAccusative, f => f = .lexical

instance (a : Affordance) (f : Formation) : Decidable (a.Available f) := by
  cases a <;> unfold Affordance.Available <;> infer_instance

/-- The locus where a construction's reciprocity is composed: in the lexicon only for lexical
reciprocal verbs, since periphrastic reciprocity is composed by the anaphor's plural operator
in the syntax (section 2.4). -/
def Construction.compositionLocus : Construction → Formation
  | .lexicalVerb => .lexical
  | .periphrastic | .syntacticVerb => .syntactic

/-- A construction allows the sub-event reading when plural events are available where its
reciprocity is composed (section 2.2, generalization (29)). -/
def Construction.AllowsSubEventReading (c : Construction) : Prop :=
  Affordance.pluralEvents.Available c.compositionLocus

instance (c : Construction) : Decidable c.AllowsSubEventReading :=
  inferInstanceAs (Decidable (Affordance.Available _ _))

theorem compositionLocus_ofFormation (f : Formation) :
    (Construction.ofFormation f).compositionLocus = f := by
  cases f <;> rfl

/-! ### Symmetric verbs and reciprocal readings (sections 2.2 and 4.1 to 4.2)

Neo-Davidsonian format after [landman-2000]: verbs are sets of events, θ-roles are functions
from events to individuals, and both domains are semilattices carrying the group operators.
Footnote 17's lexical format of the symmetric verb is the substrate contract
`Verb.SymmetricDenotation`; here it meets the paper's numbered readings and the derivation of
(41). -/

section Events

variable {D E : Type*} [SemilatticeSup E] {V : Set E} {ag th : E → D}
  {d₁ d₂ : D} {e : E} {GE : GroupStructure E}

/-- Two base-verb events realizing the two directions between `d₁` and `d₂`, the kernel shared
by (41b), (46b) and (47). -/
def CrossedPair (V : Set E) (ag th : E → D) (d₁ d₂ : D) (e₁ e₂ : E) : Prop :=
  e₁ ∈ V ∧ e₂ ∈ V ∧ ag e₁ = d₁ ∧ th e₁ = d₂ ∧ ag e₂ = d₂ ∧ th e₂ = d₁

/-- The accumulation reading of a syntactic reciprocal (46b): the event is the plain sum of the
two directional sub-events. -/
def AccumulationReading (V : Set E) (ag th : E → D) (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, e = e₁ ⊔ e₂ ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- The singular-event reading of a syntactic reciprocal (47): `up` packs the sum of the
directional sub-events into an atomic group event. -/
def GroupEventReading (GE : GroupStructure E) (V : Set E) (ag th : E → D)
    (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, e = GE.up (e₁ ⊔ e₂) ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- The content of (41b): the event's dissolution is the sum of two directional base events. -/
def UnderlyingReading (GE : GroupStructure E) (V : Set E) (ag th : E → D)
    (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, GE.down e = e₁ ⊔ e₂ ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- The sub-event reading (section 2.2): the event decomposes into two proper parts realizing
the two directions. -/
def SubEventReading (V : Set E) (ag th : E → D) (d₁ d₂ : D) (e : E) : Prop :=
  ∃ e₁ e₂, e₁ < e ∧ e₂ < e ∧ e = e₁ ⊔ e₂ ∧ CrossedPair V ag th d₁ d₂ e₁ e₂

/-- An event with the sub-event reading has proper parts, so it is not atomic. -/
theorem SubEventReading.not_atom :
    SubEventReading V ag th d₁ d₂ e → ¬ Mereology.Atom e := by
  rintro ⟨e₁, e₂, h₁, h₂, h₃, -⟩ ha
  by_cases hn : IsBot e₁
  · exact h₂.ne (by rw [h₃]; exact (sup_eq_right.mpr (hn _)).symm)
  · exact h₁.ne (ha.eq h₁.le hn)

/-- Incomparable crossed sub-events yield the sub-event reading: the accumulation reading makes
sub-events visible (46b). -/
theorem subEventReading_of_crossedPair {e₁ e₂ : E} (h₁ : ¬ e₂ ≤ e₁)
    (h₂ : ¬ e₁ ≤ e₂) (hc : CrossedPair V ag th d₁ d₂ e₁ e₂) :
    SubEventReading V ag th d₁ d₂ (e₁ ⊔ e₂) :=
  ⟨e₁, e₂, left_lt_sup.2 h₁, right_lt_sup.2 h₂, rfl, hc⟩

/-- On the singular-event reading too, counting sees one event: group events are atoms. -/
theorem GroupEventReading.atom (h : GroupEventReading GE V ag th d₁ d₂ e) :
    Mereology.Atom e := by
  obtain ⟨_, _, rfl, -⟩ := h
  exact GE.atom_up _

/-- The interpretation in (47) is identical to that of the symmetric verb in (41b): the
group-event reading's dissolution content is what the symmetric verb's postulate delivers. -/
theorem GroupEventReading.underlyingReading (h : GroupEventReading GE V ag th d₁ d₂ e) :
    UnderlyingReading GE V ag th d₁ d₂ e := by
  obtain ⟨e₁, e₂, rfl, hc⟩ := h
  exact ⟨e₁, e₂, GE.down_up _, hc⟩

variable [SemilatticeSup D] {GD : GroupStructure D} {Vsym : Set E} {agTh : E → D}

/-- (41): a symmetric kissing of the pair entails two underlying directional kissings, by
`Verb.SymmetricDenotation`'s meaning postulate (the SYM marking of (36), footnote 17). -/
theorem underlying_of_symmetric [h : Verb.SymmetricDenotation GD GE V ag th Vsym agTh]
    (he : e ∈ Vsym) (hne : d₁ ≠ d₂) (hrole : agTh e = GD.up (d₁ ⊔ d₂)) :
    UnderlyingReading GE V ag th d₁ d₂ e := by
  obtain ⟨e₁, e₂, hd, h₁, h₂, ha₁, ht₁, ha₂, ht₂⟩ := h.postulate e he d₁ d₂ hne hrole
  exact ⟨e₁, e₂, hd, h₁, h₂, ha₁, ht₁, ha₂, ht₂⟩

/-- A symmetric verb's events admit no sub-event reading for any predicate and roles
whatsoever: the underlying events are invisible to counting and modification (section 2.2). -/
theorem not_subEventReading_of_symmetric [h : Verb.SymmetricDenotation GD GE V ag th Vsym agTh]
    (he : e ∈ Vsym) {V' : Set E} {ag' th' : E → D} {d₁' d₂' : D} :
    ¬ SubEventReading V' ag' th' d₁' d₂' e :=
  λ hs => hs.not_atom (h.atomic e he)

end Events

/-! ### Reciprocalization on argument structure (sections 4.1 to 4.2)

Reciprocalization eliminates the internal argument position and leaves the subject carrying
both profiles' entailments, a bundled complex role in the lexicon ((35) and (36)) and two
separately assigned roles in the syntax (43). On the Dowty substrate the profile content is the
join of `EntailmentProfile`s over a transitive `RoleList`, the valency substrate's
`Voice.reciprocalization` coding-frame operation with both core roles cumulated and the derived
construction intransitive. -/

section Reciprocalize

variable {r : RoleList} {o : EntailmentProfile}

/-- Reciprocalization (35): the internal position is eliminated and its profile bundled onto
the subject; the bundle retains the thematic properties of both roles
(`reciprocalize_dominates`). -/
def reciprocalize (r : RoleList) : RoleList where
  subjectProfile :=
    match r.objectProfile with
    | some o => r.subjectProfile ⊔ o
    | none => r.subjectProfile

/-- Reciprocalization leaves no internal argument. -/
theorem reciprocalize_objectProfile (r : RoleList) :
    (reciprocalize r).objectProfile = none := rfl

theorem reciprocalize_subjectProfile (ho : r.objectProfile = some o) :
    (reciprocalize r).subjectProfile = r.subjectProfile ⊔ o := by
  simp [reciprocalize, ho]

/-- The reciprocalized subject retains the base subject's Proto-Agent entailments and inherits
the object's Proto-Patient entailments, the Czech depictive (section 3.1) and
comparative-ellipsis (section 3.2) diagnostics. -/
theorem reciprocalize_dominates (ho : r.objectProfile = some o) :
    PAgentDominates (reciprocalize r).subjectProfile r.subjectProfile ∧
    PPatientDominates (reciprocalize r).subjectProfile o := by
  rw [reciprocalize_subjectProfile ho]
  exact ⟨pAgentDominates_sup_left .., pPatientDominates_sup_right ..⟩

/-- For any transitive base with an agentive subject and an affected object, the reciprocalized
subject bears a complex role (section 4.1). -/
theorem reciprocalize_isComplexRole (ho : r.objectProfile = some o)
    (ha : 0 < r.subjectProfile.pAgentScore) (hp : 0 < o.pPatientScore) :
    ((reciprocalize r).subjectProfile).IsComplexRole := by
  rw [reciprocalize_subjectProfile ho]
  exact EntailmentProfile.isComplexRole_sup ha hp

/-- A reciprocal verb entry's bundled subject role is the subject of its reciprocalized base
grid: the entry-level and grid-level operations agree. -/
theorem bundledSubjectProfile_eq_reciprocalize (v : Verb.Reciprocal)
    {b : Verb} {ps po : EntailmentProfile} (hb : v.base = some b)
    (hs : b.subjectEntailments = some ps) (ho : b.objectEntailments = some po) :
    v.bundledSubjectProfile = some (reciprocalize ⟨ps, some po⟩).subjectProfile := by
  rw [Verb.Reciprocal.bundledSubjectProfile_eq hb hs ho]; rfl

end Reciprocalize

/-! ### Against an object-clitic analysis of *se* (section 3)

The rival analysis keeps the base transitive grid, with *se* realizing the internal argument;
reciprocalization instead removes the internal position and leaves the subject with both roles.
Three diagnostics decide, each a function from the verb's grid to an observable. Czech
depictives agree in case with the argument they are predicated of (17): with *se*, a depictive
construing with the Theme is nominative (18), so the Theme sits on the subject. The
comparative-ellipsis remnant construes with a case-marked argument position: transitives allow
subject and object readings (19a), *se*-verbs only the subject reading (19b), and an accusative
remnant is ungrammatical (20) because no accusative argument exists. And [kayne-1975]'s
causative generalization introduces the causee of a transitive with dative *à* and leaves an
intransitive's causee bare (25a) and (25b): *se*-verbs take the bare causee (25d), patterning
with intransitives, though a genuine object clitic patterns transitively (25c). The fourth
diagnostic, that derived subjects never reciprocalize (section 3.4, (26)), is
`Merger.eq_of_assigned_nil`. -/

section SeDiagnostics

variable {base : RoleList} {o : EntailmentProfile}

/-- [kayne-1975]'s causative generalization (section 3.3): under *faire*, the causee of an
object-taking predicate is introduced by dative *à*; an intransitive's causee stays bare. -/
def causeeRegion (r : RoleList) : CaseRegion :=
  if r.objectProfile.isSome then .dative else .accAbs

/-- (25a) against (25d): keeping the transitive grid predicts the dative causee;
reciprocalization predicts the bare causee, and *Pierre a fait s'embrasser Jean et Marie*
decides for reciprocalization. -/
theorem causative_diagnostic (ho : base.objectProfile = some o) :
    causeeRegion (reciprocalize base) = .accAbs ∧ causeeRegion base = .dative :=
  ⟨rfl, by simp [causeeRegion, ho]⟩

/-- The case of a depictive construing with the Theme (section 3.1): accusative if the internal
role sits on an object (17), nominative if it sits on the subject. -/
def themeDepictiveRegion (r : RoleList) : CaseRegion :=
  if r.objectProfile.isSome then .accAbs else .nomErg

/-- (18): with *se*, the theme-oriented depictive is nominative, and licitly so since the
reciprocalized subject bears the object's Proto-Patient entailments; the object-clitic grid
predicts accusative. -/
theorem depictive_diagnostic (ho : base.objectProfile = some o) (hp : 0 < o.pPatientScore) :
    themeDepictiveRegion (reciprocalize base) = .nomErg ∧
      0 < (reciprocalize base).subjectProfile.pPatientScore ∧
      themeDepictiveRegion base = .accAbs := by
  refine ⟨rfl, ?_, by simp [themeDepictiveRegion, ho]⟩
  rw [reciprocalize_subjectProfile ho]
  exact hp.trans_le (EntailmentProfile.pPatientScore_mono le_sup_right)

/-- The comparative remnant construes with a grid position (section 3.2): the transitive offers
two readings (19a), the reciprocalized grid one (19b); with no object there is no accusative
remnant ((20) and (21)). -/
theorem ellipsis_diagnostic (ho : base.objectProfile = some o) :
    (reciprocalize base).args.length = 1 ∧ base.args.length = 2 :=
  ⟨rfl, by simp [RoleList.args, ho]⟩

end SeDiagnostics

/-! ### Parasitic assignment (section 4.2, (43); the ECM derivation (63))

The syntactic operation forms no complex role: *se* reduces case (43a), the internal role is
retained on the verbal projection, and a retained role is assigned upon merger of another
θ-argument, a last-resort step (43b). Raising and passive subjects arrive by internal merge,
which assigns no role, so a retained role can never discharge on them: derived subjects never
reciprocalize ((45), section 3.4). In the ECM derivation (63), the embedded verb's unassigned
Agent survives the EPP-deficient TP and rides the matrix external merger, so that *Jean* ends
with both roles. -/

/-- Merger against the verbal projection's retained-role ledger ((43) and (63)): canonical
θ-merger discharges one role; *se*-marked parasitic merger discharges the merging role together
with every retained role (last resort); internal merge (movement) discharges nothing. -/
inductive Merger : (seMarked : Bool) → (before : List ThetaRole) →
    (assigned : List ThetaRole) → (after : List ThetaRole) → Prop
  | canonical (m : Bool) (θ : ThetaRole) (rest : List ThetaRole) : Merger m (θ :: rest) [θ] rest
  | parasitic (θ : ThetaRole) (retained : List ThetaRole) :
      retained ≠ [] → Merger true (θ :: retained) (θ :: retained) []
  | internalMerge (m : Bool) (pending : List ThetaRole) : Merger m pending [] pending

section Merger

variable {m : Bool} {before assigned after : List ThetaRole}

/-- Without the morphology there is no parasitic assignment, so no argument receives two roles:
the marking requirement rules out the sole potential case of overgeneration (section 5.2). -/
theorem Merger.length_le_one (h : Merger false before assigned after) :
    assigned.length ≤ 1 := by
  cases h <;> simp

/-- Two θ-roles land on one argument only via the marked last resort, section 4.3's sole-role
diagnosis, covering (63)'s ECM case where both roles are agentive. -/
theorem Merger.marked_of_two_roles (h : Merger m before assigned after)
    (h2 : 2 ≤ assigned.length) : m = true := by
  cases h <;> simp_all

/-- A merger that assigns no role is movement and leaves the ledger intact: derived subjects
never discharge a retained role ((45), section 3.4). -/
theorem Merger.eq_of_assigned_nil (h : Merger m before [] after) : after = before := by
  cases h; rfl

/-- (63c): at the matrix TP, *se*-marked merger assigns the matrix external role of *entendre*
together with the retained embedded Agent of *chanter*. -/
theorem ecm_parasitic : Merger true [.experiencer, .agent] [.experiencer, .agent] [] :=
  .parasitic _ _ (by simp)

end Merger

/-! ### The nine-property cluster (sections 2 to 7) -/

/-- The nine properties distinguishing lexical from syntactic reciprocal verbs, in the order of
the paper's concluding enumeration: (i) reciprocity involves a singular atomic event, so that
count adverbials yield mutual events rather than directional sub-events (sections 2.2 to 2.3);
(ii) the operation applies productively to transitive verbs (sections 3.5 and 5); (iii) ECM
reciprocal verbs exist, reciprocalization spanning a clause boundary (section 5.2); (iv) the
verb can be formed from a frozen entry without a transitive alternate (section 5.3); (v) it can
undergo semantic drift (section 5.3); (vi) it can head phrasal idioms unavailable to the
transitive alternate (section 5.3); (vii) it can retain an accusative argument when
reciprocalization suppresses the dative (section 5.1); (viii) it derives reciprocal event
nominals (section 6), with the exception of Czech, whose lexical nominalization ([hron-2005])
feeds syntactic reciprocalization because its clitic attaches to nouns; and (ix) it allows the
discontinuous construction of subject and comitative (section 7), a property of symmetric verbs
(section 7.5) with verb-level exceptions in both directions, English *kiss* and *hug* resisting
it (footnote 32) and listed entries in syntax-setting languages such as French *se battre*
allowing it (section 7.2). -/
inductive Property
  | singularEvent | productive | ecmReciprocals | frozenInput | semanticDrift | phrasalIdioms
  | retainsAccOnDativeSuppression | eventNominals | discontinuous
  deriving DecidableEq, Fintype

/-- A property holds of a formation as a literal of one affordance of its locus: the paper's
reduction of the nine properties to the locus of formation. -/
def Property.Holds : Property → Formation → Prop
  | .singularEvent, f | .discontinuous, f => ¬ Affordance.pluralEvents.Available f
  | .productive, f => ¬ Affordance.storesOutputs.Available f
  | .ecmReciprocals, f => Affordance.spansPredicates.Available f
  | .frozenInput, f | .semanticDrift, f | .phrasalIdioms, f | .eventNominals, f =>
      Affordance.storesOutputs.Available f
  | .retainsAccOnDativeSuppression, f => ¬ Affordance.reducesAccusative.Available f

instance (p : Property) (f : Formation) : Decidable (p.Holds f) := by
  cases p <;> unfold Property.Holds <;> infer_instance

/-- The concluding table: the properties of lexical reciprocal verbs. -/
theorem lexical_properties : Finset.univ.filter (Property.Holds · .lexical) =
    {.singularEvent, .frozenInput, .semanticDrift, .phrasalIdioms, .eventNominals,
      .discontinuous} := by
  decide

/-- The two clusters are complementary on every property: the loci differ on every affordance
and every property is a literal of one affordance. -/
theorem holds_syntactic_iff (p : Property) : p.Holds .syntactic ↔ ¬ p.Holds .lexical := by
  cases p <;> decide

/-- The discontinuous construction is a property of symmetric verbs, those whose reciprocity is
a singular event (section 7.5): both are the absence of plural events at the locus. -/
theorem holds_discontinuous_iff_singularEvent (f : Formation) :
    Property.discontinuous.Holds f ↔ Property.singularEvent.Holds f :=
  Iff.rfl

/-! ### The "I" reading (sections 2.1 and 4.3)

In *John and Paul said they defeated each other in the final* ([higginbotham-1980]), the "I"
reading, on which John said he defeated Paul and Paul said he defeated John, requires both that
the embedded verb allow the sub-event reading and that its subject bear exactly one θ-role
(section 4.3). The LF decomposition of the periphrastic side is `Studies/HeimLasnikMay1991`. -/

section IReading

variable {r : RoleList} {o : EntailmentProfile} {c : Construction}

/-- The subject's entailment profile over a transitive base: the periphrastic subject bears the
base subject role, while both verb types accumulate both profiles' entailments, as one bundled
complex role in the lexicon (36) or as two separately assigned roles in the syntax ((43),
`Merger`). -/
def Construction.subjectProfile (r : RoleList) : Construction → EntailmentProfile
  | .periphrastic => r.subjectProfile
  | .lexicalVerb | .syntacticVerb => (reciprocalize r).subjectProfile

/-- The "I" reading over a transitive base (section 4.3): the sub-event reading must be
available and the subject must bear a sole role, a profile that is not complex. -/
def Construction.AllowsIReading (r : RoleList) (c : Construction) : Prop :=
  c.AllowsSubEventReading ∧ ¬ (c.subjectProfile r).IsComplexRole

/-- Sub-event availability is necessary for the "I" reading. -/
theorem subevents_necessary_for_I (h : ¬ c.AllowsSubEventReading) : ¬ c.AllowsIReading r :=
  λ hc => h hc.1

/-- A sole θ-role on the subject is necessary for the "I" reading. -/
theorem complex_role_blocks_I (h : (c.subjectProfile r).IsComplexRole) :
    ¬ c.AllowsIReading r :=
  λ hc => hc.2 h

/-- A periphrastic reciprocal over a non-complex subject role allows the "I" reading:
sub-events from the anaphor's plural operator and a sole role on the subject. -/
theorem periphrastic_allows_I (hs : ¬ r.subjectProfile.IsComplexRole) :
    Construction.periphrastic.AllowsIReading r :=
  ⟨rfl, hs⟩

/-- No plural events in the lexicon, so no sub-events and no "I" reading, for any base. -/
theorem lexical_no_I_reading (r : RoleList) :
    ¬ (Construction.ofFormation .lexical).AllowsIReading r :=
  subevents_necessary_for_I (by decide)

/-- In the syntax the bundled subject is a complex role, so there is no "I" reading though the
sub-event reading is available. -/
theorem syntactic_no_I_reading (ho : r.objectProfile = some o)
    (ha : 0 < r.subjectProfile.pAgentScore) (hp : 0 < o.pPatientScore) :
    ¬ (Construction.ofFormation .syntactic).AllowsIReading r :=
  complex_role_blocks_I (reciprocalize_isComplexRole ho ha hp)

/-- Neither reciprocal verb type allows the "I" reading, over any transitive base with an
agentive subject and an affected object. -/
theorem no_I_reading_either_formation (f : Formation) (ho : r.objectProfile = some o)
    (ha : 0 < r.subjectProfile.pAgentScore) (hp : 0 < o.pPatientScore) :
    ¬ (Construction.ofFormation f).AllowsIReading r := by
  cases f
  exacts [lexical_no_I_reading r, syntactic_no_I_reading ho ha hp]

/-- Over any transitive base whose subject role is agentive but not complex and whose object is
affected, the "I" reading is available in the periphrastic construction and only there. -/
theorem I_reading_iff_periphrastic (hs : ¬ r.subjectProfile.IsComplexRole)
    (ho : r.objectProfile = some o) (ha : 0 < r.subjectProfile.pAgentScore)
    (hp : 0 < o.pPatientScore) : c.AllowsIReading r ↔ c = .periphrastic := by
  cases c
  · exact iff_of_true (periphrastic_allows_I hs) rfl
  · exact iff_of_false (subevents_necessary_for_I (by decide)) (by decide)
  · exact iff_of_false (complex_role_blocks_I (reciprocalize_isComplexRole ho ha hp)) (by decide)

/-- Singular-event verbs lack the sub-event reading: both are the availability of plural events
at the composition locus (sections 2.2 to 2.3). -/
theorem singular_event_no_subevents (f : Formation) (h : Property.singularEvent.Holds f) :
    ¬ (Construction.ofFormation f).AllowsSubEventReading := by
  rw [Construction.AllowsSubEventReading, compositionLocus_ofFormation]
  exact h

end IReading

/-! ### The periphrastic source of sub-events (section 2.1)

The sub-event reading of periphrastic reciprocals comes from the anaphor's plural operator: on
a two-membered antecedent, [heim-lasnik-may-1991]'s each-other LF delivers exactly the two
directional relations, which sum to the accumulation reading. -/

section Periphrastic

variable {D E : Type*} [SemilatticeSup E] [DecidableEq D] {V : Set E} {ag th : E → D}
  {d₁ d₂ : D}

/-- On a pair antecedent, the each-other LF is the crossed directional pattern: strong
reciprocity at two members. -/
theorem eachOtherLF_pair (R : D → D → Prop) (hne : d₁ ≠ d₂) :
    HeimLasnikMay1991.eachOtherLF {d₁, d₂} R ↔ R d₁ d₂ ∧ R d₂ d₁ := by
  rw [HeimLasnikMay1991.eachOtherLF_iff_strongReciprocity]
  constructor
  · intro h
    exact ⟨h d₁ (by simp) d₂ (by simp) (Ne.symm hne), h d₂ (by simp) d₁ (by simp) hne⟩
  · rintro ⟨h₁, h₂⟩ a ha b hb hba
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hba
    · exact h₁
    · exact h₂
    · exact absurd rfl hba

/-- The periphrastic construction has the accumulation reading: the LF's two directional
relations, read off the base verb's events, sum to a plural reciprocal event (sections 2.1 to
2.2). -/
theorem accumulation_of_eachOtherLF (hne : d₁ ≠ d₂)
    (h : HeimLasnikMay1991.eachOtherLF {d₁, d₂} (λ a b => ∃ e ∈ V, ag e = a ∧ th e = b)) :
    ∃ e, AccumulationReading V ag th d₁ d₂ e := by
  obtain ⟨⟨e₁, he₁, ha₁, ht₁⟩, e₂, he₂, ha₂, ht₂⟩ := (eachOtherLF_pair _ hne).mp h
  exact ⟨e₁ ⊔ e₂, e₁, e₂, rfl, he₁, he₂, ha₁, ht₁, ha₂, ht₂⟩

end Periphrastic

/-! ### Count adverbials: five mutual against ten directional events (section 2.2)

Five rounds of kissing between Dan and Rina yield ten directional events. The Hebrew symmetric
verb packs each round into a group atom: *hitnašku xameš pe'amim* counts five mutual events
(`card_mutualEvent`), each recovering its round's directional events by dissolution
(`mutualEvent_down`) though they are not parts of the counted event
(`mutualEvent_not_subEventReading`), which is also why *\*hitnašku al ha-mecax* 'kissed on the
forehead' fails (15d). The French accumulation reading sums the two directional events instead:
the same five rounds (`card_accumulated`) keep both directional events accessible as proper
parts (`directional_lt_accumulated`), so *s'embrassèrent cinq fois* can also count ten
(16b). -/

section Counting

/-- The two participants. -/
inductive Kisser
  | dan | rina
  deriving DecidableEq

/-- The event domain: finite sets of atomic event markers, the left summand for directional
kissings and the right for group atoms. -/
abbrev KissEvent : Type := Finset (ℕ ⊕ ℕ)

noncomputable def kissGroups : GroupStructure KissEvent := GroupStructure.finsetModel ℕ

/-- The `i`-th directional kissing event. -/
def directional (i : ℕ) : KissEvent := {Sum.inl i}

theorem directional_injective : Function.Injective directional :=
  λ _ _ h => Sum.inl.inj (Finset.singleton_injective h)

/-- Round `j` kisses in both directions: Dan's is event `2j`, Rina's is event `2j + 1`. -/
def kiss : Set KissEvent := {e | ∃ i < 10, e = directional i}

/-- The even directional events, Dan's kissings of Rina. -/
def IsDansKissing (e : KissEvent) : Prop := ∃ j < 5, e = directional (2 * j)

instance : DecidablePred IsDansKissing := λ e =>
  decidable_of_iff (∃ j ∈ Finset.range 5, e = directional (2 * j)) (by simp [IsDansKissing])

/-- The agent of a directional kissing: Dan for the even events. -/
def kissAg (e : KissEvent) : Kisser := if IsDansKissing e then .dan else .rina

/-- The theme of a directional kissing: Rina for the even events. -/
def kissTh (e : KissEvent) : Kisser := if IsDansKissing e then .rina else .dan

/-- Round `j`'s two directional events form a crossed pair. -/
theorem crossedPair_round {j : ℕ} (hj : j < 5) :
    CrossedPair kiss kissAg kissTh .dan .rina (directional (2 * j)) (directional (2 * j + 1)) := by
  have hodd : ¬ IsDansKissing (directional (2 * j + 1)) := by
    rintro ⟨k, -, hk⟩
    have := directional_injective hk
    omega
  exact ⟨⟨2 * j, by omega, rfl⟩, ⟨2 * j + 1, by omega, rfl⟩,
    by rw [kissAg, ite_eq_left ⟨j, hj, rfl⟩], by rw [kissTh, ite_eq_left ⟨j, hj, rfl⟩],
    by rw [kissAg, ite_eq_right hodd], by rw [kissTh, ite_eq_right hodd]⟩

theorem directional_not_le {i k : ℕ} (h : i ≠ k) : ¬ directional i ≤ directional k :=
  λ hle => by
    have hmem : (Sum.inl i : ℕ ⊕ ℕ) ∈ ({Sum.inl k} : Finset (ℕ ⊕ ℕ)) :=
      Finset.singleton_subset_iff.mp hle
    rw [Finset.mem_singleton] at hmem
    exact h (Sum.inl.inj hmem)

/-- The `j`-th mutual kissing event: the round's two directional events packed as a group atom,
the Hebrew *hitnašku* denotation. -/
noncomputable def mutualEvent (j : Fin 5) : KissEvent :=
  kissGroups.up (directional (2 * j) ⊔ directional (2 * j + 1))

theorem mutualEvent_injective : Function.Injective mutualEvent := by
  intro j j' h
  have h2 := kissGroups.up_injective h
  have hv : ({Sum.inl (2 * (j : ℕ))} ∪ {Sum.inl (2 * (j : ℕ) + 1)} : Finset (ℕ ⊕ ℕ)) =
      {Sum.inl (2 * (j' : ℕ))} ∪ {Sum.inl (2 * (j' : ℕ) + 1)} := by
    simpa [directional, Finset.sup_eq_union] using h2
  have hmem : (Sum.inl (2 * (j : ℕ)) : ℕ ⊕ ℕ) ∈
      ({Sum.inl (2 * (j' : ℕ))} ∪ {Sum.inl (2 * (j' : ℕ) + 1)} : Finset (ℕ ⊕ ℕ)) := by
    rw [← hv]; simp
  simp only [Finset.mem_union, Finset.mem_singleton, Sum.inl.injEq] at hmem
  exact Fin.ext (by omega)

/-- (15): five mutual kissing events. -/
theorem card_mutualEvent : (Finset.univ.image mutualEvent).card = 5 := by
  rw [Finset.card_image_of_injective _ mutualEvent_injective]
  simp

/-- Ten directional kissing events underlie them. -/
theorem card_directional : ((Finset.range 10).image directional).card = 10 := by
  rw [Finset.card_image_of_injective _ directional_injective]
  simp

/-- Each mutual event dissolves to its round's directional events. -/
theorem mutualEvent_down (j : Fin 5) :
    kissGroups.down (mutualEvent j) = directional (2 * j) ⊔ directional (2 * j + 1) :=
  kissGroups.down_up _

/-- Yet the mutual event has no accessible parts: the count adverbial and locative modification
see one atomic event per round ((15a) and (15d)). -/
theorem mutualEvent_not_subEventReading (j : Fin 5) :
    ¬ SubEventReading kiss kissAg kissTh .dan .rina (mutualEvent j) :=
  λ hs => hs.not_atom (kissGroups.atom_up _)

/-- (16): the French accumulation event of round `j` is the plain sum. -/
def accumulated (j : Fin 5) : KissEvent := directional (2 * j) ⊔ directional (2 * j + 1)

/-- Five accumulation events, the five-count of (16b). -/
theorem card_accumulated : (Finset.univ.image accumulated).card = 5 := by
  have hinj : Function.Injective accumulated := by
    intro j j' h
    have hmem : (Sum.inl (2 * (j : ℕ)) : ℕ ⊕ ℕ) ∈
        ({Sum.inl (2 * (j' : ℕ))} ∪ {Sum.inl (2 * (j' : ℕ) + 1)} : Finset (ℕ ⊕ ℕ)) := by
      have hv := h
      simp only [accumulated, Finset.sup_eq_union, directional] at hv
      rw [← hv]; simp
    simp only [Finset.mem_union, Finset.mem_singleton, Sum.inl.injEq] at hmem
    exact Fin.ext (by omega)
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- The accumulation event keeps the sub-event reading: both directional events are accessible
((16b)'s ten-count, (16c)'s modification). -/
theorem accumulated_subEventReading (j : Fin 5) :
    SubEventReading kiss kissAg kissTh .dan .rina (accumulated j) :=
  subEventReading_of_crossedPair (directional_not_le (by omega)) (directional_not_le (by omega))
    (crossedPair_round j.isLt)

/-- Both directional events are proper parts of the accumulation event. -/
theorem directional_lt_accumulated (j : Fin 5) :
    directional (2 * j) < accumulated j ∧ directional (2 * j + 1) < accumulated j :=
  ⟨left_lt_sup.mpr (directional_not_le (by omega)),
    right_lt_sup.mpr (directional_not_le (by omega))⟩

end Counting

/-! ### The discontinuous construction: dyadic symmetric verbs (sections 7.4 to 7.5)

The discontinuous phrase is an argument (section 7.4), so lexical reciprocal verbs have two
realizations of one entry: monadic, with the pair-group subject, and dyadic, with subject and
comitative each contributing one member of the pair (section 7.5). Syntactic reciprocal verbs
have no listed symmetric entry to realize dyadically, which is why drifted *se battre* 'fight'
allows discontinuity in syntax-set French (section 7.2) while English *kiss* and *hug* resist it
lexically (footnote 32). -/

section Dyadic

variable {D E : Type*} [SemilatticeSup D] {GD : GroupStructure D} {Vsym : Set E} {d₁ d₂ : D}
  {e : E}

/-- The dyadic realization (section 7.5): the verb's events and complex role are those of the
monadic symmetric entry, the role taken at the subject and comitative's pair-group. -/
def DyadicReading (GD : GroupStructure D) (Vsym : Set E) (agTh : E → D) (d₁ d₂ : D) (e : E) :
    Prop :=
  e ∈ Vsym ∧ agTh e = GD.up (d₁ ⊔ d₂)

/-- Discontinuity is symmetric: *Dan corresponded with Rina* and *Rina corresponded with Dan*
describe the same events, the pair-group being unordered (section 7.1). -/
theorem dyadicReading_comm {agTh : E → D} :
    DyadicReading GD Vsym agTh d₁ d₂ e ↔ DyadicReading GD Vsym agTh d₂ d₁ e := by
  unfold DyadicReading
  rw [sup_comm]

/-- The discontinuous construction entails reciprocity between subject and oblique (section
7.1): the dyadic reading of a symmetric verb yields the crossed directional events. -/
theorem DyadicReading.underlying [SemilatticeSup E] {GE : GroupStructure E} {V : Set E}
    {ag th agTh : E → D} [h : Verb.SymmetricDenotation GD GE V ag th Vsym agTh] (hne : d₁ ≠ d₂)
    (hd : DyadicReading GD Vsym agTh d₁ d₂ e) : UnderlyingReading GE V ag th d₁ d₂ e :=
  underlying_of_symmetric hd.1 hne hd.2

end Dyadic

/-! ### The language sample (sections 2.4, 5 and 7) -/

/-- The paper's language sample: the abstract announces ten languages and eleven are named with
data. -/
inductive Language
  | hebrew | russian | hungarian | english
  | french | italian | spanish | czech | romanian | serboCroatian | bulgarian
  deriving DecidableEq, Fintype

/-- The locus at which a language forms its reciprocal verbs (section 2.4): the lexicon in
Hebrew, Russian, Hungarian and English, the syntax in the Romance languages, Czech,
Serbo-Croatian and Bulgarian. English's reciprocal verbs (intransitive *kiss*, *meet*,
*collide*) are lexicon-formed though the language's primary strategy is periphrastic, and
footnote 32 notes that *kiss* and *hug* nonetheless resist the discontinuous construction. -/
def Language.formation : Language → Formation
  | .hebrew | .russian | .hungarian | .english => .lexical
  | .french | .italian | .spanish | .czech | .romanian | .serboCroatian | .bulgarian => .syntactic

end Siloni2012
