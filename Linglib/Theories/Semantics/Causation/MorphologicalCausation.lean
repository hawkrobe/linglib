import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.CoerciveImplication
import Linglib.Theories.Semantics.Lexical.Verb.AgentivityLattice
import Linglib.Core.RootDimensions

/-!
# Morphological Causation: Causative Construction Typology

@cite{comrie-1981} @cite{song-1996} @cite{shibatani-1976} @cite{dixon-2000} @cite{krejci-2012}

Causative constructions cross-linguistically vary along two orthogonal
axes: **morphological complexity** (compact → analytic) and **semantic
directness** (direct → indirect mediation). @cite{comrie-1981}'s central
generalization: more complex morphology correlates with more indirect
causation.

## Causer Type

Causative constructions are sensitive to the causer's **intentionality**
and ontological category. Following @cite{hafeez-2025}, we distinguish:
- **intentional human** (IHCr): volitional, controlled action → full agentivity
- **accidental human** (AHCr): unintentional, no control → marginal agentivity
- **natural force** (NFCr): non-human, non-volitional → non-agentive

The key dimension is intentionality, not ontological type: IHCr and AHCr
are both human but differ in agentivity. This three-way distinction drives
construction selection in Urdu and other languages.

## Causee/Affectee Type

The second participant in a causal chain (causee or affectee) varies in
four levels of control and animacy, following @cite{hafeez-2025}:
- **controlling human** (ContrHCEAF): exercises control over the induced action
- **physically impacted human** (PhysImpHCEAF): involuntarily coerced
- **psychologically impacted human** (PsychImpHCEAF): mentally affected
- **inanimate** (InanCEAF): no volition or sentience

## Agentivity

Agentivity decomposes into **intentionality × control** (following
@cite{van-valin-wilkins-1996}, @cite{bohnemeyer-2004}). Three degrees:
- **full**: intentional causer (IHCr)
- **marginal**: accidental human (AHCr) or natural force (NFCr)
- **partial/induced**: causee exercises control under causer's influence

## Bridges

- `CauserType.toCausalSource` → `CausalSource` (psych causation)
- `CauserType.toAgentivityNode` → `AgentivityNode` (agentivity lattice)
- `CauserType.volitionality` → `Volitionality` (root dimensions)
- `CauserType.agentivityDegree` → `AgentivityDegree`
- `CausativeConstruction` bundles complexity + mediation + causer/causee
  restrictions for cross-linguistic comparison
- `comrie_monotone` formalizes the compact-diffuse correlation

## Intransitivization (@cite{krejci-2012})

The causative/inchoative alternation has two directions: causativization
(adding an external cause) and intransitivization (removing or
coidentifying it). @cite{krejci-2012}'s central insight: intransitive
variants are NOT structurally uniform. **Reflexive** intransitives
(German *sich*, Hindi *apne-aap*) coidentify causer and causee,
retaining bieventive structure. **Anticausative** intransitives remove
the external cause entirely, yielding monoeventive structure.

- `IntransitivizationType` distinguishes reflexive, anticausative,
  and unmarked intransitivization
- Three diagnostics (*again*/*re-* ambiguity, negation over CAUSE,
  "by itself") all detect the causer position retained by reflexive
  intransitives but absent from anticausatives
-/

namespace Semantics.Causation.MorphologicalCausation

open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Lexical.Verb.AgentivityLattice (AgentivityNode)

-- ════════════════════════════════════════════════════
-- § 1. Causer Type (@cite{hafeez-2025}, @cite{comrie-1981})
-- ════════════════════════════════════════════════════

/-- Causer type distinguished by intentionality and ontological category.

    The key dimension is **intentionality**: IHCr and AHCr are both human
    but have fundamentally different agentivity profiles. NFCr is non-human
    and non-intentional.

    This three-way distinction drives construction selection in Urdu
    (@cite{hafeez-2025}) and other languages. -/
inductive CauserType where
  | intentionalHuman  -- IHCr: volitional, controlled action
  | accidentalHuman   -- AHCr: unintentional, no control
  | naturalForce      -- NFCr: non-human, non-volitional
  deriving DecidableEq, BEq, Repr

/-- Causee/affectee type: four levels of control and animacy.

    @cite{hafeez-2025}'s four-way distinction captures the gradient of
    the second participant's autonomy in a causal chain. A controlling
    causee reduces the causer's responsibility; an inanimate affectee
    increases it. -/
inductive CauseeAffecteeType where
  | controllingHuman   -- ContrHCEAF: exercises control over induced action
  | physImpactHuman     -- PhysImpHCEAF: physically coerced, no control
  | psychImpactHuman    -- PsychImpHCEAF: psychologically affected
  | inanimate           -- InanCEAF: no volition
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Agentivity Degree (@cite{hafeez-2025} Ch. 7)
-- ════════════════════════════════════════════════════

/-- Degree of agentivity, decomposed from intentionality × control.

    @cite{hafeez-2025}: "an intentional causer displays full agentivity,
    an accidental causer shows reduced or marginal agentivity, and a
    causee/affectee who exerts control displays induced or partial
    agentivity." -/
inductive AgentivityDegree where
  | full     -- intentional causer (IHCr)
  | marginal -- accidental (AHCr) or natural force (NFCr)
  | induced  -- causee exercises control under causer influence
  deriving DecidableEq, BEq, Repr

/-- Causer type determines causer's agentivity degree. -/
def CauserType.agentivityDegree : CauserType → AgentivityDegree
  | .intentionalHuman => .full
  | .accidentalHuman  => .marginal
  | .naturalForce     => .marginal

/-- A controlling causee has partial (induced) agentivity;
    all other causee types have no independent agentivity. -/
def CauseeAffecteeType.hasInducedAgentivity : CauseeAffecteeType → Bool
  | .controllingHuman => true
  | _                 => false

-- ════════════════════════════════════════════════════
-- § 3. Mediation (@cite{comrie-1981} §8.1)
-- ════════════════════════════════════════════════════

/-- Directness of causal mediation between causer and result.

    @cite{comrie-1981}: direct causation involves no intermediary — the
    causer brings about the result without an intervening causee
    decision or action. Indirect causation involves a mediating causee
    who retains some autonomy over the caused event. -/
inductive Mediation where
  | direct    -- causer directly brings about result
  | indirect  -- causer acts through intermediary/causee
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 4. Causative Complexity (@cite{comrie-1981} §8.2)
-- ════════════════════════════════════════════════════

/-- Morphological complexity of a causative construction.

    @cite{comrie-1981}'s compact-to-analytic continuum:
    - **lexical**: suppletive or idiosyncratic (kill/die, fell/fall)
    - **morphological**: productive affix (Urdu -aa, Japanese -(s)ase)
    - **periphrastic**: analytic multi-word (English "make X do Y")

    Ordered from compact to analytic. -/
inductive CausativeComplexity where
  | lexical
  | morphological
  | periphrastic
  deriving DecidableEq, BEq, Repr

instance : LT CausativeComplexity where
  lt a b := match a, b with
    | .lexical, .morphological => True
    | .lexical, .periphrastic => True
    | .morphological, .periphrastic => True
    | _, _ => False

instance : LE CausativeComplexity where
  le a b := a = b ∨ a < b

instance (a b : CausativeComplexity) : Decidable (a < b) :=
  match a, b with
  | .lexical, .morphological => isTrue trivial
  | .lexical, .periphrastic => isTrue trivial
  | .morphological, .periphrastic => isTrue trivial
  | .lexical, .lexical => isFalse (fun h => h)
  | .morphological, .lexical => isFalse (fun h => h)
  | .morphological, .morphological => isFalse (fun h => h)
  | .periphrastic, .lexical => isFalse (fun h => h)
  | .periphrastic, .morphological => isFalse (fun h => h)
  | .periphrastic, .periphrastic => isFalse (fun h => h)

-- ════════════════════════════════════════════════════
-- § 5. Causative Construction
-- ════════════════════════════════════════════════════

/-- A causative construction bundles morphological complexity with
    semantic parameters that govern its use.

    Each language's causative system is a list of `CausativeConstruction`
    values — e.g., Urdu has 7 (acceptability study), Japanese has 3. -/
structure CausativeConstruction where
  /-- Morphological complexity (compact → analytic) -/
  complexity : CausativeComplexity
  /-- Direct vs. indirect mediation -/
  mediation : Mediation
  /-- Restriction on causer type (none = unrestricted) -/
  causerRestriction : Option CauserType
  /-- Required causee/affectee type (none = unrestricted) -/
  causeeRestriction : Option CauseeAffecteeType
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 6. Semantic Prototype
-- ════════════════════════════════════════════════════

/-- A semantic prototype specifies the combination of semantic variables
    under which a construction receives its peak acceptability rating or
    is preferentially produced.

    @cite{hafeez-2025} Table 25: each construction has a (possibly empty)
    set of features that define its prototype. A prototype is "hypothesized"
    when the acceptability peak exceeds 50% ceiling for a scene type.

    Prototypes use both **positive** (e.g., [+IHCr]) and **negative**
    (e.g., [-IHCr]) feature specifications. Both are represented as lists:
    `presentCausers`/`absentCausers` etc. -/
structure SemanticPrototype where
  /-- Causer types that must be present (e.g., [+IHCr]) -/
  presentCausers : List CauserType
  /-- Causer types that must be absent (e.g., [-IHCr]) -/
  absentCausers : List CauserType
  /-- Causee/affectee types that must be present -/
  presentCausees : List CauseeAffecteeType
  /-- Causee/affectee types that must be absent -/
  absentCausees : List CauseeAffecteeType
  /-- Whether mediation is part of the prototype -/
  requiresMediation : Option Bool
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 7. Comrie's Generalization
-- ════════════════════════════════════════════════════

/-- **Comrie's monotonicity** (@cite{comrie-1981} §8.4): within a single
    language, if construction A is morphologically more compact than
    construction B, then A encodes more direct causation than B.

    Stated as a predicate on pairs: a system satisfies Comrie's
    generalization when complexity and mediation co-vary. -/
def comrie_monotone (c1 c2 : CausativeConstruction) : Prop :=
  c1.complexity < c2.complexity → c1.mediation = .direct ∨ c2.mediation = .indirect

-- ════════════════════════════════════════════════════
-- § 8. Bridges to Existing Infrastructure
-- ════════════════════════════════════════════════════

/-- All causer types are "external" in @cite{kim-2024}'s sense.

    The causer type taxonomy refines `CausalSource.external`:
    psych verbs' internal source (mental representation) is
    not a causer type in the morphological causation sense. -/
def CauserType.toCausalSource : CauserType → CausalSource
  | .intentionalHuman => .external
  | .accidentalHuman  => .external
  | .naturalForce     => .external

/-- Intentional human causers are volitional; accidental and natural
    force causers are not. -/
def CauserType.volitionality : CauserType → Volitionality
  | .intentionalHuman => .volitional
  | .accidentalHuman  => .nonvolitional
  | .naturalForce     => .nonvolitional

/-- Intentional human causers map to the agentive pole of the lattice
    (volition + sentience + instigation); accidental humans retain
    sentience but lack volition; natural forces have instigation only. -/
def CauserType.toAgentivityNode : CauserType → AgentivityNode
  | .intentionalHuman => ⟨true, true, true, false⟩   -- V+S+I
  | .accidentalHuman  => ⟨false, true, true, false⟩  -- S+I (sentient but not volitional)
  | .naturalForce     => ⟨false, false, true, false⟩  -- I only

-- ════════════════════════════════════════════════════
-- § 9. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- Intentional human causers have maximal agentivity among causer types. -/
theorem intentional_max_agentivity :
    (CauserType.toAgentivityNode .intentionalHuman).volition = true ∧
    (CauserType.toAgentivityNode .intentionalHuman).sentience = true ∧
    (CauserType.toAgentivityNode .intentionalHuman).instigation = true := ⟨rfl, rfl, rfl⟩

/-- Accidental human causers retain sentience but lack volition. -/
theorem accidental_sentient_not_volitional :
    (CauserType.toAgentivityNode .accidentalHuman).sentience = true ∧
    (CauserType.toAgentivityNode .accidentalHuman).volition = false := ⟨rfl, rfl⟩

/-- Natural force causers have only instigation (no sentience, no volition). -/
theorem naturalForce_instigation_only :
    (CauserType.toAgentivityNode .naturalForce) = ⟨false, false, true, false⟩ := rfl

/-- All causer types project to external `CausalSource`. -/
theorem all_causers_external (ct : CauserType) :
    ct.toCausalSource = .external := by cases ct <;> rfl

/-- IHCr has full agentivity; AHCr and NFCr have marginal. -/
theorem intentional_full_agentivity :
    CauserType.agentivityDegree .intentionalHuman = .full := rfl

theorem accidental_marginal_agentivity :
    CauserType.agentivityDegree .accidentalHuman = .marginal := rfl

theorem naturalForce_marginal_agentivity :
    CauserType.agentivityDegree .naturalForce = .marginal := rfl

/-- Controlling causees have induced agentivity;
    all other causee types do not. -/
theorem controlling_has_induced :
    CauseeAffecteeType.hasInducedAgentivity .controllingHuman = true := rfl

theorem inanimate_no_induced :
    CauseeAffecteeType.hasInducedAgentivity .inanimate = false := rfl

theorem physImpact_no_induced :
    CauseeAffecteeType.hasInducedAgentivity .physImpactHuman = false := rfl

-- ════════════════════════════════════════════════════
-- § 10. Intransitivization Type (@cite{krejci-2012})
-- ════════════════════════════════════════════════════

/-- How an alternating verb forms its intransitive variant.

    @cite{krejci-2012}'s central insight: intransitive variants of
    causative/inchoative alternation verbs are NOT structurally uniform.
    Two distinct operations produce surface intransitives:

    - **anticausative**: the external cause is removed entirely.
      The result is monoeventive: [BECOME [x STATE]].
      No causer position exists.
    - **reflexive**: the causer and causee are *coidentified* —
      a single participant fills both roles. The result is bieventive:
      [x ACT] CAUSE [BECOME [x STATE]] with causer = causee.
      Morphologically marked: German *sich*, Marathi *-un*.
    - **unmarked**: no morphological distinction (English *break*).
      Event structure must be diagnosed per-verb. -/
inductive IntransitivizationType where
  | anticausative   -- external cause removed; monoeventive result
  | reflexive       -- causer = causee (coidentification); bieventive
  | unmarked        -- no overt marking (English)
  deriving DecidableEq, BEq, Repr

/-- Reflexive intransitives retain the causer position (coidentified
    with the causee), preserving bieventive structure. Anticausatives
    remove the causer entirely, yielding monoeventive structure. -/
def IntransitivizationType.isBieventive : IntransitivizationType → Bool
  | .reflexive => true
  | _ => false

/-- Does the intransitive variant involve coidentification of causer
    and causee (a single participant in both roles)? -/
def IntransitivizationType.hasCoidentification : IntransitivizationType → Bool
  | .reflexive => true
  | _ => false

/-- "By itself" (*von selbst*, *apne-aap*, *aapo-aap*) is licensed
    when a causer position exists, even if coidentified with the
    causee. Anticausatives lack a causer position entirely.

    English unmarked intransitives also license "by itself"
    ("The door opened by itself"), because the unmarked form can be
    either reflexive or anticausative — only true anticausatives
    block the modifier. -/
def IntransitivizationType.licensesBySelf : IntransitivizationType → Bool
  | .anticausative => false
  | _ => true

-- § 10a. Bridge theorems

/-- Coidentification implies bieventivity (the causer position
    preserved by coidentification is what makes the structure bieventive). -/
theorem coidentification_implies_bieventive (it : IntransitivizationType) :
    it.hasCoidentification = true → it.isBieventive = true := by
  cases it <;> simp [IntransitivizationType.hasCoidentification,
    IntransitivizationType.isBieventive]

/-- Bieventivity implies "by itself" licensing (both track the
    presence of a causer position). -/
theorem bieventive_implies_bySelf (it : IntransitivizationType) :
    it.isBieventive = true → it.licensesBySelf = true := by
  cases it <;> simp [IntransitivizationType.isBieventive,
    IntransitivizationType.licensesBySelf]

/-- Anticausatives are monoeventive: no coidentification, no bieventivity,
    no "by itself" licensing. -/
theorem anticausative_monoeventive :
    IntransitivizationType.isBieventive .anticausative = false ∧
    IntransitivizationType.hasCoidentification .anticausative = false ∧
    IntransitivizationType.licensesBySelf .anticausative = false := ⟨rfl, rfl, rfl⟩

/-- Reflexive intransitives are bieventive with coidentification. -/
theorem reflexive_bieventive :
    IntransitivizationType.isBieventive .reflexive = true ∧
    IntransitivizationType.hasCoidentification .reflexive = true ∧
    IntransitivizationType.licensesBySelf .reflexive = true := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Causativizability Hierarchy (@cite{krejci-2012})
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012} proposes a cross-linguistic hierarchy of
    causativizability — the extent to which a morphological causative
    morpheme can apply to different verb classes:

        unaccusatives > middles/ingestives > unergatives > simple transitives

    The hierarchy is implicational: if a morpheme causativizes a
    higher verb class, it also causativizes all lower classes. This
    is validated across 12 languages in @cite{krejci-2012} Table 5.4. -/

/-- Cross-linguistic data on causativizability: which verb classes
    a given morphological causative morpheme can apply to. -/
structure CausativizabilityData where
  language : String
  morpheme : String
  unaccusative : Bool
  middlesIngestive : Bool := false
  unergative : Bool := false
  simpleTransitive : Bool := false
  deriving Repr, BEq

/-- The hierarchy is implicational: each level implies all lower levels.
    simpleTransitive → unergative → middlesIngestive → unaccusative. -/
def CausativizabilityData.respectsHierarchy (d : CausativizabilityData) : Bool :=
  (!d.simpleTransitive || d.unergative) &&
  (!d.unergative || d.middlesIngestive) &&
  (!d.middlesIngestive || d.unaccusative)

/-- Cross-linguistic causativizability data from @cite{krejci-2012} Table 5.4.
    Languages are ordered from narrowest to broadest causative scope. -/
def krejciLanguages : List CausativizabilityData :=
  [ { language := "Slave",            morpheme := "-h-",    unaccusative := true }
  , { language := "Mapudungun",       morpheme := "-'ɨm",   unaccusative := true }
  , { language := "Classical Nahuatl", morpheme := "-tia",  unaccusative := true }
  , { language := "Cora",             morpheme := "-te",    unaccusative := true
    , middlesIngestive := true }
  , { language := "Marathi",          morpheme := "-aw",    unaccusative := true
    , middlesIngestive := true }
  , { language := "Amharic",          morpheme := "a-",     unaccusative := true
    , middlesIngestive := true }
  , { language := "Ahtna",            morpheme := "-ɬ-",    unaccusative := true
    , middlesIngestive := true, unergative := true }
  , { language := "Tariana",          morpheme := "-i-ta",  unaccusative := true
    , middlesIngestive := true, unergative := true }
  , { language := "Malayalam",        morpheme := "-icc",   unaccusative := true
    , middlesIngestive := true, unergative := true }
  , { language := "Basque",           morpheme := "-arazi", unaccusative := true
    , middlesIngestive := true, unergative := true, simpleTransitive := true }
  , { language := "Dulong/Rawang",    morpheme := "-shv",   unaccusative := true
    , middlesIngestive := true, unergative := true, simpleTransitive := true }
  , { language := "Koyukon",          morpheme := "-ɬ-",    unaccusative := true
    , middlesIngestive := true, unergative := true, simpleTransitive := true }
  ]

/-- All 12 languages respect the implicational hierarchy. -/
theorem krejci_hierarchy_holds :
    krejciLanguages.all (·.respectsHierarchy) = true := by native_decide

end Semantics.Causation.MorphologicalCausation
