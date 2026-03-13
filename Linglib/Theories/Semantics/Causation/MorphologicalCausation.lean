import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.CoerciveImplication
import Linglib.Theories.Semantics.Lexical.Verb.AgentivityLattice
import Linglib.Core.RootDimensions

/-!
# Morphological Causation: Causative Construction Typology

@cite{comrie-1981} @cite{song-1996} @cite{shibatani-1976} @cite{dixon-2000}

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
    when the acceptability peak exceeds 50% ceiling for a scene type. -/
structure SemanticPrototype where
  /-- Required causer type features (present = required, absent = any) -/
  causerFeatures : List CauserType
  /-- Required causee/affectee features -/
  causeeFeatures : List CauseeAffecteeType
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

end Semantics.Causation.MorphologicalCausation
