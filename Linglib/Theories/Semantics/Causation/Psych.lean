/-!
# Psych Verb Causation (@cite{kim-2024} UPH)

@cite{kim-2024}

Types for the Uniform Projection Hypothesis: all Class II (object experiencer)
psych verbs uniformly project Cause + Experiencer. The eventive/stative split
comes from the *causal source*: mind-external percepts (eventive, extensional
subject) vs mind-internal representations (stative, intensional subject).

Subject Matter (T/SM) is a causal adjunct mapping to the onset of the causal
chain; its incompatibility with an overt Cause follows from the Onset Condition.

## Key types

| Type | Purpose |
|------|---------|
| `CausalSource` | External (percept) vs internal (representation) |
| `CausalChainPosition` | Onset vs terminus in a two-link chain |

## Key results

- `subjectIntensional`: internal source → intensional subject position
- `onsetCondition`: causal adjuncts map to onset position
- T/SM restriction: Cause occupies onset, SM wants onset → conflict

-/

namespace Semantics.Causation.PsychCausation

/-- Source of causation for psych causatives (@cite{kim-2024} UPH).

    Class II psych verbs uniformly project Cause + Experiencer.
    The aspectual distinction (eventive vs stative) comes from
    what the Cause picks out:
    - `.external`: mind-external percept/event ("the noise frightened John")
    - `.internal`: mind-internal representation via "stative causation" /
      maintenance relation — an existing mental
      representation maintains the experiencer's psychological state
      ("the problem concerns John") -/
inductive CausalSource where
  | external  -- percept/event → eventive reading
  | internal  -- mental representation (stative causation/maintenance) → stative reading
  deriving DecidableEq, Repr

/-- Position in a two-link causal chain.

    Class II psych verbs involve a causal chain from cause (onset)
    to experiencer's mental state change (terminus). -/
inductive CausalChainPosition where
  | onset      -- first link: external cause or representation
  | terminus   -- final link: experiencer's mental state change
  deriving DecidableEq, Repr

/-- The Onset Condition: causal adjuncts (including Subject Matter)
    must map to the onset position of the causal chain.

    This is the key to the T/SM restriction: if Cause already occupies
    onset and SM also requires onset, they conflict. -/
def onsetCondition (pos : CausalChainPosition) : Bool :=
  pos == .onset

/-- Internal causal source implies the subject position is intensional.

    When the cause is a mind-internal representation, the subject's
    referent depends on the experiencer's knowledge state, so
    substitution of co-referential terms can fail (Cicero/Tully). -/
def subjectIntensional (src : CausalSource) : Bool :=
  match src with
  | .internal => true
  | .external => false

/-- Is this a stative Class II reading? Stative ↔ internal source. -/
def CausalSource.isStative : CausalSource → Bool
  | .internal => true
  | .external => false

/-- Is this an eventive Class II reading? Eventive ↔ external source. -/
def CausalSource.isEventive : CausalSource → Bool
  | .external => true
  | .internal => false

-- ════════════════════════════════════════════════════
-- § Stimulus Subtype (@cite{pesetsky-1995})
-- ════════════════════════════════════════════════════

/-- @cite{pesetsky-1995}'s subdivision of the stimulus role.

    Class II psych verbs take a stimulus/cause argument, but
    Pesetsky shows this role has two semantically distinct subtypes:

    - **Target (T)**: what the emotion is *directed at*
      "John fears the dog" — the dog is the target of fear
    - **SubjectMatter (SM)**: what the emotion is *about*
      "John worries about the exam" — the exam is the subject matter

    The T/SM distinction controls PP frame selection (*of* for T,
    *about* for SM), cooccurrence with Cause (SM and Cause conflict
    via the Onset Condition), and the naturalness of the experiencer
    predicate (T-predicates are "natural", SM-predicates are
    "arbitrary" in Pesetsky's terms).

    @cite{pesetsky-1995} argues that the T/SM distinction has syntactic
    consequences: Target and Subject Matter cannot cooccur with Causer
    in the same predicate (the T/SM restriction, explained via the
    Head Movement Constraint). -/
inductive StimulusType where
  | target        -- T: directed-at ("fears the dog")
  | subjectMatter -- SM: about ("worries about the exam")
  deriving DecidableEq, Repr

/-- Target stimuli select *of*-PP complements. -/
def StimulusType.ppFrame : StimulusType → String
  | .target        => "of"
  | .subjectMatter => "about"

/-- Subject Matter conflicts with overt Cause (Onset Condition).
    Target does not — it occupies a different position in the
    causal chain. -/
def StimulusType.conflictsWithCause : StimulusType → Bool
  | .target        => false
  | .subjectMatter => true

-- ════════════════════════════════════════════════════
-- § CausalSource → StimulusType Derivation
-- ════════════════════════════════════════════════════

/-- Derive stimulus subtype from causal source.

    For Class II psych verbs, the T/SM distinction is *determined by*
    the causal source:

    - External percept → Target: the percept IS the direct object of
      the emotion ("the noise frightened John" → frightened *of* the noise)
    - Internal representation → Subject Matter: the representation is
      what the emotion is *about* ("the problem concerns John" →
      concerned *about* the problem)

    For Class I verbs (fear, enjoy), T/SM is a per-use property selected
    by PP frame (*of* vs *about*), not a lexical property. A single Class I
    verb like "afraid" can take either T ("afraid of dogs") or SM
    ("afraid about the outcome"). So this derivation applies only to
    Class II, where the stimulus is the subject and the causal source
    is a lexical property. -/
def CausalSource.toStimulusType : CausalSource → StimulusType
  | .external => .target
  | .internal => .subjectMatter

/-- External causal source derives Target stimulus. -/
theorem external_is_target :
    CausalSource.toStimulusType .external = .target := rfl

/-- Internal causal source derives Subject Matter stimulus. -/
theorem internal_is_subjectMatter :
    CausalSource.toStimulusType .internal = .subjectMatter := rfl

/-- Derived SM conflicts with Cause; derived T does not.
    This connects the Onset Condition to the causal source:
    internal-source verbs can't cooccur with overt Cause because
    their derived SM stimulus competes for the onset position. -/
theorem sm_cause_conflict_from_source :
    (CausalSource.toStimulusType .internal).conflictsWithCause = true ∧
    (CausalSource.toStimulusType .external).conflictsWithCause = false :=
  ⟨rfl, rfl⟩

/-- The causal source determines three properties simultaneously:
    stimulus subtype, PP frame, and Cause cooccurrence. -/
theorem source_determines_stimulus_properties :
    -- External → T, "of", no conflict
    CausalSource.toStimulusType .external = .target ∧
    (CausalSource.toStimulusType .external).ppFrame = "of" ∧
    (CausalSource.toStimulusType .external).conflictsWithCause = false ∧
    -- Internal → SM, "about", conflict
    CausalSource.toStimulusType .internal = .subjectMatter ∧
    (CausalSource.toStimulusType .internal).ppFrame = "about" ∧
    (CausalSource.toStimulusType .internal).conflictsWithCause = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Semantics.Causation.PsychCausation
