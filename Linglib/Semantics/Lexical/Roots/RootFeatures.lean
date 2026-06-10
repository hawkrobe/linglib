/-!
# Root Quality Dimensions and Structural Entailments

Per-root content typology: ranges over root quality dimensions
([talmy-1988], [dowty-1991], [majid-boster-bowerman-2008],
[spalek-mcnally-2026]) and the binary entailment tetrad of
[beavers-koontz-garboden-2020].

The tetrad is framework-committed: [rappaport-hovav-levin-2010] reject
the entailment-feature framing (for them manner/result are
event-structural template properties, not root features); a
formalization of their account would be a sibling file with divergence
theorems.

## Main declarations

* `Range` — within-class variation along a quality dimension
* `RootProfile` — bundled quality dimensions (force, robustness,
  instrument, dimensionality, agent properties)
* `RootEntailments` — the B&K-G tetrad, with `WellFormed` collocational
  constraints and the canonical root types of their ch. 5 typology
-/

namespace Semantics.Lexical.Roots

/-! ### Range mechanism -/

/-- Acceptable values along a quality dimension.

    - `none`: the root is unconstrained on this dimension (says nothing)
    - `some [v₁, v₂, …]`: the root is compatible with exactly these values

    Roots are **regions**, not points: a verb like *tear* is compatible with
    a range of force levels, not a single one. -/
abbrev Range (α : Type) := Option (List α)

namespace Range

variable {α : Type}

def unconstrained : Range α := none

def only (vs : List α) : Range α := some vs

def isCompatible [BEq α] : Range α → α → Bool
  | none, _ => true
  | some vs, v => vs.contains v

def isConstrained : Range α → Bool
  | none => false
  | some _ => true

/-- Two ranges overlap if they share at least one value. -/
def overlaps [BEq α] : Range α → Range α → Bool
  | none, _ => true
  | _, none => true
  | some vs₁, some vs₂ => vs₁.any (vs₂.contains ·)

end Range

/-! ### Quality dimensions -/

/-- Magnitude of force involved in the event.

    [talmy-1988] identifies force magnitude as a core parameter of
    force-dynamic schemas. [spalek-mcnally-2026]: *tear* implies considerable
    force; *rasgar* implies less (enough to damage something flimsy). -/
inductive ForceLevel where
  | none      -- no force component (states)
  | low       -- gentle / minimal force
  | moderate  -- typical force
  | high      -- considerable / violent force
  deriving DecidableEq, Repr

/-- Spatial pattern of force application.

    [talmy-2000]: force vectors have directional parameters.
    [spalek-mcnally-2026]: *tear* implies contrary-direction force (pulling
    apart); *rasgar* implies unidirectional force (gash-like). -/
inductive ForceDirection where
  | none             -- no directional force component
  | unidirectional   -- linear / single-direction force (rasgar: gash)
  | bidirectional    -- contrary directions (tear: pulling apart)
  | omnidirectional  -- multi-directional (shatter: radiating fracture)
  deriving DecidableEq, Repr

/-- Material substantiality of the affected entity (patient).

    [spalek-mcnally-2026]: the primary dimension distinguishing
    *tear* (unrestricted) from *rasgar* (flimsy patients only). -/
inductive Robustness where
  | insubstantial  -- states, abstractions (silence, darkness)
  | flimsy         -- thin solids: fabric, paper, thin plastic
  | moderate       -- standard solids: rope, muscle, tendons
  | robust         -- thick solids: bread, cement, bone
  deriving DecidableEq, Repr

/-- Nature of the physical change produced by the event.

    Grounded in [levin-1993]'s class descriptions and [hale-keyser-1987] notion of "separation in material integrity":
    - 45.1 Break: loss of material integrity (break, crack, shatter, tear)
    - 45.2 Bend: change in shape without loss of integrity
    - 44 Destroy: total destruction (no specific resulting state)
    - 21 Cut: separation via instrument contact
    Refined by [beavers-koontz-garboden-2020] on CoS root types.
    UNVERIFIED: Levin chapter numbers cited from memory. -/
inductive ResultType where
  | separation      -- loss of integrity via pulling apart (tear)
  | surfaceBreach   -- gash-like damage to surface (rasgar)
  | fracture        -- breakage along stress lines (crack, break)
  | fragmentation   -- complete structural failure (shatter, smash)
  | deformation     -- shape change, integrity preserved (bend, fold)
  | totalDestruction -- entity ceases to exist as such (destroy, ruin)
  deriving DecidableEq, Repr

/-- Type of instrument used in the event.

    [majid-boster-bowerman-2008]: instrument type interacts with object
    properties to determine the predictability of separation locus (their
    Dimension 1). Sharp instruments yield predictable separations; blunt
    instruments and hands yield unpredictable separations.

    [levin-1993]: *cut* verbs specify their instrument
    (`instrumentSpec = true`); *break* verbs do not.
    UNVERIFIED: Levin chapter (§21 vs §45.1) cited from memory. -/
inductive InstrumentType where
  | sharpBlade    -- knife, scissors, saw, chisel (predictable separation)
  | bluntImpact   -- hammer, mallet, rock (unpredictable separation)
  | hands         -- bare hands (tearing, snapping, pulling apart)
  | none          -- no instrument / unspecified
  deriving DecidableEq, Repr

/-- Dimensionality of the affected object (patient).

    [majid-boster-bowerman-2008]: object dimensionality interacts
    with instrument type and manner of action to determine event
    categorization cross-linguistically. 1D objects (rope, stick) can
    be snapped; 2D objects (cloth, paper) can be torn; 3D objects
    (melon, pot) can be smashed. -/
inductive ObjectDimensionality where
  | oneD          -- elongated: rope, stick, twig, carrot, yarn
  | twoD          -- flat/flexible: cloth, paper, plate
  | threeD        -- solid/volumetric: melon, pot, box, orange
  deriving DecidableEq, Repr

/-- Whether the agent acts with volitional intent.

    [dowty-1991]: Proto-Agent entailment P1 = "volitional involvement
    in the event or state." [ausensi-yu-smith-2021]: killing verb roots impose
    specific intentionality requirements on the agent (*murder* requires
    intentional agent; *kill* does not).
    [levin-1993]: some *break* verbs "allow unintentional, action
    interpretations with body-part objects." -/
inductive Volitionality where
  | nonvolitional  -- unintentional / accidental
  | neutral        -- underspecified for volition
  | volitional     -- intentional / deliberate
  deriving DecidableEq, Repr

/-- Whether the action can be performed with care and control.

    [dowty-1991]: Proto-Agent entailment P2 = "sentience
    (and/or perception)," enabling controlled action.
    [spalek-mcnally-2026]: *tear* is compatible with careful action
    ("carefully tore the tin foil"); *rasgar* is not
    ("??rasgaron con cuidado el papel"). -/
inductive AgentControl where
  | incompatible  -- incompatible with careful/controlled action
  | neutral       -- underspecified for control
  | compatible    -- compatible with careful/controlled action
  deriving DecidableEq, Repr

/-- Within-class root content profile.

    Captures **quality** dimensions of root content — force, robustness,
    agent properties — as opposed to `RootEntailments`, which captures
    **structural** entailments (state, manner, result, cause).

    Each dimension is a `Range` of acceptable values; `none` means the
    root says nothing about that dimension (unconstrained). -/
structure RootProfile where
  /-- Force magnitude: [talmy-1988]. -/
  forceMag : Range ForceLevel := none
  /-- Force directionality: [talmy-2000], [spalek-mcnally-2026]. -/
  forceDir : Range ForceDirection := none
  /-- Patient material robustness: [spalek-mcnally-2026]. -/
  patientRob : Range Robustness := none
  /-- Type of physical change: [levin-1993], [beavers-koontz-garboden-2020]. -/
  resultType : Range ResultType := none
  /-- Agent volitionality: [dowty-1991] P1, [ausensi-yu-smith-2021]. -/
  agentVolition : Range Volitionality := none
  /-- Agent control: [dowty-1991] P2, [spalek-mcnally-2026]. -/
  agentControl : Range AgentControl := none
  /-- Instrument type the root selects for: [majid-boster-bowerman-2008].
      *cut* selects for sharp blades; *break* is unspecified. -/
  instrumentType : Range InstrumentType := none
  /-- Patient dimensionality: [majid-boster-bowerman-2008].
      *tear* selects for 2D objects (cloth, paper); *snap* for 1D (stick, twig). -/
  patientDim : Range ObjectDimensionality := none
  deriving BEq, Repr, Inhabited

/-! ### Root structural entailments -/

/-- Root-level structural entailments from [beavers-koontz-garboden-2020].

    B&KG argue against Bifurcation (roots never carry templatic
    meaning) and Manner/Result Complementarity (no root encodes both).
    Roots CAN entail states, change, and causation — notions
    traditionally reserved for templates (CAUSE, BECOME).

    The four features define a root typology (the book's ch. 5):
    - `state`: root describes a state (√FLAT, √CRACK, √DRY)
    - `manner`: root describes an action/manner (√JOG, √RUN, √HIT)
    - `result`: root entails change — low-scope *again* still
      presupposes a prior change
    - `cause`: root entails causation

    Constraints: `result → state` and `cause → result` (see
    `WellFormed`); the book presents both as definitional ("not
    root-specific stipulations"), mirroring conditions on templates. -/
structure RootEntailments where
  state  : Bool
  manner : Bool
  result : Bool
  cause  : Bool
  deriving DecidableEq, Repr

namespace RootEntailments

/-- If a root entails change (result), it entails a state that changes.
    [beavers-koontz-garboden-2020]: "+result entails being +state,
    since become′ entails something that has come about." -/
def ResultImpliesState (r : RootEntailments) : Prop :=
  r.result = true → r.state = true

instance (r : RootEntailments) : Decidable r.ResultImpliesState := by
  unfold ResultImpliesState; infer_instance

/-- If a root entails causation, it entails what is caused (a result).
    [beavers-koontz-garboden-2020]: "+cause entails being +result,
    since cause′ entails that there is a caused event." -/
def CauseImpliesResult (r : RootEntailments) : Prop :=
  r.cause = true → r.result = true

instance (r : RootEntailments) : Decidable r.CauseImpliesResult := by
  unfold CauseImpliesResult; infer_instance

/-- Well-formedness: both collocational constraints hold. -/
def WellFormed (r : RootEntailments) : Prop :=
  r.ResultImpliesState ∧ r.CauseImpliesResult

instance (r : RootEntailments) : Decidable r.WellFormed := by
  unfold WellFormed; infer_instance

/-! ### Canonical root types

The attested rows of the root typology in [beavers-koontz-garboden-2020]
ch. 5 (their example display (12), §5.4). -/

/-- +S −M −R −C: property concept roots (√FLAT, √DRY).
    Deadjectival COS verbs — the root names the result state.
    Complement position. -/
def propertyConcept : RootEntailments := ⟨true, false, false, false⟩

/-- +S −M +R −C: internally caused result roots (√BLOSSOM, √RUST).
    Root entails both a state and a change to that state, but not
    external causation. Complement position. -/
def pureResult : RootEntailments := ⟨true, false, true, false⟩

/-- +S −M +R +C: externally caused result roots (√CRACK, √BREAK).
    Root entails a state, change, AND causation. If roots subdivide by
    entailed causation, this may underlie Levin & Rappaport Hovav's
    (1995) externally vs internally caused change-of-state distinction
    ([beavers-koontz-garboden-2020], hedged as a possibility).
    Complement position. -/
def causativeResult : RootEntailments := ⟨true, false, true, true⟩

/-- −S +M −R −C: pure manner roots (√JOG, √RUN, √SWIM).
    Root specifies action manner without entailing any state.
    Adjoined position. -/
def pureManner : RootEntailments := ⟨false, true, false, false⟩

/-- +S +M +R −C: manner + result without cause. Well-formed per the
    constraints; [beavers-koontz-garboden-2020] leave its attestation
    an open question ("whether a change and a manner can exist together
    in a single meaning without causation"), with candidate witnesses
    *slide* and motion-in-sound-emission *buzz*. -/
def mannerResult : RootEntailments := ⟨true, true, true, false⟩

/-- +S +M +R +C: fully specified roots (√HAND adjoined, √DROWN and the
    other manner-of-killing roots in complement position;
    [beavers-koontz-garboden-2020] chs. 3–4). These are the attested
    MRC violators. The adjoined/complement contrast is carried by
    `Root.Position`, not by this struct. -/
def fullSpec : RootEntailments := ⟨true, true, true, true⟩

/-- −S −M −R −C: minimal roots — no structural entailments.
    Conservative default for classes not yet studied under B&KG's
    framework. Not a row in B&KG's typology (which only lists roots
    with at least one positive feature). -/
def minimal : RootEntailments := ⟨false, false, false, false⟩

/-! ### Canonical type well-formedness -/

theorem propertyConcept_wf : propertyConcept.WellFormed := by decide
theorem pureResult_wf : pureResult.WellFormed := by decide
theorem causativeResult_wf : causativeResult.WellFormed := by decide
theorem pureManner_wf : pureManner.WellFormed := by decide
theorem mannerResult_wf : mannerResult.WellFormed := by decide
theorem fullSpec_wf : fullSpec.WellFormed := by decide
theorem minimal_wf : minimal.WellFormed := by decide

/-! ### MRC violation detection -/

/-- Does this root violate Manner/Result Complementarity?
    [beavers-koontz-garboden-2020] ch. 4: some roots encode both manner
    and result. [rappaport-hovav-levin-2010] dispute this; the framing
    "violates MRC" presupposes MRC as a baseline norm — itself a
    framework commitment. -/
def ViolatesMRC (r : RootEntailments) : Prop :=
  r.manner = true ∧ r.result = true

instance (r : RootEntailments) : Decidable r.ViolatesMRC := by
  unfold ViolatesMRC; infer_instance

theorem fullSpec_violates_MRC : fullSpec.ViolatesMRC := by decide
theorem mannerResult_violates_MRC : mannerResult.ViolatesMRC := by decide
theorem pureResult_respects_MRC : ¬ pureResult.ViolatesMRC := by decide
theorem pureManner_respects_MRC : ¬ pureManner.ViolatesMRC := by decide
theorem causativeResult_respects_MRC : ¬ causativeResult.ViolatesMRC := by decide

end RootEntailments

/-! ### Derived properties -/

/-- Does a root profile constrain patient properties? -/
def RootProfile.constrainsPatient (rp : RootProfile) : Prop :=
  rp.patientRob.isConstrained = true

instance (rp : RootProfile) : Decidable rp.constrainsPatient :=
  inferInstanceAs (Decidable (_ = true))

/-- Do two root profiles overlap (share at least one compatible event)? -/
def RootProfile.overlaps (rp₁ rp₂ : RootProfile) : Prop :=
  rp₁.forceMag.overlaps rp₂.forceMag = true ∧
  rp₁.forceDir.overlaps rp₂.forceDir = true ∧
  rp₁.patientRob.overlaps rp₂.patientRob = true ∧
  rp₁.resultType.overlaps rp₂.resultType = true ∧
  rp₁.agentVolition.overlaps rp₂.agentVolition = true ∧
  rp₁.agentControl.overlaps rp₂.agentControl = true

instance (rp₁ rp₂ : RootProfile) : Decidable (rp₁.overlaps rp₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end Semantics.Lexical.Roots
