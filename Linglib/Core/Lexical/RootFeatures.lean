/-!
# Root Quality Dimensions and Structural Entailments
@cite{talmy-1988} @cite{talmy-2000} @cite{dowty-1991} @cite{beavers-koontz-garboden-2020} @cite{majid-boster-bowerman-2008}

Framework-agnostic infrastructure for characterizing verb root content.
Roots are **regions**, not points: each dimension is a `Range` of acceptable
values, reflecting that verbs are compatible with a range of event types.

## Quality dimensions (§§ 1–2)

Range-valued dimensions capturing within-class variation: force magnitude,
force direction, patient robustness, result type, instrument type, object
dimensionality, agent volition, agent control.

## Root structural entailments (§ 3)

From @cite{beavers-koontz-garboden-2020}: binary features capturing what the
root itself entails about event structure (state, manner, result, cause).

## Root structural position (§ 4)

From Marantz (2009) and @cite{beavers-koontz-garboden-2020}: whether the root
merges as complement or adjunct of v.
-/

-- ════════════════════════════════════════════════════
-- § 2. Range Mechanism
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 3. Quality Dimensions (Root-Specific Features)
-- ════════════════════════════════════════════════════

/-- Magnitude of force involved in the event.

    @cite{talmy-1988} identifies force magnitude as a core parameter of
    force-dynamic schemas. Spalek & McNally: *tear* implies considerable
    force; *rasgar* implies less (enough to damage something flimsy). -/
inductive ForceLevel where
  | none      -- no force component (states)
  | low       -- gentle / minimal force
  | moderate  -- typical force
  | high      -- considerable / violent force
  deriving DecidableEq, BEq, Repr

/-- Spatial pattern of force application.

    @cite{talmy-2000}: force vectors have directional parameters.
    Spalek & McNally: *tear* implies contrary-direction force (pulling
    apart); *rasgar* implies unidirectional force (gash-like). -/
inductive ForceDirection where
  | none             -- no directional force component
  | unidirectional   -- linear / single-direction force (rasgar: gash)
  | bidirectional    -- contrary directions (tear: pulling apart)
  | omnidirectional  -- multi-directional (shatter: radiating fracture)
  deriving DecidableEq, BEq, Repr

/-- Material substantiality of the affected entity (patient).

    Spalek & McNally (forthcoming): the primary dimension distinguishing
    *tear* (unrestricted) from *rasgar* (flimsy patients only). -/
inductive Robustness where
  | insubstantial  -- states, abstractions (silence, darkness)
  | flimsy         -- thin solids: fabric, paper, thin plastic
  | moderate       -- standard solids: rope, muscle, tendons
  | robust         -- thick solids: bread, cement, bone
  deriving DecidableEq, BEq, Repr

/-- Nature of the physical change produced by the event.

    Grounded in @cite{levin-1993}'s class descriptions and @cite{hale-keyser-1987} notion of "separation in material integrity":
    - 45.1 Break: loss of material integrity (break, crack, shatter, tear)
    - 45.2 Bend: change in shape without loss of integrity
    - 44 Destroy: total destruction (no specific resulting state)
    - 21 Cut: separation via instrument contact
    Refined by @cite{beavers-koontz-garboden-2020} on CoS root types. -/
inductive ResultType where
  | separation      -- loss of integrity via pulling apart (tear)
  | surfaceBreach   -- gash-like damage to surface (rasgar)
  | fracture        -- breakage along stress lines (crack, break)
  | fragmentation   -- complete structural failure (shatter, smash)
  | deformation     -- shape change, integrity preserved (bend, fold)
  | totalDestruction -- entity ceases to exist as such (destroy, ruin)
  deriving DecidableEq, BEq, Repr

/-- Type of instrument used in the event.

    @cite{majid-boster-bowerman-2008}: instrument type interacts with object
    properties to determine the predictability of separation locus (their
    Dimension 1). Sharp instruments yield predictable separations; blunt
    instruments and hands yield unpredictable separations.

    @cite{levin-1993}: *cut* verbs (§21) specify their instrument
    (`instrumentSpec = true`); *break* verbs (§45.1) do not. -/
inductive InstrumentType where
  | sharpBlade    -- knife, scissors, saw, chisel (predictable separation)
  | bluntImpact   -- hammer, mallet, rock (unpredictable separation)
  | hands         -- bare hands (tearing, snapping, pulling apart)
  | none          -- no instrument / unspecified
  deriving DecidableEq, BEq, Repr

/-- Dimensionality of the affected object (patient).

    @cite{majid-boster-bowerman-2008}: object dimensionality interacts
    with instrument type and manner of action to determine event
    categorization cross-linguistically. 1D objects (rope, stick) can
    be snapped; 2D objects (cloth, paper) can be torn; 3D objects
    (melon, pot) can be smashed. -/
inductive ObjectDimensionality where
  | oneD          -- elongated: rope, stick, twig, carrot, yarn
  | twoD          -- flat/flexible: cloth, paper, plate
  | threeD        -- solid/volumetric: melon, pot, box, orange
  deriving DecidableEq, BEq, Repr

/-- Whether the agent acts with volitional intent.

    @cite{dowty-1991}: Proto-Agent entailment P1 = "volitional involvement
    in the event or state." @cite{ausensi-yu-smith-2021}: killing verb roots impose
    specific intentionality requirements on the agent (*murder* requires
    intentional agent; *kill* does not).
    @cite{levin-1993}: some *break* verbs "allow unintentional, action
    interpretations with body-part objects." -/
inductive Volitionality where
  | nonvolitional  -- unintentional / accidental
  | neutral        -- underspecified for volition
  | volitional     -- intentional / deliberate
  deriving DecidableEq, BEq, Repr

/-- Whether the action can be performed with care and control.

    @cite{dowty-1991}: Proto-Agent entailment P2 = "sentience
    (and/or perception)," enabling controlled action.
    Spalek & McNally: *tear* is compatible with careful action
    ("carefully tore the tin foil"); *rasgar* is not
    ("??rasgaron con cuidado el papel"). -/
inductive AgentControl where
  | incompatible  -- incompatible with careful/controlled action
  | neutral       -- underspecified for control
  | compatible    -- compatible with careful/controlled action
  deriving DecidableEq, BEq, Repr

/-- Within-class root content profile.

    Captures **quality** dimensions of root content — force, robustness,
    agent properties — as opposed to `RootEntailments` (§ 3b), which
    captures **structural** entailments (state, manner, result, cause).

    Each dimension is a `Range` of acceptable values; `none` means the
    root says nothing about that dimension (unconstrained).

    Together with `MeaningComponents` (which defines the class),
    `LevinClass` (which identifies the class), and `RootEntailments`
    (which captures structural entailments), this gives a four-level
    characterization of a verb's semantic content:
    1. Class-defining meaning components (binary, from alternations)
    2. Class membership (Levin taxonomy)
    3. Root structural entailments (B&@cite{beavers-koontz-garboden-2020})
    4. Root-specific quality features (ranges, from detailed lexical analysis) -/
structure RootProfile where
  /-- Force magnitude: @cite{talmy-1988}. -/
  forceMag : Range ForceLevel := none
  /-- Force directionality: @cite{talmy-2000}, Spalek & McNally. -/
  forceDir : Range ForceDirection := none
  /-- Patient material robustness: Spalek & McNally. -/
  patientRob : Range Robustness := none
  /-- Type of physical change: @cite{levin-1993}, @cite{beavers-koontz-garboden-2020}. -/
  resultType : Range ResultType := none
  /-- Agent volitionality: @cite{dowty-1991} P1, @cite{ausensi-yu-smith-2021}. -/
  agentVolition : Range Volitionality := none
  /-- Agent control: @cite{dowty-1991} P2, Spalek & McNally. -/
  agentControl : Range AgentControl := none
  /-- Instrument type the root selects for: @cite{majid-boster-bowerman-2008}.
      *cut* selects for sharp blades; *break* is unspecified. -/
  instrumentType : Range InstrumentType := none
  /-- Patient dimensionality: @cite{majid-boster-bowerman-2008}.
      *tear* selects for 2D objects (cloth, paper); *snap* for 1D (stick, twig). -/
  patientDim : Range ObjectDimensionality := none
  deriving BEq, Repr, Inhabited

-- ════════════════════════════════════════════════════
-- § 3b. Root Structural Entailments (B&@cite{beavers-koontz-garboden-2020})
-- ════════════════════════════════════════════════════

/-- Root-level structural entailments from @cite{beavers-koontz-garboden-2020}.

    B&KG argue against Bifurcation (roots only contribute idiosyncratic
    content) and Manner/Result Complementarity (no root encodes both).
    Roots CAN entail states, change, and causation — notions traditionally
    reserved for templates (CAUSE, BECOME).

    The four features define a root typology (Table 12, p. 228):
    - `state`: root describes a state (√FLAT, √CRACK, √DRY)
    - `manner`: root describes an action/manner (√JOG, √RUN, √HIT)
    - `result`: root entails change — passes restitutive *again* test
    - `cause`: root entails causation

    Constraints: `result → state` and `cause → result` (see `wellFormed`).

    @cite{beavers-koontz-garboden-2020} -/
structure RootEntailments where
  state  : Bool
  manner : Bool
  result : Bool
  cause  : Bool
  deriving DecidableEq, BEq, Repr

namespace RootEntailments

/-- If a root entails change (result), it entails a state that changes.
    B&@cite{beavers-koontz-garboden-2020}: result entailments presuppose state entailments. -/
def resultImpliesState (r : RootEntailments) : Bool :=
  !r.result || r.state

/-- If a root entails causation, it entails what is caused (a result).
    B&@cite{beavers-koontz-garboden-2020}: cause entailments presuppose result entailments. -/
def causeImpliesResult (r : RootEntailments) : Bool :=
  !r.cause || r.result

/-- Well-formedness: both collocational constraints hold. -/
def wellFormed (r : RootEntailments) : Bool :=
  r.resultImpliesState && r.causeImpliesResult

/-! ### Canonical root types (B&KG Table 12) -/

/-- +S −M −R −C: property concept roots (√FLAT, √DRY).
    Deadjectival COS verbs — the root names the result state.
    Table 12, row 1, complement position. -/
def propertyConcept : RootEntailments := ⟨true, false, false, false⟩

/-- +S −M +R −C: internally caused result roots (√BLOSSOM, √RUST).
    Root entails both a state and a change to that state, but not
    external causation. Table 12, row 2, complement position. -/
def pureResult : RootEntailments := ⟨true, false, true, false⟩

/-- +S −M +R +C: externally caused result roots (√CRACK, √BREAK).
    Root entails a state, change, AND causation — the root inherently
    implies an external cause. Table 12, row 3, complement position.
    B&KG (p. 228): these "lexicalize crosslinguistically as basic
    causatives" unlike √BLOSSOM-type roots. -/
def causativeResult : RootEntailments := ⟨true, false, true, true⟩

/-- −S +M −R −C: pure manner roots (√JOG, √RUN, √SWIM).
    Root specifies action manner without entailing any state.
    Table 12, row 4, adjoined position. -/
def pureManner : RootEntailments := ⟨false, true, false, false⟩

/-- +S +M +R −C: manner + result without cause.
    Well-formed per the constraints but UNATTESTED in B&KG's Table 12
    (row 6 is empty in both positions). B&KG (p. 229): such roots
    "would essentially derive syntactically unergative verbs with pure
    change-of-state meanings." Defined for completeness. -/
def mannerResult : RootEntailments := ⟨true, true, true, false⟩

/-- +S +M +R +C: fully specified roots (√HAND, √DROWN, √CUT).
    B&KG Ch. 3–4: manner + caused change. These are the attested MRC
    violators. Table 12, row 7.
    √HAND sits in adjoined position, √DROWN in complement position;
    this structural difference is not captured here. -/
def fullSpec : RootEntailments := ⟨true, true, true, true⟩

/-- −S −M −R −C: minimal roots — no structural entailments.
    Conservative default for classes not yet studied under B&KG's
    framework. Not a row in Table 12 (which only lists roots with
    at least one positive feature). -/
def minimal : RootEntailments := ⟨false, false, false, false⟩

/-! ### Canonical type well-formedness -/

theorem propertyConcept_wf : propertyConcept.wellFormed = true := rfl
theorem pureResult_wf : pureResult.wellFormed = true := rfl
theorem causativeResult_wf : causativeResult.wellFormed = true := rfl
theorem pureManner_wf : pureManner.wellFormed = true := rfl
theorem mannerResult_wf : mannerResult.wellFormed = true := rfl
theorem fullSpec_wf : fullSpec.wellFormed = true := rfl
theorem minimal_wf : minimal.wellFormed = true := rfl

/-! ### MRC violation detection -/

/-- Does this root violate Manner/Result Complementarity?
    B&KG Ch. 4: some roots encode both manner and result. -/
def violatesMRC (r : RootEntailments) : Bool := r.manner && r.result

theorem fullSpec_violates_MRC : fullSpec.violatesMRC = true := rfl
theorem mannerResult_violates_MRC : mannerResult.violatesMRC = true := rfl
theorem pureResult_respects_MRC : pureResult.violatesMRC = false := rfl
theorem pureManner_respects_MRC : pureManner.violatesMRC = false := rfl
theorem causativeResult_respects_MRC : causativeResult.violatesMRC = false := rfl

end RootEntailments

-- ════════════════════════════════════════════════════
-- § 3c. Root Structural Position
-- ════════════════════════════════════════════════════

/-- Structural attachment position of a verb root, following
    Marantz (2009a;b, 2013) as systematized by
    @cite{beavers-koontz-garboden-2020} Table 12.

    - **Complement**: root merges as complement of v (inside VP).
      Fills the result-state slot. Change-of-state roots: √FLAT,
      √CRACK, √BLOSSOM, √DROWN.
    - **Adjoined**: root merges as adjunct to v (outside VP).
      Modifies the causing event. Manner/activity roots: √JOG,
      √TOSS, √HAND.

    This distinction is structurally significant beyond root typology:
    it determines vVPE eligibility (@cite{kalyakin-2026}), scope of
    result-state modifiers, and the restitutive/repetitive *again*
    ambiguity (@cite{beavers-koontz-garboden-2020}, @cite{merchant-2013}). -/
inductive RootPosition where
  | complement  -- under v: fills result/state slot (inside VP)
  | adjoined    -- to v: modifies causing event (outside VP)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 7. Derived Properties
-- ════════════════════════════════════════════════════

/-- Does a root profile constrain patient properties? -/
def RootProfile.constrainsPatient (rp : RootProfile) : Bool :=
  rp.patientRob.isConstrained

/-- Do two root profiles overlap (share at least one compatible event)? -/
def RootProfile.overlaps (rp₁ rp₂ : RootProfile) : Bool :=
  rp₁.forceMag.overlaps rp₂.forceMag &&
  rp₁.forceDir.overlaps rp₂.forceDir &&
  rp₁.patientRob.overlaps rp₂.patientRob &&
  rp₁.resultType.overlaps rp₂.resultType &&
  rp₁.agentVolition.overlaps rp₂.agentVolition &&
  rp₁.agentControl.overlaps rp₂.agentControl
