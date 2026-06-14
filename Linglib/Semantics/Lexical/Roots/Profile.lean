import Mathlib.Data.Fintype.Basic

/-!
# Root Quality Dimensions

Within-class root content profiles: ranges over quality dimensions —
force, robustness, instrument, dimensionality, agent properties. A
multi-paper synthesis ([talmy-1988], [talmy-2000], [dowty-1991],
[majid-boster-bowerman-2008], [spalek-mcnally-2026]); no single paper
carries this profile. Structural entailments (state, manner, result,
cause) are the separate `Root.FeatureSignature` (`Roots/Signature.lean`).

## Main declarations

* `Root.Profile.Range` — within-class variation along a dimension
* the dimension enums (`ForceLevel`, `Robustness`, `InstrumentType`, …)
* `Root.Profile` — the bundled profile
-/

namespace Verb

namespace Root.Profile

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

end Root.Profile

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

namespace Root

open Profile (Range)

/-- Within-class root content profile.

    Captures **quality** dimensions of root content — force, robustness,
    agent properties — as opposed to `Root.FeatureSignature`, which captures
    **structural** entailments (state, manner, result, cause).

    Each dimension is a `Range` of acceptable values; `none` means the
    root says nothing about that dimension (unconstrained). -/
structure Profile where
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

namespace Profile

/-- Does a root profile constrain patient properties? -/
def constrainsPatient (rp : Profile) : Prop :=
  rp.patientRob.isConstrained = true

instance (rp : Profile) : Decidable rp.constrainsPatient :=
  inferInstanceAs (Decidable (_ = true))

/-- Do two root profiles overlap (share at least one compatible event)? -/
def overlaps (rp₁ rp₂ : Profile) : Prop :=
  rp₁.forceMag.overlaps rp₂.forceMag = true ∧
  rp₁.forceDir.overlaps rp₂.forceDir = true ∧
  rp₁.patientRob.overlaps rp₂.patientRob = true ∧
  rp₁.resultType.overlaps rp₂.resultType = true ∧
  rp₁.agentVolition.overlaps rp₂.agentVolition = true ∧
  rp₁.agentControl.overlaps rp₂.agentControl = true

instance (rp₁ rp₂ : Profile) : Decidable (rp₁.overlaps rp₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end Profile

end Root

end Verb
