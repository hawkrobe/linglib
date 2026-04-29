/-!
# Root Quality Dimensions and Structural Entailments
@cite{talmy-1988} @cite{talmy-2000} @cite{dowty-1991} @cite{beavers-koontz-garboden-2020} @cite{majid-boster-bowerman-2008}

Per-root content typology: ranges over root quality dimensions, the
@cite{beavers-koontz-garboden-2020} (B&KG) binary entailment tetrad,
and Marantz-style root structural position.

## Provenance

Moved from `Core/Lexical/RootFeatures.lean` in the cleanup that
dissolved `Core/Lexical/`. The file's original docstring claimed
"framework-agnostic infrastructure" but its load-bearing content
(B&KG's binary [state, manner, result, cause] tetrad in §3, Marantz's
complement-vs-adjunct merge position in §4) is framework-specific:
B&KG's tetrad is the thesis of @cite{beavers-koontz-garboden-2020},
explicitly opposed to Rappaport Hovav & Levin's template-based
account (@cite{rappaport-hovav-levin-2010}) and to Embick's
contextual-allosemy framework. Promoting these features to a named
Theories file (sibling of `Roots/Basic.lean`, `Roots/Typology.lean`,
`Roots/Template.lean`) makes the framework commitment legible.

**Sibling slots intentionally unfilled.** `Theories/Semantics/Verb/Roots/RappaportHovavLevin.lean`
is the natural home for the template-based competitor account
(@cite{rappaport-hovav-levin-2010}, @cite{rappaport-hovav-levin-2024}).
@cite{rappaport-hovav-levin-2010} reject the very feature setup
encoded here; their position is that manner/result are
*event-structural templates*, not root features. The slot is empty
in this restructure; future work formalizing RH&L's framework
should land there as a sibling, with refutation theorems showing
where B&KG and RH&L disagree on attested verbs.

## Sections

- §1 Range mechanism — `Range α := Option (List α)` for within-class variation
- §2 Quality dimensions — force, robustness, instrument, dimensionality, agent properties
- §3 B&KG root structural entailments — state/manner/result/cause + collocational constraints
- §4 Marantz root structural position — complement vs adjunct of v
- §5 Derived properties on `RootProfile`

## Citation hygiene notes

- B&KG page references (e.g., "Table 12, p. 228", "p. 229") are flagged
  `UNVERIFIED:` per CLAUDE.md ("Never cite specific page ranges from
  memory"). Verify against the published @cite{beavers-koontz-garboden-2020}
  monograph before treating as authoritative.
- Inline `Marantz (2009a;b, 2013)` references in the original file
  lacked bib entries. The substantive claim — that roots merge as
  complement or adjunct of v — is uncontroversially attributed to
  Marantz across the DM literature, but the specific publication
  citations need verification before adding to `references.bib`.
-/

namespace Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Range Mechanism
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
-- § 2. Quality Dimensions (Root-Specific Features)
-- ════════════════════════════════════════════════════

/-- Magnitude of force involved in the event.

    @cite{talmy-1988} identifies force magnitude as a core parameter of
    force-dynamic schemas. @cite{spalek-mcnally-2026}: *tear* implies considerable
    force; *rasgar* implies less (enough to damage something flimsy). -/
inductive ForceLevel where
  | none      -- no force component (states)
  | low       -- gentle / minimal force
  | moderate  -- typical force
  | high      -- considerable / violent force
  deriving DecidableEq, Repr

/-- Spatial pattern of force application.

    @cite{talmy-2000}: force vectors have directional parameters.
    @cite{spalek-mcnally-2026}: *tear* implies contrary-direction force (pulling
    apart); *rasgar* implies unidirectional force (gash-like). -/
inductive ForceDirection where
  | none             -- no directional force component
  | unidirectional   -- linear / single-direction force (rasgar: gash)
  | bidirectional    -- contrary directions (tear: pulling apart)
  | omnidirectional  -- multi-directional (shatter: radiating fracture)
  deriving DecidableEq, Repr

/-- Material substantiality of the affected entity (patient).

    @cite{spalek-mcnally-2026}: the primary dimension distinguishing
    *tear* (unrestricted) from *rasgar* (flimsy patients only). -/
inductive Robustness where
  | insubstantial  -- states, abstractions (silence, darkness)
  | flimsy         -- thin solids: fabric, paper, thin plastic
  | moderate       -- standard solids: rope, muscle, tendons
  | robust         -- thick solids: bread, cement, bone
  deriving DecidableEq, Repr

/-- Nature of the physical change produced by the event.

    Grounded in @cite{levin-1993}'s class descriptions and @cite{hale-keyser-1987} notion of "separation in material integrity":
    - 45.1 Break: loss of material integrity (break, crack, shatter, tear)
    - 45.2 Bend: change in shape without loss of integrity
    - 44 Destroy: total destruction (no specific resulting state)
    - 21 Cut: separation via instrument contact
    Refined by @cite{beavers-koontz-garboden-2020} on CoS root types.
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

    @cite{majid-boster-bowerman-2008}: instrument type interacts with object
    properties to determine the predictability of separation locus (their
    Dimension 1). Sharp instruments yield predictable separations; blunt
    instruments and hands yield unpredictable separations.

    @cite{levin-1993}: *cut* verbs specify their instrument
    (`instrumentSpec = true`); *break* verbs do not.
    UNVERIFIED: Levin chapter (§21 vs §45.1) cited from memory. -/
inductive InstrumentType where
  | sharpBlade    -- knife, scissors, saw, chisel (predictable separation)
  | bluntImpact   -- hammer, mallet, rock (unpredictable separation)
  | hands         -- bare hands (tearing, snapping, pulling apart)
  | none          -- no instrument / unspecified
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Whether the action can be performed with care and control.

    @cite{dowty-1991}: Proto-Agent entailment P2 = "sentience
    (and/or perception)," enabling controlled action.
    @cite{spalek-mcnally-2026}: *tear* is compatible with careful action
    ("carefully tore the tin foil"); *rasgar* is not
    ("??rasgaron con cuidado el papel"). -/
inductive AgentControl where
  | incompatible  -- incompatible with careful/controlled action
  | neutral       -- underspecified for control
  | compatible    -- compatible with careful/controlled action
  deriving DecidableEq, Repr

/-- Within-class root content profile.

    Captures **quality** dimensions of root content — force, robustness,
    agent properties — as opposed to `RootEntailments` (§ 3), which
    captures **structural** entailments (state, manner, result, cause).

    Each dimension is a `Range` of acceptable values; `none` means the
    root says nothing about that dimension (unconstrained).

    Together with `MeaningComponents` (which defines the class),
    `LevinClass` (which identifies the class), and `RootEntailments`
    (which captures structural entailments), this gives a four-level
    characterization of a verb's semantic content:
    1. Class-defining meaning components (binary, from alternations)
    2. Class membership (Levin taxonomy)
    3. Root structural entailments (@cite{beavers-koontz-garboden-2020})
    4. Root-specific quality features (ranges, from detailed lexical analysis) -/
structure RootProfile where
  /-- Force magnitude: @cite{talmy-1988}. -/
  forceMag : Range ForceLevel := none
  /-- Force directionality: @cite{talmy-2000}, @cite{spalek-mcnally-2026}. -/
  forceDir : Range ForceDirection := none
  /-- Patient material robustness: @cite{spalek-mcnally-2026}. -/
  patientRob : Range Robustness := none
  /-- Type of physical change: @cite{levin-1993}, @cite{beavers-koontz-garboden-2020}. -/
  resultType : Range ResultType := none
  /-- Agent volitionality: @cite{dowty-1991} P1, @cite{ausensi-yu-smith-2021}. -/
  agentVolition : Range Volitionality := none
  /-- Agent control: @cite{dowty-1991} P2, @cite{spalek-mcnally-2026}. -/
  agentControl : Range AgentControl := none
  /-- Instrument type the root selects for: @cite{majid-boster-bowerman-2008}.
      *cut* selects for sharp blades; *break* is unspecified. -/
  instrumentType : Range InstrumentType := none
  /-- Patient dimensionality: @cite{majid-boster-bowerman-2008}.
      *tear* selects for 2D objects (cloth, paper); *snap* for 1D (stick, twig). -/
  patientDim : Range ObjectDimensionality := none
  deriving BEq, Repr, Inhabited

-- ════════════════════════════════════════════════════
-- § 3. Root Structural Entailments (@cite{beavers-koontz-garboden-2020})
-- ════════════════════════════════════════════════════

/-- Root-level structural entailments from @cite{beavers-koontz-garboden-2020}.

    B&KG argue against Bifurcation (roots only contribute idiosyncratic
    content) and Manner/Result Complementarity (no root encodes both).
    Roots CAN entail states, change, and causation — notions traditionally
    reserved for templates (CAUSE, BECOME).

    The four features define a root typology:
    - `state`: root describes a state (√FLAT, √CRACK, √DRY)
    - `manner`: root describes an action/manner (√JOG, √RUN, √HIT)
    - `result`: root entails change — passes restitutive *again* test
    - `cause`: root entails causation

    Constraints: `result → state` and `cause → result` (see `WellFormed`).

    @cite{rappaport-hovav-levin-2010} reject this entailment-feature
    framing; for them manner/result are event-structural template
    properties, not root features. The competitor analysis would live
    in `Theories/Semantics/Verb/Roots/RappaportHovavLevin.lean` (planned).

    UNVERIFIED: B&KG Table 12 reference cited from memory. -/
structure RootEntailments where
  state  : Bool
  manner : Bool
  result : Bool
  cause  : Bool
  deriving DecidableEq, Repr

namespace RootEntailments

/-- If a root entails change (result), it entails a state that changes.
    @cite{beavers-koontz-garboden-2020}: result entailments presuppose state entailments. -/
def ResultImpliesState (r : RootEntailments) : Prop :=
  r.result = true → r.state = true

instance (r : RootEntailments) : Decidable r.ResultImpliesState := by
  unfold ResultImpliesState; infer_instance

/-- If a root entails causation, it entails what is caused (a result).
    @cite{beavers-koontz-garboden-2020}: cause entailments presuppose result entailments. -/
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

UNVERIFIED: Specific row references to @cite{beavers-koontz-garboden-2020}
Table 12 are cited from memory. The 7 canonical types below cover
B&KG's typology; verify row numbers against the published monograph
before treating as definitive. -/

/-- +S −M −R −C: property concept roots (√FLAT, √DRY).
    Deadjectival COS verbs — the root names the result state.
    Complement position. -/
def propertyConcept : RootEntailments := ⟨true, false, false, false⟩

/-- +S −M +R −C: internally caused result roots (√BLOSSOM, √RUST).
    Root entails both a state and a change to that state, but not
    external causation. Complement position. -/
def pureResult : RootEntailments := ⟨true, false, true, false⟩

/-- +S −M +R +C: externally caused result roots (√CRACK, √BREAK).
    Root entails a state, change, AND causation — the root inherently
    implies an external cause. Complement position.
    @cite{beavers-koontz-garboden-2020}: these "lexicalize crosslinguistically as basic
    causatives" unlike √BLOSSOM-type roots. -/
def causativeResult : RootEntailments := ⟨true, false, true, true⟩

/-- −S +M −R −C: pure manner roots (√JOG, √RUN, √SWIM).
    Root specifies action manner without entailing any state.
    Adjoined position. -/
def pureManner : RootEntailments := ⟨false, true, false, false⟩

/-- +S +M +R −C: manner + result without cause.
    Well-formed per the constraints but UNATTESTED in B&KG's typology.
    Such roots "would essentially derive syntactically unergative verbs
    with pure change-of-state meanings." Defined for completeness. -/
def mannerResult : RootEntailments := ⟨true, true, true, false⟩

/-- +S +M +R +C: fully specified roots (√HAND, √DROWN, √CUT).
    @cite{beavers-koontz-garboden-2020} Ch. 3–4: manner + caused change. These are the attested MRC
    violators. √HAND sits in adjoined position, √DROWN in complement
    position; this structural difference is not captured here. -/
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
    @cite{beavers-koontz-garboden-2020} Ch. 4: some roots encode both manner and result.
    @cite{rappaport-hovav-levin-2010} dispute this; the framing
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

-- ════════════════════════════════════════════════════
-- § 4. Root Structural Position (Marantz / B&KG)
-- ════════════════════════════════════════════════════

/-- Structural attachment position of a verb root. Following the
    Distributed-Morphology tradition (Marantz; systematized by
    @cite{beavers-koontz-garboden-2020}):

    - **Complement**: root merges as complement of v (inside VP).
      Fills the result-state slot. Change-of-state roots: √FLAT,
      √CRACK, √BLOSSOM, √DROWN.
    - **Adjoined**: root merges as adjunct to v (outside VP).
      Modifies the causing event. Manner/activity roots: √JOG,
      √TOSS, √HAND.

    This distinction is structurally significant beyond root typology:
    it determines vVPE eligibility (@cite{kalyakin-2026}), scope of
    result-state modifiers, and the restitutive/repetitive *again*
    ambiguity (@cite{beavers-koontz-garboden-2020}, @cite{merchant-2013}).

    UNVERIFIED: The Marantz publications usually cited in this
    context (DM "Phases and words" handout, "No Escape from Syntax",
    "Verbal argument structure" chapter) have not been added to
    `references.bib`. The substantive claim is uncontroversially
    attributed to Marantz across DM, but specific publication
    references should be verified before citing.

    Note: this is the canonical `RootPosition` for the `Roots/`
    subdirectory; `Template.lean` will be updated in the same restructure
    commit to drop its local duplicate def and import from here. -/
inductive RootPosition where
  | complement  -- under v: fills result/state slot (inside VP)
  | adjoined    -- to v: modifies causing event (outside VP)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 5. Derived Properties
-- ════════════════════════════════════════════════════

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

end Semantics.Verb.Roots
