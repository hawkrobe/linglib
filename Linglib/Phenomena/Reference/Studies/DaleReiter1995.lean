import Linglib.Theories.Pragmatics.GriceanMaxims
import Linglib.Theories.Pragmatics.RSA.Core.Noise

/-!
# @cite{dale-reiter-1995}
@cite{grice-1975}

Computational Interpretations of the Gricean Maxims in the Generation
of Referring Expressions. *Cognitive Science* 19(2), 233–263.

## Core Argument

Four computational interpretations of Grice's Brevity maxim (Q2) are
possible for referring expression generation (REG):

1. **Full Brevity**: generate the shortest possible RE. NP-hard
   (reduction from minimum set cover).
2. **Greedy Heuristic**: at each step, add the most discriminating
   attribute. Polynomial but still globally optimizing.
3. **Local Brevity**: no redundant attributes, but allows reordering.
4. **No Brevity**: iterate through a fixed preference order, include
   any attribute that rules out ≥ 1 distractor. May include globally
   redundant attributes.

Psycholinguistic evidence (speakers routinely over-describe) and
computational complexity (Full Brevity is NP-hard) support
**No Brevity**. The paper presents the **Incremental Algorithm** (IA),
which operationalizes Q1 (be informative) with No-Brevity Q2.

## The Incremental Algorithm (Figure 6)

Given target referent r, contrast set C, and preference-ordered
attribute list P:

1. For each attribute Aᵢ in P:
   - Get the target's value V for Aᵢ
   - If ⟨Aᵢ, V⟩ rules out any distractor in C, include it and remove
     those distractors from C
   - If C is empty, stop (success)
2. Return the collected attribute-value pairs

Key properties: linear in |P|, no backtracking, no optimization.
The preference order determines which attributes are included — a
different order can produce a different (possibly longer) description.

## Verified Data

Worked example (§4.4) verified against paper text.

## Connection to RSA

RSA's S1 score decomposes as: α · informativity(u) − cost(u).

- informativity = Q1 (Grice's "be informative enough")
- cost = Q2 pressure (Grice's "be brief")

The Brevity interpretations correspond to regimes in RSA's
(α, cost) parameter space:

- Full Brevity ≈ α → ∞, cost > 0 (hard optimization with cost)
- No Brevity ≈ cost ≈ 0 (informativity only, no brevity pressure)

The IA's `PreferredAttributes` list orders attributes by cognitive
accessibility. The noise discrimination ordering in `RSA.Noise`
(color > size > material) provides a related but distinct ordering
based on perceptual reliability.
-/

namespace Phenomena.Reference.Studies.DaleReiter1995

-- ============================================================================
-- § Brevity Interpretations (§3)
-- ============================================================================

open Theories.Pragmatics.GriceanMaxims

/-- The four computational interpretations of Grice's Brevity maxim (Q2),
    ordered from most to least constrained. All four satisfy Q1
    (informativeness) when successful; they differ only in how strictly
    they enforce Q2 (brevity). -/
inductive BrevityInterpretation where
  /-- Generate the shortest possible RE. NP-hard by reduction from
      minimum set cover (Garey & Johnson, 1979). -/
  | fullBrevity
  /-- At each step, add the attribute that rules out the most
      distractors. Polynomial but still globally optimizing. -/
  | greedyHeuristic
  /-- No redundant attributes (each must rule out ≥ 1 new distractor),
      but allows reordering to find a shorter description. -/
  | localBrevity
  /-- Fixed preference order. Include any attribute that rules out
      ≥ 1 distractor. May include attributes that are globally
      redundant (because order is fixed, not optimized). Called
      the "Incremental Algorithm Interpretation" in the paper;
      the recommended interpretation. -/
  | noBrevity
  deriving DecidableEq, BEq, Repr

/-- Constraint strength: higher value = more constrained Q2.
    Full Brevity (3) is strictest, No Brevity (0) is weakest. -/
def BrevityInterpretation.strength : BrevityInterpretation → Nat
  | .fullBrevity     => 3
  | .greedyHeuristic => 2
  | .localBrevity    => 1
  | .noBrevity       => 0

-- ============================================================================
-- § Knowledge Base Representation (§4.1)
-- ============================================================================

/-- An attribute in the REG knowledge base. The paper's "type" attribute
    (head noun, e.g., "dog") is distinguished from modifier attributes
    (adjectives like colour, size), which map to `PropertyDomain`. -/
inductive REGAttribute where
  /-- Head noun type at the basic level (e.g., "dog", "cat").
      The paper's `BasicLevelValue` function maps species-level
      types (chihuahua, siamese-cat) to basic-level types (dog, cat);
      we use basic-level values directly. -/
  | headNoun
  /-- Modifying property (colour, size, material, ...). -/
  | modifier (d : Core.PropertyDomain)
  deriving DecidableEq, BEq, Repr

/-- A knowledge base entity: attribute-value pairs.
    Values are strings for generality (the paper uses a subsumption
    taxonomy on values; we simplify to flat strings). -/
structure KBEntity where
  attrs : List (REGAttribute × String)
  deriving Repr

/-- Look up an attribute's value for an entity. -/
def KBEntity.get (e : KBEntity) (a : REGAttribute) : Option String :=
  e.attrs.find? (fun p => p.1 == a) |>.map (·.2)

-- ============================================================================
-- § The Incremental Algorithm (§4, Figure 6)
-- ============================================================================

/-- Does an attribute-value pair rule out a distractor?
    A distractor is ruled out if it either lacks the attribute
    entirely or has a different value for it. -/
def rulesOut (attr : REGAttribute) (value : String) (distractor : KBEntity) : Bool :=
  match distractor.get attr with
  | none   => true          -- distractor lacks this attribute
  | some v => v != value    -- different value

/-- The Incremental Algorithm (Figure 6, simplified).

    Iterates through the preference-ordered attribute list. For each
    attribute, if the target has a value and that value rules out ≥ 1
    remaining distractor, include it and remove those distractors.
    Stop when all distractors are eliminated or attributes are exhausted.

    Simplifications vs. the paper:
    - No `FindBestValue` (subsumption taxonomy on values)
    - No `UserKnows` (epistemic accessibility filter)
    - No `BasicLevelValue` (Rosch basic-level categories —
      we use basic-level values directly in entity definitions)
    - No forced head noun inclusion (the paper always includes
      a type attribute; we include it only when discriminating) -/
def incrementalAlgorithm
    (target : KBEntity)
    (distractors : List KBEntity)
    (preferred : List REGAttribute) : List (REGAttribute × String) :=
  go preferred distractors []
where
  go : List REGAttribute → List KBEntity → List (REGAttribute × String)
      → List (REGAttribute × String)
  | [], _, acc => acc
  | _, [], acc => acc  -- success: all distractors ruled out
  | attr :: rest, remaining, acc =>
    match target.get attr with
    | none => go rest remaining acc
    | some v =>
      let newRemaining := remaining.filter (fun d => ¬rulesOut attr v d)
      if newRemaining.length < remaining.length then
        go rest newRemaining (acc ++ [(attr, v)])
      else
        go rest remaining acc

/-- Did the IA succeed? All distractors are ruled out by the result. -/
def iaSuccess
    (target : KBEntity)
    (distractors : List KBEntity)
    (preferred : List REGAttribute) : Bool :=
  distractors.all fun d =>
    (incrementalAlgorithm target distractors preferred).any fun (attr, v) =>
      rulesOut attr v d

-- ============================================================================
-- § Worked Example (§4.4): Kennel Domain
-- ============================================================================

/-! Three objects in a kennel. The paper uses species-level types
(chihuahua, siamese-cat) internally, but `BasicLevelValue` maps these
to basic-level types (dog, cat) for the referring expression. We use
the basic-level values directly. -/

/-- Object1: a small black dog (TARGET).
    Underlying species: chihuahua; BasicLevelValue = "dog". -/
def obj1 : KBEntity :=
  ⟨[(.headNoun, "dog"), (.modifier .size, "small"), (.modifier .color, "black")]⟩

/-- Object2: a large white dog.
    Underlying species: chihuahua; BasicLevelValue = "dog". -/
def obj2 : KBEntity :=
  ⟨[(.headNoun, "dog"), (.modifier .size, "large"), (.modifier .color, "white")]⟩

/-- Object3: a small black cat.
    Underlying species: siamese-cat; BasicLevelValue = "cat". -/
def obj3 : KBEntity :=
  ⟨[(.headNoun, "cat"), (.modifier .size, "small"), (.modifier .color, "black")]⟩

/-- P = {type, colour, size, ...} (§4.4). The paper lists colour
    before size in the preference order. -/
def kennelPreferred : List REGAttribute :=
  [.headNoun, .modifier .color, .modifier .size]

-- ============================================================================
-- § Verification Theorems: Worked Example
-- ============================================================================

/-- §4.4: The IA produces "the black dog" — type=dog rules out Object3
    (cat ≠ dog); colour=black rules out Object2 (white ≠ black).
    Size is never reached. -/
theorem kennel_result :
    incrementalAlgorithm obj1 [obj2, obj3] kennelPreferred =
    [(.headNoun, "dog"), (.modifier .color, "black")] := by
  native_decide

/-- The IA succeeds: both distractors are ruled out. -/
theorem kennel_succeeds :
    iaSuccess obj1 [obj2, obj3] kennelPreferred = true := by
  native_decide

/-- §4.4: "if P had been {type, size, colour, ...} instead of
    {type, colour, size, ...}, MakeReferringExpression would have
    returned {⟨type, dog⟩, ⟨size, small⟩} instead." The preference
    order determines which attributes are included. -/
theorem kennel_order_matters :
    incrementalAlgorithm obj1 [obj2, obj3]
      [.headNoun, .modifier .size, .modifier .color] =
    [(.headNoun, "dog"), (.modifier .size, "small")] := by
  native_decide

/-- Both preference orders succeed — the IA identifies the referent
    regardless of attribute ordering (in this example). -/
theorem kennel_both_orders_succeed :
    iaSuccess obj1 [obj2, obj3] kennelPreferred = true ∧
    iaSuccess obj1 [obj2, obj3]
      [.headNoun, .modifier .size, .modifier .color] = true := by
  constructor <;> native_decide

-- ============================================================================
-- § Non-Minimality Example
-- ============================================================================

/-! The IA can produce non-minimal descriptions because it processes
attributes in a fixed order. An attribute included early may become
globally redundant once a later attribute is also included. -/

/-- Target: a red plastic cup. -/
def cup1 : KBEntity :=
  ⟨[(.headNoun, "cup"), (.modifier .color, "red"), (.modifier .material, "plastic")]⟩

/-- Distractor 1: a blue glass cup. -/
def cup2 : KBEntity :=
  ⟨[(.headNoun, "cup"), (.modifier .color, "blue"), (.modifier .material, "glass")]⟩

/-- Distractor 2: a blue plastic cup. -/
def cup3 : KBEntity :=
  ⟨[(.headNoun, "cup"), (.modifier .color, "blue"), (.modifier .material, "plastic")]⟩

/-- With [type, material, colour], the IA produces {material=plastic,
    colour=red} — 2 modifier attributes. -/
theorem cups_material_first :
    incrementalAlgorithm cup1 [cup2, cup3]
      [.headNoun, .modifier .material, .modifier .color] =
    [(.modifier .material, "plastic"), (.modifier .color, "red")] := by
  native_decide

/-- With [type, colour, material], the IA produces {colour=red} alone —
    1 modifier attribute. Colour=red rules out BOTH distractors at once
    (both are blue), so material is never needed. -/
theorem cups_colour_first :
    incrementalAlgorithm cup1 [cup2, cup3]
      [.headNoun, .modifier .color, .modifier .material] =
    [(.modifier .color, "red")] := by
  native_decide

/-- The material-first result includes a globally redundant attribute:
    colour=red alone suffices, but the IA also includes material=plastic
    because it was processed first and ruled out cup2. This is the
    No-Brevity regime — locally useful attributes are kept even when
    globally unnecessary. -/
theorem cups_non_minimal :
    -- material-first: 2 attributes
    (incrementalAlgorithm cup1 [cup2, cup3]
      [.headNoun, .modifier .material, .modifier .color]).length = 2 ∧
    -- colour-first: 1 attribute suffices
    (incrementalAlgorithm cup1 [cup2, cup3]
      [.headNoun, .modifier .color, .modifier .material]).length = 1 ∧
    -- both succeed
    iaSuccess cup1 [cup2, cup3]
      [.headNoun, .modifier .material, .modifier .color] = true ∧
    iaSuccess cup1 [cup2, cup3]
      [.headNoun, .modifier .color, .modifier .material] = true := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- § Bridge: Brevity Hierarchy
-- ============================================================================

/-- The hierarchy is strict: FB > GH > LB > NB. -/
theorem brevity_hierarchy :
    BrevityInterpretation.fullBrevity.strength >
    BrevityInterpretation.greedyHeuristic.strength ∧
    BrevityInterpretation.greedyHeuristic.strength >
    BrevityInterpretation.localBrevity.strength ∧
    BrevityInterpretation.localBrevity.strength >
    BrevityInterpretation.noBrevity.strength := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- No Brevity targets Q2: it weakens the "don't over-inform" sub-maxim,
    not Q1. The IA still enforces Q1 — each included attribute must rule
    out at least one distractor. -/
theorem noBrevity_weakens_q2 :
    QuantityViolation.overInformative.submaxim = .Q2 := rfl

-- ============================================================================
-- § Bridge: Preference Order and Noise Discrimination
-- ============================================================================

/-- The paper's preference order places colour before size among modifier
    attributes. This aligns with the RSA noise discrimination ordering:
    colour (0.98) has higher discrimination than size (0.60), so colour
    modifiers provide more signal to the L0 listener. Higher-signal
    attributes are both more preferred (D&R) and more discriminating
    (RSA Noise). -/
theorem preference_aligns_with_discrimination :
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination :=
  RSA.Noise.color_gt_size

/-- The full discrimination ordering: colour > size > material.
    This predicts that speakers should prefer to include colour
    modifiers (high signal) over material modifiers (low signal),
    aligning with the empirical finding that colour is used
    redundantly more than material. -/
theorem full_discrimination_ordering :
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination :=
  RSA.Noise.discrimination_ordering

-- ============================================================================
-- § Bridge: PropertyDomain Connection
-- ============================================================================

/-- The IA's modifier attributes map to `PropertyDomain`, connecting
    the classical REG representation to linglib's type infrastructure.
    This means noise parameters, comparison-class properties, and
    cross-study data are all accessible for IA modifier attributes. -/
theorem modifier_domains_have_discrimination :
    Core.PropertyDomain.noiseDiscrimination .color = some RSA.Noise.colorDiscrimination ∧
    Core.PropertyDomain.noiseDiscrimination .size = some RSA.Noise.sizeDiscrimination ∧
    Core.PropertyDomain.noiseDiscrimination .material = some RSA.Noise.materialDiscrimination :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § Bridge: RSA Connection
-- ============================================================================

/-- The IA and RSA S1 solve the same problem — producing a referring
    expression that identifies a target among distractors — but via
    different mechanisms:

    - **IA**: greedy, deterministic, fixed attribute order, no cost
    - **RSA S1**: probabilistic, soft-maximizes informativity − cost

    Both decompose into Q1 (informativity) and Q2 (brevity):

    | Framework   | Q1                          | Q2               |
    |-------------|-----------------------------| -----------------|
    | D&R IA      | include if discriminating   | preference order |
    | RSA S1      | α · log P_L0(w|u)           | −cost(u)         |

    When RSA cost = 0, S1 has no brevity pressure, corresponding
    to No Brevity. When cost > 0, S1 penalizes longer utterances,
    moving toward Full Brevity as α → ∞. -/
theorem q1_q2_decomposition :
    -- Q1 and Q2 are independent sub-maxims
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim := by decide

end Phenomena.Reference.Studies.DaleReiter1995
