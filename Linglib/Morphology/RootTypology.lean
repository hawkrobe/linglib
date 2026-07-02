import Linglib.Semantics.Lexical.EventStructure
import Linglib.Semantics.Aspect.ChangeOfState
import Linglib.Semantics.Lexical.LevinTheory
import Linglib.Semantics.Lexical.LevinClassProfiles
import Linglib.Semantics.Verb.Root.Template
import Linglib.Semantics.Verb.Root.Arity
import Linglib.Semantics.Verb.Root.Profile
import Linglib.Semantics.Verb.Root.Outcomes

open Semantics.Lexical
open Verb

/-!
# Root Typology: States and Changes of State ([beavers-etal-2021], B&[beavers-koontz-garboden-2020]) [beavers-etal-2021] [beavers-koontz-garboden-2020] [coon-2019]
[arad-2005] [dixon-1982] [embick-2004] [dowty-1991] [embick-2009] [rose-nichols-2021] [levin-1993]

Beavers, Everdell, Jerro, Kauhanen, [beavers-etal-2021]
"States and changes of state: A crosslinguistic study of the roots of verbal
meaning." Language 97(3), 439–484.

## Core contribution

Change-of-state verb roots split into two types:
- **Property concept (PC) roots**: flat, red, long — underlie deadjectival CoS verbs
- **Result roots**: crack, break, shatter — underlie non-deadjectival CoS verbs

The key semantic distinction: result roots **lexically entail change**, while PC
roots do not. This refutes the **Bifurcation Thesis**:
contra bifurcation, some roots introduce templatic meaning (change = BECOME).

## The deepest theorem

A root's entailment of change determines ALL of its morphosyntactic behavior
in a single four-way biconditional (§§3–8):

    entailsChange R ↔ ¬hasSimpleStative R ∧ ¬verbalFormIsMarked R ∧ ¬allowsRestitutiveAgain R

This holds crosslinguistically (88-language typological study), ruling out
bifurcation as an explanation. The deeper explanation is the **Markedness
Generalization** (eq. 44): morphological markedness reflects semantic mismatch
between functional head and root.

## Bridges

- `EntailmentProfile.changeOfState` = result root entailment (ProtoRoles §8)
- `TemplateHead.vBecome` = the templatic operator that result roots lexicalize
- `CoSType.inception` = BECOME as ¬P→P transition (ChangeOfState/Theory)
- `Template.achievement`/`.accomplishment` = templates containing BECOME (EventStructure)
- Crosslinguistic data validates the correlations (`Studies/`, e.g.
  `Coon2019`, `BeaversEtAl2021`)

## Unified Root (§§15–17)

Extends the file with the `RootClassification` structure (§16) bundling [coon-2019]'s arity
dimension (does the root select an internal argument?) with Beavers et al.'s
change-entailment dimension. The two axes cross-classify orthogonally
(`arity_changeType_orthogonal`): knowing whether a root selects a theme tells
you nothing about whether it entails change, and vice versa.

- Coon, J. (2019). Building verbs in Chuj: Consequences for the nature of
  roots. *Journal of Linguistics* 55(1): 35–81.
- Hale, K. & Keyser, S.J. (2002). *Prolegomenon to a Theory of Argument
  Structure*. MIT Press.
- Harley, H. (2014). On the identity of roots. *Theoretical Linguistics*
  40, 225–276.
-/

open Semantics.Lexical.EventStructure
open ArgumentStructure (EntailmentProfile)
open ArgumentStructure.EntailmentProfile
open Features.ChangeOfState
open Features

-- ════════════════════════════════════════════════════
-- § 1. Root Type Subclasses ([beavers-etal-2021] §3.1)
-- ════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 0. Root Primitive Types
-- ════════════════════════════════════════════════════

/-- Two types of change-of-state verb roots ([beavers-etal-2021] §3.1).

    **Property concept (PC) roots**: underlie
    deadjectival CoS verbs. The root describes a gradable property
    (dimension, color, value, etc.). Examples: flat, red, long, warm.

    **Result roots**: underlie non-deadjectival CoS verbs. The root describes
    a specific result state that arises from a particular kind of event
    (breaking, cooking, killing, etc.). Examples: crack, break, shatter. -/
inductive RootType where
  | propertyConcept  -- flat, red, long — deadjectival CoS (flatten, redden)
  | result           -- crack, break, shatter — non-deadjectival CoS
  deriving DecidableEq, Repr

/-- Whether a root lexically entails prior change ([beavers-etal-2021] §3.6).

    PC roots denote simple states that can hold without any prior change event.
    Result roots denote states that entail a prior change event. -/
def RootType.entailsChange : RootType → Bool
  | .propertyConcept => false
  | .result => true

/-- The semantic denotation domain of a root ([coon-2019], (3);
    extended by [hanink-koontz-garboden-2025]).

    - **indivStatePred** ⟨e, ⟨v,t⟩⟩: individual/state relation (√TV, √ITV;
      also PC Class 1/3 roots per [hanink-koontz-garboden-2025]: λx_e λs_v[P(x)(s)])
    - **statePred** ⟨v,t⟩: predicate of states, no individual argument
      ([hanink-koontz-garboden-2025] Class 2 PC roots: λs_v[P(s)],
      e.g., √I:YEL 'big' in Wá·šiw)
    - **measureFn** ⟨e, ⟨s,d⟩⟩: entity → event → degree (√POS; [henderson-2019])
    - **entityPred** ⟨e,t⟩: entity → truth-value, no event (√NOM) -/
inductive RootDenotationType where
  | indivStatePred  -- ⟨e, ⟨v,t⟩⟩ (√TV, √ITV; PC Class 1/3)
  | statePred       -- ⟨v,t⟩ (PC Class 2: quality-type)
  | measureFn       -- ⟨e, ⟨s,d⟩⟩ (√POS; [henderson-2019])
  | entityPred      -- ⟨e,t⟩ (√NOM)
  deriving DecidableEq, Repr

/-- Whether a root denotation type includes an individual argument.

    Types with an individual argument (⟨e, ...⟩) can compose directly
    with v_become (which requires ⟨e, ⟨v,t⟩⟩). Types without one
    (⟨v,t⟩) cause a type mismatch and require type-shifting (e.g., ∇)
    or possessive semantics (v_have) to predicate of individuals.
    ([hanink-koontz-garboden-2025] §5.1) -/
def RootDenotationType.hasIndivArg : RootDenotationType → Bool
  | .indivStatePred => true   -- ⟨e, ⟨v,t⟩⟩
  | .statePred      => false  -- ⟨v,t⟩
  | .measureFn      => true   -- ⟨e, ⟨s,d⟩⟩
  | .entityPred     => true   -- ⟨e,t⟩

/-- Unified root characterization bundling all classification dimensions.

    A root is characterized along five independent axes:
    1. **Arity**: does it select an internal argument?
    2. **Change entailment**: does it lexically
       entail a prior change event?
    3. **Denotation type** ([coon-2019], (3)): event predicate, measure
       function, or entity predicate.
    4. **Quality dimensions** ([spalek-mcnally-2026]): within-class root content
    5. **Class membership**: verb class taxonomy

    Axes 1, 2, and 3 cross-classify: Coon's four Chuj root classes are
    recovered as (arity × denotationType) pairs:
    √TV = selectsTheme + indivStatePred, √ITV = noTheme + indivStatePred,
    √POS = noTheme + measureFn, √NOM = noTheme + entityPred. -/
structure RootClassification where
  /-- Does this root select an internal argument? -/
  arity : Root.Arity
  /-- Does this root lexically entail prior change? -/
  changeType : RootType
  /-- Semantic denotation domain ([coon-2019], (3)). Optional — not all
      roots have been annotated. -/
  denotationType : Option RootDenotationType := none
  /-- Within-class quality dimensions ([spalek-mcnally-2026]) -/
  profile : Root.Profile := {}
  /-- Verb class membership -/
  levinClass : Option LevinClass := none
  deriving BEq, Repr

/-- Does this root lexically entail prior change? -/
def RootClassification.entailsChange (r : RootClassification) : Bool := r.changeType.entailsChange

/-! ### Root change type, and its blindness to the outcome axis

`RootType` is a *projection* of a root's entailment signature, derived not
stored — `Root.changeType` is the derived analog of the stored
`RootClassification.changeType`. Crucially it is blind to the [bhadra-2024]
outcome axis (`Root.outcomes`, the orthogonal dimension `Root` now carries): two
roots with the same entailments share a `changeType` whatever their outcomes —
which is precisely why outcome cardinality is a genuinely independent dimension
of root content, the one that drives reversative *un-* where the manner/result
typology cannot. -/

/-- The change-entailment type of a root, derived from its kind signature:
    a root entails change iff its signature carries `result` ([beavers-etal-2021]).
    The derived analog of `RootClassification.changeType`. -/
def Verb.Root.changeType (r : Verb.Root) : RootType :=
  if LexKind.result ∈ r.kinds then .result else .propertyConcept

theorem Verb.Root.changeType_eq_result_iff (r : Verb.Root) :
    r.changeType = .result ↔ r.HasResult := by
  unfold Verb.Root.changeType Verb.Root.HasResult
  by_cases h : LexKind.result ∈ r.kinds <;> simp [h]

/-- `changeType` is blind to outcomes: same entailments ⇒ same `changeType`,
    whatever the `outcomes`. The formal statement of why [bhadra-2024]'s outcome
    cardinality is an independent axis the manner/result signature cannot see. -/
theorem Verb.Root.changeType_ignores_outcomes {r r' : Verb.Root}
    (h : r.entailments = r'.entailments) : r.changeType = r'.changeType := by
  have hsig : r.kinds = r'.kinds := by
    unfold Verb.Root.kinds; rw [h]
  unfold Verb.Root.changeType; rw [hsig]

/-- A *bend*-like and a *break*-like root with the same entailments but different
    outcome cardinality share a `changeType` — only the outcome axis tells them
    apart ([bhadra-2024]). -/
example :
    ({ entailments := {.becomesState "s", .hasCause}, outcomes := some .multi } : Root).changeType
      = ({ entailments := {.becomesState "s", .hasCause}, outcomes := some .singleton } : Root).changeType :=
  Root.changeType_ignores_outcomes rfl

/-- Property concept root subclasses ([dixon-1982]; [beavers-etal-2021] ex. 5).

    [dixon-1982] identifies seven semantic categories. [beavers-etal-2021]
    omits HUMAN PROPENSITY from their Table 2 sample but the category is attested
    crosslinguistically ([hanink-koontz-garboden-2025] Table A1: hungry,
    afraid, sick, brave, generous, etc. in Wá·šiw). -/
inductive PCClass where
  | dimension         -- large/big, small, long, short, deep, wide, tall/high
  | age               -- old/aged
  | value             -- bad/worse, good/improved
  | color             -- white, black, red, green, blue, brown
  | physicalProperty  -- cool/cold, warm/hot, dry/wet, soft/hard, smooth/rough
  | humanPropensity   -- hungry, afraid, sick, brave, generous ([dixon-1982])
  | speed             -- fast, slow
  deriving DecidableEq, Repr

/-- Result root subclasses ([levin-1993]; [beavers-etal-2021] ex. 6). -/
inductive ResultClass where
  | entitySpecificCoS          -- burned, melted, frozen, decayed, bloomed, rusted
  | cooking                    -- cooked, baked, fried, roasted, boiled
  | breaking                   -- broken, cracked, crushed, shattered, split, torn
  | bending                    -- bent, folded, wrinkled, creased
  | killing                    -- dead, killed, murdered, drowned
  | destroying                 -- destroyed, ruined
  | calibratableCoS            -- go up, increase, go down, decrease, differ
  | inherentlyDirectedMotion   -- come, go, enter, exit, return
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 1b. Change Restriction (B&[beavers-koontz-garboden-2020] §2.4)
-- ════════════════════════════════════════════════════

/-- How a result root's change entailment is restricted (B&[beavers-koontz-garboden-2020] §2.4).

    Break-type result roots (√CRACK, √SHATTER) entail change of ANY kind —
    spatial or temporal. A crack can "run from the tree to the house" without
    a temporal becoming event; the state itself extends spatially.

    Cook/kill-type result roots (√COOK, √KILL) entail only TEMPORAL change.
    Cooking, killing, and melting are necessarily temporal processes.
    "✱The meat cooked from the oven to the table" is ruled out.

    This three-way refinement (PC / break-type / cook-type) is invisible to
    the binary `entailsChange` flag but has consequences for spatial predication
    and the interpretation of directional PPs (B&[beavers-koontz-garboden-2020] §2.4). -/
inductive ChangeRestriction where
  | anyChange      -- break-type: spatial or temporal (√CRACK, √SHATTER, √BEND)
  | temporalOnly   -- cook/kill-type: temporal change only (√COOK, √KILL, √MELT)
  deriving DecidableEq, Repr

/-- Change restriction for each result root subclass.
    Breaking/bending roots and directed motion allow spatial change descriptions;
    cooking/killing/destroying/scalar-change roots are temporally restricted. -/
def ResultClass.changeRestriction : ResultClass → ChangeRestriction
  | .breaking => .anyChange
  | .bending => .anyChange
  | .inherentlyDirectedMotion => .anyChange  -- directional change is inherently spatial
  | .entitySpecificCoS => .temporalOnly      -- burn, melt, freeze — temporal processes
  | .cooking => .temporalOnly
  | .killing => .temporalOnly
  | .destroying => .temporalOnly
  | .calibratableCoS => .temporalOnly        -- increase/decrease — temporal scalar change

/-- Breaking roots allow spatial change: "The road cracked from the tree to the house." -/
theorem breaking_allows_spatial :
    ResultClass.changeRestriction .breaking = .anyChange := rfl

/-- Cooking roots restrict to temporal change: "✱The meat cooked from A to B." -/
theorem cooking_temporal_only :
    ResultClass.changeRestriction .cooking = .temporalOnly := rfl

-- ════════════════════════════════════════════════════
-- § 2. Morphosyntactic Correlates (§§3.2–3.5, 6–7)
-- ════════════════════════════════════════════════════

/-- PC roots have simple (unmarked) stative forms; result roots lack them.

    Crosslinguistic evidence (§6, Fig. 1): PC median = 95.67% of languages
    have simple statives; result median = 1.59% (Mann-Whitney U = 1266.5,
    p < 0.001, n₁ = n₂ = 36).

    English: "bright" (PC, simple adj) vs *"shattered" requires prior change. -/
def RootType.hasSimpleStative : RootType → Bool
  | .propertyConcept => true
  | .result => false

/-- PC root verbs TEND to be morphologically marked (deadjectival: wid-en,
    flat-ten); result root verbs tend to be unmarked (break, crack, shatter).

    This captures the cross-linguistic DEFAULT pattern, not a universal.
    [hanink-koontz-garboden-2025] §4: Wá·šiw Class 1 PC roots predicate
    as bare verbs without verbal morphology (zero categorization), deviating
    from the tendency captured here.

    Crosslinguistic evidence (§7, Fig. 5): PC median = 56.01% marked;
    result median = 15.20% (U = 1291, p < 0.001). -/
def RootType.verbalFormIsMarked : RootType → Bool
  | .propertyConcept => true
  | .result => false

/-- PC roots allow restitutive 'again' (scope over root only);
    result roots allow only repetitive 'again' (scope over BECOME).

    §3.4: "John sharpened the knife again" allows restitutive reading
    (could be just one sharpening), but "#Chris thawed the meat again"
    in a restitutive context is unacceptable (necessarily two defrostings).

    Under the analysis in §3.6: 'again' can target √ROOT. For PC roots,
    this yields a restitutive reading (return to prior state without
    prior change). For result roots, since the root itself entails change,
    'again' over the root still entails a prior change event. -/
def RootType.allowsRestitutiveAgain : RootType → Bool
  | .propertyConcept => true
  | .result => false

-- ════════════════════════════════════════════════════
-- § 4. The Deepest Theorem: Semantic-Morphosyntactic Biconditional
-- ════════════════════════════════════════════════════

/-- **The main theorem of [beavers-etal-2021].**

    A root's entailment of change determines ALL of its morphosyntactic
    behavior in a single four-way biconditional. This is the paper's
    deepest result: four independently testable properties form a
    perfect correlation package.

    For result roots (entailsChange = true):
    - No simple stative forms (§6)
    - Unmarked verbal forms (§7)
    - No restitutive 'again' — only repetitive (§3.4)

    For PC roots (entailsChange = false):
    - Simple stative forms exist (§6)
    - Marked verbal forms (§7)
    - Restitutive 'again' available (§3.4)

    This correlation holds crosslinguistically (88 languages, §§4–7)
    and refutes the Bifurcation Thesis: if roots couldn't introduce
    templatic meaning (change), there would be NO semantic basis for
    the morphological and syntactic correlations. -/
theorem semantic_determines_morphosyntax (rt : RootType) :
    rt.entailsChange = true ↔
    (rt.hasSimpleStative = false ∧
     rt.verbalFormIsMarked = false ∧
     rt.allowsRestitutiveAgain = false) := by
  cases rt <;> simp [RootType.entailsChange, RootType.hasSimpleStative,
    RootType.verbalFormIsMarked, RootType.allowsRestitutiveAgain]

/-- The converse: NOT entailing change determines the opposite package. -/
theorem pc_determines_morphosyntax (rt : RootType) :
    rt.entailsChange = false ↔
    (rt.hasSimpleStative = true ∧
     rt.verbalFormIsMarked = true ∧
     rt.allowsRestitutiveAgain = true) := by
  cases rt <;> simp [RootType.entailsChange, RootType.hasSimpleStative,
    RootType.verbalFormIsMarked, RootType.allowsRestitutiveAgain]

-- ════════════════════════════════════════════════════
-- § 5. The Bifurcation Thesis and Its Refutation (§§2, 3.6, 9)
-- ════════════════════════════════════════════════════

/-- The Bifurcation Thesis for Roots ([embick-2009]:1, [arad-2005]:79;
    [beavers-etal-2021] eq. 2):

    "If a component of meaning is introduced by a semantic rule that
    applies to elements in combination [i.e. by templatic operators],
    then that component of meaning cannot be part of the meaning of
    a [lexical semantic] root."

    Under bifurcation, change (= BECOME) is introduced only by templates,
    never by roots. Therefore NO root should entail change. -/
def bifurcationThesis (rootEntailsChange : RootType → Bool) : Prop :=
  ∀ rt, rootEntailsChange rt = false

/-- [beavers-etal-2021] main result: bifurcation does not hold.
    Result roots entail change, violating the thesis (§§3.3, 3.6, 9). -/
theorem bifurcation_fails :
    ¬ bifurcationThesis RootType.entailsChange := by
  intro h
  have := h .result
  simp [RootType.entailsChange] at this

/-- Corollary: result roots are a witness to bifurcation failure. -/
theorem result_roots_witness_against_bifurcation :
    RootType.entailsChange .result = true := rfl

/-- PC roots are consistent with bifurcation (they don't entail change). -/
theorem pc_roots_consistent_with_bifurcation :
    RootType.entailsChange .propertyConcept = false := rfl

/-- **B&[beavers-koontz-garboden-2020] strengthened bifurcation failure via `Root.Kinds`.**

    [beavers-etal-2021] show roots can entail CHANGE (one templatic notion).
    B&[beavers-koontz-garboden-2020] show roots can entail CHANGE, CAUSATION, and MANNER —
    ALL notions traditionally reserved for templates. This is a strictly
    stronger refutation: even if one accepted that change is "special",
    roots encoding manner+cause (√GUILLOTINE, √HAND) violate bifurcation
    on three separate dimensions simultaneously.

    Witness: `Root.Kinds.fullSpec` carries all four kinds. -/
theorem bkg_bifurcation_fails_all_dimensions :
    -- Roots can entail change (result kind)
    LexKind.result ∈ Root.Kinds.fullSpec ∧
    -- Roots can entail causation (cause kind)
    LexKind.cause ∈ Root.Kinds.fullSpec ∧
    -- Roots can entail manner (manner kind)
    LexKind.manner ∈ Root.Kinds.fullSpec ∧
    -- All at once — not just one dimension
    LexKind.state ∈ Root.Kinds.fullSpec := by decide

/-- Multiple Levin classes witness the stronger bifurcation failure. -/
theorem bkg_bifurcation_multiple_witnesses :
    LexKind.result ∈ LevinClass.rootEntailments .cut ∧
    LexKind.manner ∈ LevinClass.rootEntailments .cut ∧
    LexKind.cause ∈ LevinClass.rootEntailments .give ∧
    LexKind.manner ∈ LevinClass.rootEntailments .give := by decide

-- ════════════════════════════════════════════════════
-- § 6. The Markedness Generalization (§8, eq. 44)
-- ════════════════════════════════════════════════════

/-- Whether a form is morphologically marked (=derived/complex) or
    unmarked (=basic/simple). -/
inductive Markedness where
  | unmarked  -- Basic form (no additional morphology)
  | marked    -- Derived form (overt morphological marking: -en, -ed, etc.)
  deriving DecidableEq, Repr

/-- The Markedness Generalization ([beavers-etal-2021] eq. 44).

    Morphological markedness reflects semantic **mismatch** between a
    functional head and its root complement. A form is unmarked when
    the head's semantic contribution is REDUNDANT with the root's meaning:

    (a) Default realization of v_become with complement √ROOT:
        - If √ROOT entails change → v_become is redundant → UNMARKED verb
        - If √ROOT does not entail change → v_become adds content → MARKED verb

    (b) Default realization of Asp_{S/R} with complement X:
        - If X does not entail change → already stative → UNMARKED stative
        - If X entails change → change must be stripped → MARKED stative

    This explains three attested language types:
    1. English-type: markedness asymmetry realized overtly (-en, -ed)
    2. Equipollent: both marked (high-marking languages like Hebrew)
    3. Labile: neither marked (low-marking languages like Kinyarwanda)

    And rules out the **unattested** fourth type (where the markedness
    pattern is the inverse of what the generalization predicts). -/
def verbalMarkedness (rt : RootType) : Markedness :=
  if rt.entailsChange then .unmarked else .marked

/-- Stative markedness is the mirror image of verbal markedness. -/
def stativeMarkedness (rt : RootType) : Markedness :=
  if rt.entailsChange then .marked else .unmarked

/-- Verbal and stative markedness are always complementary. -/
theorem markedness_complementarity (rt : RootType) :
    verbalMarkedness rt ≠ stativeMarkedness rt := by
  cases rt <;> simp [verbalMarkedness, stativeMarkedness, RootType.entailsChange]

/-- Result roots produce unmarked verbs. -/
theorem result_root_unmarked_verb :
    verbalMarkedness .result = .unmarked := rfl

/-- PC roots produce marked verbs. -/
theorem pc_root_marked_verb :
    verbalMarkedness .propertyConcept = .marked := rfl

/-- Result roots produce marked statives. -/
theorem result_root_marked_stative :
    stativeMarkedness .result = .marked := rfl

/-- PC roots produce unmarked statives. -/
theorem pc_root_unmarked_stative :
    stativeMarkedness .propertyConcept = .unmarked := rfl

/-- The markedness generalization is equivalent to the semantic distinction. -/
theorem markedness_from_semantics (rt : RootType) :
    verbalMarkedness rt = .unmarked ↔ rt.entailsChange = true := by
  cases rt <;> simp [verbalMarkedness, RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 7c. Ditransitive Root Classes (B&[beavers-koontz-garboden-2020] Ch. 3)
-- ════════════════════════════════════════════════════

/-- What a ditransitive root entails about possession (B&[beavers-koontz-garboden-2020] §3.3).
    Templates always introduce PROSPECTIVE possession (via ◇ modality).
    Whether the ROOT adds actual or prospective possession on top
    determines cancellability:
    "gave X the ball, #but X never had it" vs.
    "sent X the ball, but it never arrived" (OK). -/
inductive PossessionEntailment where
  | none        -- root says nothing about possession (template provides ◇have')
  | prospective -- root entails future/intended possession (√PROMISE, √OWE)
  | actual      -- root entails actual possession transfer (√GIVE, √HAND)
  deriving DecidableEq, Repr

/-- Six classes of ditransitive verb roots (B&[beavers-koontz-garboden-2020] §3.6).
    The ditransitive parallel to the PC/result distinction for CoS roots:
    templates contribute only PROSPECTIVE states; roots can contribute
    ACTUAL states. -/
inductive DitransitiveRootClass where
  | causedPossession   -- √GIVE, √HAND, √PASS: actual possession transfer
  | futureHaving       -- √PROMISE, √OWE, √BEQUEATH: prospective possession
  | ballisticMotion    -- √THROW, √TOSS, √FLING: manner + caused motion
  | sending            -- √SEND, √MAIL, √SHIP: caused motion, no manner
  | accompaniedMotion  -- √BRING, √TAKE: agent accompanies theme
  | carrying           -- √CARRY, √HAUL, √LUG: manner + accompaniment
  deriving DecidableEq, Repr

/-- What a ditransitive root entails about the transfer event.
    Each field is a distinct semantic entailment from the ROOT,
    independent of what the template provides. -/
structure DitransitiveEntailments where
  possession    : PossessionEntailment
  causedMotion  : Bool  -- root entails caused motion of theme
  manner        : Bool  -- root specifies manner of transfer/motion
  accompaniment : Bool  -- root entails agent accompanies theme
  deriving DecidableEq, Repr

/-- Entailment profile for each ditransitive root class (B&[beavers-koontz-garboden-2020] §3.6). -/
def DitransitiveRootClass.entailments : DitransitiveRootClass → DitransitiveEntailments
  | .causedPossession  => ⟨.actual,      false, false, false⟩
  | .futureHaving      => ⟨.prospective, false, false, false⟩
  | .ballisticMotion   => ⟨.none,        true,  true,  false⟩
  | .sending           => ⟨.none,        true,  false, false⟩
  | .accompaniedMotion => ⟨.none,        true,  false, true⟩
  | .carrying          => ⟨.none,        true,  true,  true⟩

/-- √GIVE entails actual possession — "Kim gave Sandy the ball,
    #but Sandy never had it" is contradictory (§3.3, ex. 17). -/
theorem give_entails_actual_possession :
    (DitransitiveRootClass.entailments .causedPossession).possession = .actual := rfl

/-- √SEND does NOT entail possession — "Kim sent Sandy the ball,
    but it never arrived" is felicitous (§3.3, ex. 18). -/
theorem send_no_possession :
    (DitransitiveRootClass.entailments .sending).possession = .none := rfl

/-- √PROMISE entails only prospective possession. -/
theorem promise_prospective :
    (DitransitiveRootClass.entailments .futureHaving).possession = .prospective := rfl

/-- √THROW entails manner + caused motion but not possession. -/
theorem throw_manner_motion :
    let e := DitransitiveRootClass.entailments .ballisticMotion
    e.possession = .none ∧ e.causedMotion = true ∧ e.manner = true := ⟨rfl, rfl, rfl⟩

/-- √BRING entails accompaniment — agent travels with theme. -/
theorem bring_accompaniment :
    (DitransitiveRootClass.entailments .accompaniedMotion).accompaniment = true := rfl

/-- √CARRY entails manner + accompaniment but not possession. -/
theorem carry_manner_accompaniment :
    let e := DitransitiveRootClass.entailments .carrying
    e.manner = true ∧ e.accompaniment = true ∧ e.possession = .none := ⟨rfl, rfl, rfl⟩

namespace Semantics.Lexical

/-- Bridge to LevinClass: ditransitive Levin classes → root classes. -/
def LevinClass.ditransitiveRootClass : LevinClass → Option DitransitiveRootClass
  | .give => some .causedPossession
  | .contribute => some .causedPossession
  | .exchange => some .causedPossession
  | .throw => some .ballisticMotion
  | .send => some .sending
  | .carry => some .carrying
  | _ => none

theorem give_class_causedPossession :
    LevinClass.ditransitiveRootClass .give = some .causedPossession := rfl
theorem throw_class_ballisticMotion :
    LevinClass.ditransitiveRootClass .throw = some .ballisticMotion := rfl
theorem send_class_sending :
    LevinClass.ditransitiveRootClass .send = some .sending := rfl
theorem carry_class_carrying :
    LevinClass.ditransitiveRootClass .carry = some .carrying := rfl

end Semantics.Lexical

-- ════════════════════════════════════════════════════
-- § 7e. MRC Diagnostics (B&[beavers-koontz-garboden-2020] §§4.2–4.3)
-- ════════════════════════════════════════════════════

/-- The six MRC diagnostics developed in B&KG (2020 §§4.2–4.3).
    Three test for result entailment in the root; three test for manner.
    An MRC violation is a verb that passes diagnostics from BOTH sets.

    Result diagnostics (§4.2):
    - `denialOfResult`: "X cut Y, #but Y wasn't separated" — contradictory
    - `objectDeletion`: result verbs resist unspecified object deletion
    - `restrictedResultatives`: result verbs block adding new result XPs

    Manner diagnostics (§4.3):
    - `selectionalRestriction`: subject restricted to agents capable of the manner
    - `denialOfAction`: "X cut Y, #but X didn't do anything" — contradictory
    - `actorParaphrase`: paraphrasable as "X did manner to Y" (§4.3) -/
inductive MRCDiagnostic where
  | denialOfResult
  | objectDeletion
  | restrictedResultatives
  | selectionalRestriction
  | denialOfAction
  | actorParaphrase
  deriving DecidableEq, Repr

/-- Whether a diagnostic tests for result entailment. -/
def MRCDiagnostic.TestsResult : MRCDiagnostic → Prop
  | .denialOfResult => True
  | .objectDeletion => True
  | .restrictedResultatives => True
  | _ => False

instance : DecidablePred MRCDiagnostic.TestsResult := fun d => by
  cases d <;> unfold MRCDiagnostic.TestsResult <;> infer_instance

/-- Whether a diagnostic tests for manner entailment. -/
def MRCDiagnostic.TestsManner : MRCDiagnostic → Prop
  | .selectionalRestriction => True
  | .denialOfAction => True
  | .actorParaphrase => True
  | _ => False

instance : DecidablePred MRCDiagnostic.TestsManner := fun d => by
  cases d <;> unfold MRCDiagnostic.TestsManner <;> infer_instance

/-- Each diagnostic tests for exactly one of manner or result. -/
theorem diagnostic_exclusive (d : MRCDiagnostic) :
    d.TestsResult ↔ ¬ d.TestsManner := by
  cases d <;> simp [MRCDiagnostic.TestsResult, MRCDiagnostic.TestsManner]

/-- A verb's diagnostic profile: which of the six diagnostics it passes.
    B&KG (2020 §§4.2–4.3) survey these for each verb class. -/
structure MRCDiagnosticProfile where
  denialOfResult         : Bool
  objectDeletion         : Bool
  restrictedResultatives : Bool
  selectionalRestriction : Bool
  denialOfAction         : Bool
  actorParaphrase   : Bool
  deriving DecidableEq, Repr

/-- Whether the profile shows result entailment (passes ≥1 result diagnostic). -/
def MRCDiagnosticProfile.showsResult (p : MRCDiagnosticProfile) : Bool :=
  p.denialOfResult || p.objectDeletion || p.restrictedResultatives

/-- Whether the profile shows manner entailment (passes ≥1 manner diagnostic). -/
def MRCDiagnosticProfile.showsManner (p : MRCDiagnosticProfile) : Bool :=
  p.selectionalRestriction || p.denialOfAction || p.actorParaphrase

/-- An MRC violation is a verb whose diagnostics show BOTH manner and result. -/
def MRCDiagnosticProfile.showsMRCViolation (p : MRCDiagnosticProfile) : Bool :=
  p.showsManner && p.showsResult

/-- Cut passes all 6 diagnostics (B&KG §4.4): manner of cutting + separation.
    "Kim cut the bread, #but the bread wasn't separated" (result)
    "Kim cut the bread, #but Kim didn't do anything" (manner) -/
def cutDiagnostics : MRCDiagnosticProfile :=
  ⟨true, true, true, true, true, true⟩

/-- Break passes result diagnostics only: pure result (√CRACK), no manner. -/
def breakDiagnostics : MRCDiagnosticProfile :=
  ⟨true, true, true, false, false, false⟩

/-- Hit passes manner diagnostics only: pure manner (impact), no result. -/
def hitDiagnostics : MRCDiagnosticProfile :=
  ⟨false, false, false, true, true, true⟩

/-- Drown passes all 6 (B&KG §4.5): manner of drowning + death result. -/
def drownDiagnostics : MRCDiagnosticProfile :=
  ⟨true, true, true, true, true, true⟩

theorem cut_MRC_violation : cutDiagnostics.showsMRCViolation = true := rfl
theorem break_no_MRC_violation : breakDiagnostics.showsMRCViolation = false := rfl
theorem hit_no_MRC_violation : hitDiagnostics.showsMRCViolation = false := rfl
theorem drown_MRC_violation : drownDiagnostics.showsMRCViolation = true := rfl

/-- Cut is MRC-violating by BOTH diagnostics AND kind signature. -/
theorem cut_diagnostics_match_entailments :
    cutDiagnostics.showsMRCViolation = true ↔
    (LevinClass.rootEntailments .cut).HasMannerAndResult := by decide

/-- Break is MRC-respecting by BOTH diagnostics AND kind signature. -/
theorem break_diagnostics_match_entailments :
    breakDiagnostics.showsMRCViolation = true ↔
    (LevinClass.rootEntailments .break_).HasMannerAndResult := by decide

/-- Hit is MRC-respecting by BOTH diagnostics AND kind signature. -/
theorem hit_diagnostics_match_entailments :
    hitDiagnostics.showsMRCViolation = true ↔
    (LevinClass.rootEntailments .hit).HasMannerAndResult := by decide

-- ════════════════════════════════════════════════════
-- § 8. Bridge to EntailmentProfile.changeOfState (ProtoRoles §8)
-- ════════════════════════════════════════════════════

/-- Dowty's P-Patient entailment (a) "undergoes change of state" is
    precisely the result root entailment. An object bearing a result
    root's state predicate has `changeOfState = true`.

    This bridges the root typology to the
    entailment profile via the shared property. -/
def rootTypeFromChangeEntailment (p : EntailmentProfile) : RootType :=
  if p.changeOfState then .result else .propertyConcept

/-- A result verb's object (accomplishment template) has
    changeOfState = true, so it patterns with result roots. Contact-verb
    objects (*kick*: CA+St, no entailed change per [beavers-2011]
    eq. (60c)) fall on the other side of the bridge. -/
theorem result_object_has_changeOfState :
    rootTypeFromChangeEntailment accomplishmentObjectProfile = .result ∧
    rootTypeFromChangeEntailment Features.LevinClassProfiles.contactObject
      = .propertyConcept := by
  decide

/-- Die subject undergoes change → result-type pattern. -/
theorem die_result_pattern :
    rootTypeFromChangeEntailment
      Features.LevinClassProfiles.disappearance.subjectProfile = .result := by
  decide

-- ════════════════════════════════════════════════════
-- § 9. Bridge to Template / BECOME (EventStructure §2)
-- ════════════════════════════════════════════════════

/-- Result roots MUST combine with a template containing BECOME
    (achievement or accomplishment), because the root's change
    entailment is semantically redundant with BECOME.

    PC roots CAN combine with any template — with BECOME (achievement/
    accomplishment) they get change compositionally; without it (state)
    they denote simple states. -/
def RootType.requiresBECOME : RootType → Bool
  | .result => true
  | .propertyConcept => false

/-- Result roots always get templates with BECOME. -/
theorem result_root_gets_become_template :
    RootType.requiresBECOME .result = true := rfl

/-- Achievement and accomplishment templates contain BECOME. -/
def Template.hasBECOME : Template → Bool
  | .achievement => true
  | .accomplishment => true
  | _ => false

/-- The templates result roots combine with always have BECOME. -/
theorem result_templates_have_become :
    Template.hasBECOME .achievement = true ∧
    Template.hasBECOME .accomplishment = true :=
  ⟨rfl, rfl⟩

/-- State template lacks BECOME — only available to PC roots. -/
theorem state_template_no_become :
    Template.hasBECOME .state = false := rfl

/-- Bridge: templates with BECOME map to achievement/accomplishment Vendler
    classes, both of which are telic (bounded by the result state).
    This connects the template operator to the existing aspectual profile. -/
theorem become_templates_telic :
    Template.vendlerClass .achievement = .achievement ∧
    Template.vendlerClass .accomplishment = .accomplishment := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. Connecting Root Types to VendlerClass (Aspect.lean)
-- ════════════════════════════════════════════════════

/-- Aspectual profile for root types in their stative use. -/
def RootType.stativeAspectualProfile : RootType → AspectualProfile
  | .propertyConcept => stateProfile        -- "The rug is flat" (stative)
  | .result => achievementProfile           -- No pure stative; even "broken" entails change

/-- Result root verbs are typically achievements or accomplishments
    (they have BECOME in their template). PC root verbs in their
    inchoative (change-of-state) use are also achievements/accomplishments,
    but their stative use is a state (derived from profile). -/
def RootType.stativeVendlerClass (rt : RootType) : VendlerClass :=
  rt.stativeAspectualProfile.toVendlerClass

/-- PC roots in stative use are states; result roots pattern as achievements
    even in adjectival use (the state entails prior change). -/
theorem root_stative_vendler :
    RootType.stativeVendlerClass .propertyConcept = .state ∧
    RootType.stativeVendlerClass .result = .achievement :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. [embick-2004] Adjectival Structures (§3.2, eq. 8)
-- ════════════════════════════════════════════════════

/-- [embick-2004] posits two adjectival structures:

    (8a) BASIC STATIVES: [AspP AspS √ROOT]
         Simple adjective directly combining with stativizer.
         Only available to PC roots.

    (8b) RESULT STATIVES: [AspP AspR [vP DP v_become √ROOT]]
         Deverbal adjective containing v_become.
         Available to result roots; superficially also to PC roots.

    Under the non-bifurcated analysis, result root adjectives are
    ALWAYS (8b) because the root requires v_become. PC root adjectives
    are (8a) by default but can also be (8b). -/
inductive AdjectivalStructure where
  | basicStative    -- [AspP AspS √ROOT] — simple adjective
  | resultStative   -- [AspP AspR [vP DP v_become √ROOT]] — deverbal
  deriving DecidableEq, Repr

/-- PC roots admit both structures; result roots only admit resultStative. -/
def RootType.admitsBasicStative : RootType → Bool
  | .propertyConcept => true
  | .result => false

/-- This is equivalent to NOT entailing change. -/
theorem admitsBasicStative_iff_no_change (rt : RootType) :
    rt.admitsBasicStative = true ↔ rt.entailsChange = false := by
  cases rt <;> simp [RootType.admitsBasicStative, RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 12. The Again Diagnostic ([beavers-koontz-garboden-2020] §1.3.2, §2.4)
-- ════════════════════════════════════════════════════

/-- Reading-count tabulation of sublexical *again* by root type
    ([beavers-koontz-garboden-2020] §1.3.2 (25), §2.4 (46)–(47)). *again* attaches
    either low (to the root, restitutive) or high (over `vbecome`, repetitive):

    - RESTITUTIVE: presupposes only a prior state — available iff the root is
      change-free (PC roots, BKG (46));
    - REPETITIVE: presupposes a prior change — always available.

    A result root's state itself entails change, so its low/restitutive attachment
    still presupposes change and collapses into the repetitive reading (BKG (47),
    "result roots never admit truly restitutive readings"). The *mechanism* — the
    presuppositional operator and the reading hierarchy — is the canonical
    `Verb.CosModel.again` (see `result_restitution_entails_change`); this enum just
    records how many distinct readings each `RootType` admits. -/
inductive AgainReading where
  | restitutive   -- again scopes over root only
  | repetitive    -- again scopes over vP (includes BECOME)
  deriving DecidableEq, Repr

/-- Which readings of 'again' are available for each root type. -/
def RootType.againReadings : RootType → List AgainReading
  | .propertyConcept => [.restitutive, .repetitive]
  | .result => [.repetitive]

/-- PC roots have strictly more 'again' readings than result roots. -/
theorem pc_more_again_readings :
    (RootType.againReadings .propertyConcept).length >
    (RootType.againReadings .result).length := by decide

/-- Result roots lack the restitutive reading. -/
theorem result_no_restitutive :
    ¬ AgainReading.restitutive ∈ RootType.againReadings .result := by
  simp [RootType.againReadings]

/-- PC roots have the restitutive reading. -/
theorem pc_has_restitutive :
    AgainReading.restitutive ∈ RootType.againReadings .propertyConcept := by
  simp [RootType.againReadings]

-- ════════════════════════════════════════════════════
-- § 12c. Ditransitive Telicity and *Again* (B&[beavers-koontz-garboden-2020] §§3.7, 3.9)
-- ════════════════════════════════════════════════════

/-- Whether a ditransitive verb is obligatorily telic in the IO frame
    (B&[beavers-koontz-garboden-2020] §3.7).

    Telicity correlates with whether the root spells out a state in the
    template. If the root entails actual possession, the template's
    prospective possession is discharged → definite endpoint → telic.

    "Kim gave Sandy balls for an hour" — # (bounded by possession transfer)
    "Kim sent Sandy balls for an hour" — OK (endpoint only prospective) -/
def DitransitiveRootClass.obligatorilyTelic : DitransitiveRootClass → Bool
  | .causedPossession  => true
  | _ => false

/-- Telicity aligns exactly with actual possession entailment. -/
theorem telic_iff_actual_possession (c : DitransitiveRootClass) :
    c.obligatorilyTelic = true ↔
    c.entailments.possession = .actual := by
  cases c <;> simp [DitransitiveRootClass.obligatorilyTelic,
    DitransitiveRootClass.entailments]

/-- Predicted *again* readings for each ditransitive root class. -/
def DitransitiveRootClass.againReadings :
    DitransitiveRootClass → List AgainReading
  | .causedPossession => [.repetitive]
  | _ => [.restitutive, .repetitive]

/-- Give has one reading (collapse); send has two (distinct). -/
theorem give_one_send_two_again :
    (DitransitiveRootClass.againReadings .causedPossession).length = 1 ∧
    (DitransitiveRootClass.againReadings .sending).length = 2 := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. Consequence for Event-Structural Theory (§9)
-- ════════════════════════════════════════════════════

/-- Beavers et al.'s conclusion (§9): accepting that result roots entail
    change does NOT blunt the predictive power of event structures. It
    simply means the theory of possible root meanings is richer than
    bifurcation allows. A verb that entails change should have
    v_become-type grammatical behavior (argument structure, morphology)
    even if the change comes from the ROOT rather than the template.

    Formally: if a root entails change, then the verb should be
    associated with a template containing BECOME. -/
theorem entails_change_implies_become_template (rt : RootType)
    (h : rt.entailsChange = true) :
    rt.requiresBECOME = true := by
  cases rt <;> simp_all [RootType.entailsChange, RootType.requiresBECOME]

/-- And conversely: if a root does NOT require BECOME, it doesn't
    entail change (it can stand alone as a simple stative). -/
theorem no_become_implies_no_change (rt : RootType)
    (h : rt.requiresBECOME = false) :
    rt.entailsChange = false := by
  cases rt <;> simp_all [RootType.requiresBECOME, RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 14. Grand Unification: All Correlates from entailsChange
-- ════════════════════════════════════════════════════

/-- **The full correlation package.**

    Starting from the single Boolean `entailsChange`, we can derive
    ALL of the paper's morphosyntactic predictions. This is the formal
    content of the paper's main contribution: one semantic property
    (whether the root lexically entails change) is the sole determinant
    of six independently observable properties. -/
theorem grand_unification (rt : RootType) :
    -- Change entailment determines EVERYTHING:
    (rt.entailsChange = true →
      rt.hasSimpleStative = false ∧
      rt.verbalFormIsMarked = false ∧
      rt.allowsRestitutiveAgain = false ∧
      rt.requiresBECOME = true ∧
      rt.admitsBasicStative = false ∧
      verbalMarkedness rt = .unmarked ∧
      stativeMarkedness rt = .marked) ∧
    (rt.entailsChange = false →
      rt.hasSimpleStative = true ∧
      rt.verbalFormIsMarked = true ∧
      rt.allowsRestitutiveAgain = true ∧
      rt.requiresBECOME = false ∧
      rt.admitsBasicStative = true ∧
      verbalMarkedness rt = .marked ∧
      stativeMarkedness rt = .unmarked) := by
  cases rt <;> simp_all [
    RootType.entailsChange, RootType.hasSimpleStative,
    RootType.verbalFormIsMarked, RootType.allowsRestitutiveAgain,
    RootType.requiresBECOME, RootType.admitsBasicStative,
    verbalMarkedness, stativeMarkedness]

-- ════════════════════════════════════════════════════
-- § 15. Root Extension: Markedness Functions
-- ════════════════════════════════════════════════════

/-- Predicted verbal markedness from change entailment. -/
def RootClassification.verbalMarkedness (r : RootClassification) : Markedness :=
  _root_.verbalMarkedness r.changeType

/-- Predicted stative markedness from change entailment. -/
def RootClassification.stativeMarkedness (r : RootClassification) : Markedness :=
  _root_.stativeMarkedness r.changeType

-- ════════════════════════════════════════════════════
-- § 16. Cross-Classification: Arity × Change Entailment
-- ════════════════════════════════════════════════════

-- Witnesses for all four cells of the 2×2 cross-classification.

/-- √BREAK: selects theme + entails change (result root, Levin 45.1).
    "Break X" — the root obligatorily takes a patient that undergoes
    breaking, and the root lexically entails a prior change event. -/
def RootClassification.break_ : RootClassification :=
  { arity := .selectsTheme, changeType := .result,
    denotationType := some .indivStatePred, levinClass := some .break_ }

/-- √HIT: selects theme + does not entail change (Levin 18.1).
    "Hit X" — the root takes a contactee, but hitting does not entail
    that the patient undergoes a change of state ([levin-1993] pp. 5–8).
    `.propertyConcept` is used broadly here: the formal content
    (`entailsChange = false`) is what matters, not the label. -/
def RootClassification.hit : RootClassification :=
  { arity := .selectsTheme, changeType := .propertyConcept,
    denotationType := some .indivStatePred, levinClass := some .hit }

/-- √DIE: no theme + entails change.
    "Die" — intransitive; the dying entity is introduced by functional
    structure (unaccusative vGO/vBE), not selected by the root. Dying
    lexically entails a prior change event (becoming dead). -/
def RootClassification.die : RootClassification :=
  { arity := .noTheme, changeType := .result,
    denotationType := some .indivStatePred }

/-- √SIT: no theme + does not entail change (positional root).
    "Sit" — Coon's √POS class: denotes a spatial configuration state.
    No internal argument, no entailed change. -/
def RootClassification.sit : RootClassification :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .measureFn, levinClass := some .assumePosition }

/-- **Orthogonality of arity and change entailment.**

    All four cells of the 2×2 cross-classification are inhabited.
    This proves the two dimensions are genuinely independent:
    knowing that a root selects a theme tells you nothing about
    whether it entails change, and vice versa. -/
theorem arity_changeType_orthogonal :
    (∃ r : RootClassification, r.arity = .selectsTheme ∧ r.changeType = .result) ∧
    (∃ r : RootClassification, r.arity = .selectsTheme ∧ r.changeType = .propertyConcept) ∧
    (∃ r : RootClassification, r.arity = .noTheme ∧ r.changeType = .result) ∧
    (∃ r : RootClassification, r.arity = .noTheme ∧ r.changeType = .propertyConcept) :=
  ⟨⟨.break_, rfl, rfl⟩, ⟨.hit, rfl, rfl⟩, ⟨.die, rfl, rfl⟩, ⟨.sit, rfl, rfl⟩⟩

/-- **Change entailment does not determine arity** (and vice versa).

    Beavers et al.'s grand unification (§14) shows that `entailsChange`
    determines ALL morphosyntactic correlates (markedness, simple stative,
    again readings, template requirements). But it determines NOTHING
    about internal argument selection. Coon's arity adds an independent
    dimension of prediction: whether the root will surface with an
    internal argument across voice alternations. -/
theorem change_does_not_determine_arity :
    (∃ r : RootClassification, r.entailsChange = true ∧ r.arity = .selectsTheme) ∧
    (∃ r : RootClassification, r.entailsChange = true ∧ r.arity = .noTheme) ∧
    (∃ r : RootClassification, r.entailsChange = false ∧ r.arity = .selectsTheme) ∧
    (∃ r : RootClassification, r.entailsChange = false ∧ r.arity = .noTheme) :=
  ⟨⟨.break_, rfl, rfl⟩, ⟨.die, rfl, rfl⟩, ⟨.hit, rfl, rfl⟩, ⟨.sit, rfl, rfl⟩⟩

/-- **Theme persistence** ([coon-2019] main empirical claim).

    If a root selects a theme, the internal argument persists regardless
    of what v/Voice⁰ head combines with it. In Chuj, √TV roots surface
    with an internal argument in transitive (Ø), passive (-ch, -j),
    and antipassive (-w) constructions alike.

    This is expressed by design: `arity` is a field of `RootClassification`, not of
    the derived verb. No functional head modifies it. -/
theorem theme_persistence (r : RootClassification) (h : r.arity = .selectsTheme) :
    r.arity.hasInternalArg = true := by
  simp [h, Root.Arity.hasInternalArg]

/-- Change entailment determines markedness in the unified Root. -/
theorem root_markedness_from_change (r : RootClassification) :
    r.verbalMarkedness = .unmarked ↔ r.entailsChange = true := by
  cases r with | mk arity changeType _ _ _ =>
  cases changeType <;> simp [RootClassification.verbalMarkedness, RootClassification.entailsChange,
    verbalMarkedness, RootType.entailsChange]

/-- Roots with the same change type have identical morphosyntactic
    behavior regardless of arity — markedness, stative forms, and
    again readings are orthogonal to internal argument selection. -/
theorem same_change_same_morphosyntax (r₁ r₂ : RootClassification)
    (h : r₁.changeType = r₂.changeType) :
    r₁.verbalMarkedness = r₂.verbalMarkedness ∧
    r₁.stativeMarkedness = r₂.stativeMarkedness ∧
    r₁.entailsChange = r₂.entailsChange := by
  simp [RootClassification.verbalMarkedness, RootClassification.stativeMarkedness, RootClassification.entailsChange, h]

-- ════════════════════════════════════════════════════
-- § 17. Root Position in Event Structure (B&[beavers-koontz-garboden-2020] §5.4.1, Table 12)
-- ════════════════════════════════════════════════════

/-- Full root specification: entailment features + structural position.
    This is [beavers-koontz-garboden-2020]'s ch. 5 root typology
    (display (12)) in full — the 4 binary entailment features × 2
    positions give 32 theoretical cells, of which 7 are attested and
    the rest are principled gaps. -/
structure FullRootSpec where
  entailments : Root.Kinds
  position : Root.Position
  deriving DecidableEq

/-- Adjoined position requires +manner: a root in adjunct position
    must specify a manner of action. Without manner, there is nothing
    to adjoin — the adjunct slot expects an action modifier. -/
def FullRootSpec.PositionLicensed (s : FullRootSpec) : Prop :=
  s.position = .adjoined → LexKind.manner ∈ s.entailments

instance (s : FullRootSpec) : Decidable s.PositionLicensed :=
  inferInstanceAs (Decidable (_ → _))

/-- +manner +state −result −cause is semantically incoherent (B&KG §5.4.1):
    the root would specify both a manner of action and a state, but with
    no result or cause linking them. What would such a verb mean?
    "Perform manner M while in state S" — with no causal connection. -/
def FullRootSpec.SemanticallyCoherent (s : FullRootSpec) : Prop :=
  ¬ (LexKind.manner ∈ s.entailments ∧ LexKind.state ∈ s.entailments ∧
     LexKind.result ∉ s.entailments ∧ LexKind.cause ∉ s.entailments)

instance (s : FullRootSpec) : Decidable s.SemanticallyCoherent :=
  inferInstanceAs (Decidable (¬ _))

/-- Full well-formedness: entailment constraints + position licensing +
    semantic coherence. -/
def FullRootSpec.WellFormed (s : FullRootSpec) : Prop :=
  s.entailments.WellFormed ∧ s.PositionLicensed ∧ s.SemanticallyCoherent

instance (s : FullRootSpec) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Attested cells of Table 12 -/

/-- √FLAT: +S −M −R −C, complement. Property concept root. -/
def FullRootSpec.flat : FullRootSpec :=
  ⟨Root.Kinds.propertyConcept, .complement⟩

/-- √BLOSSOM: +S −M +R −C, complement. Pure result root. -/
def FullRootSpec.blossom : FullRootSpec :=
  ⟨Root.Kinds.pureResult, .complement⟩

/-- √CRACK: +S −M +R +C, complement. Causative result root. -/
def FullRootSpec.crack : FullRootSpec :=
  ⟨Root.Kinds.causativeResult, .complement⟩

/-- √JOG: −S +M −R −C, adjoined. Pure manner root. -/
def FullRootSpec.jog : FullRootSpec :=
  ⟨Root.Kinds.pureManner, .adjoined⟩

/-- √DROWN: +S +M +R +C, complement. Manner+result in complement position —
    the manner restricts HOW the state is caused. -/
def FullRootSpec.drown : FullRootSpec :=
  ⟨Root.Kinds.fullSpec, .complement⟩

/-- √TOSS: +S +M +R +C, adjoined. Manner+result in adjunct position —
    the manner is the primary event that happens to cause a state change. -/
def FullRootSpec.toss : FullRootSpec :=
  ⟨Root.Kinds.fullSpec, .adjoined⟩

/-- √HAND: same entailments + position as √TOSS. The difference is in
    the ditransitive layer (DitransitiveRootClass.causedPossession vs
.ballisticMotion), not in FullRootSpec's 4+1 features. -/
abbrev FullRootSpec.hand : FullRootSpec := FullRootSpec.toss

/-- √EXIST: −S −M −R −C, complement. Minimal stative root. -/
def FullRootSpec.exist : FullRootSpec :=
  ⟨Root.Kinds.minimal, .complement⟩

-- All attested types are well-formed
theorem flat_wf : FullRootSpec.flat.WellFormed := by decide
theorem blossom_wf : FullRootSpec.blossom.WellFormed := by decide
theorem crack_wf : FullRootSpec.crack.WellFormed := by decide
theorem jog_wf : FullRootSpec.jog.WellFormed := by decide
theorem drown_wf : FullRootSpec.drown.WellFormed := by decide
theorem toss_wf : FullRootSpec.toss.WellFormed := by decide
theorem hand_wf : FullRootSpec.hand.WellFormed := by decide
theorem exist_wf : FullRootSpec.exist.WellFormed := by decide

/-- √DROWN and √TOSS have identical entailments but different positions. -/
theorem drown_toss_same_entailments :
    FullRootSpec.drown.entailments = FullRootSpec.toss.entailments := rfl

theorem drown_toss_diff_position :
    FullRootSpec.drown.position ≠ FullRootSpec.toss.position := by decide

-- ════════════════════════════════════════════════════
-- § 18. Root → Templatic Head Prediction (B&[beavers-koontz-garboden-2020] Table 13)
-- ════════════════════════════════════════════════════

/-- Templatic functional heads in event structure (B&[beavers-koontz-garboden-2020] Table 13).

    Each root type PREDICTS which templatic heads its verb will entail.
    If the root's own meaning already includes what a template head
    provides, that head is "entailed by the root" — its semantic
    contribution is redundant (though structurally still present).

    v_act, v_cause, v_become are verbal heads. P_loc and P_have
    are prepositional heads specific to ditransitive structures. -/
inductive TemplateHead where
  | vAct     -- v_act: agentive activity head
  | vCause   -- v_cause: causal relation head
  | vBecome  -- v_become: change-of-state head
  | pLoc     -- P_loc: locative preposition (ditransitive motion)
  | pHave    -- P_have: possession preposition (ditransitive transfer)
  deriving DecidableEq, Repr

/-- Which template heads a root's entailments make redundant (Table 13).

    The mapping is monotone: more root entailments → more heads entailed.

    - +result → v_become (root entails the change v_become would provide)
    - +cause → v_cause (root entails the causation v_cause would provide)
    - +manner ∧ +cause → v_act (manner that causes = activity)
    - +manner alone → no v_act (manner without causation doesn't entail
      activity — √JOG specifies jogging manner but v_act still provides
      the activity frame) -/
def Verb.Root.Kinds.entailedHeads (s : Verb.Root.Kinds) : List TemplateHead :=
  (if LexKind.result ∈ s then [.vBecome] else []) ++
  (if LexKind.cause ∈ s then [.vCause] else []) ++
  (if LexKind.manner ∈ s ∧ LexKind.cause ∈ s then [.vAct] else [])

/-- For ditransitive roots, additional prepositional heads beyond
    the verbal heads predicted by `entailedHeads`. -/
def DitransitiveRootClass.additionalHeads : DitransitiveRootClass → List TemplateHead
  | .causedPossession  => [.pLoc, .pHave]  -- √HAND: location + possession
  | .ballisticMotion   => [.pLoc]           -- √TOSS: location of arrival
  | .sending           => [.pLoc]           -- √SEND: location of arrival
  | .accompaniedMotion => [.pLoc]           -- √BRING: destination
  | .carrying          => [.pLoc]           -- √CARRY: destination
  | .futureHaving      => []                -- √PROMISE: no spatial path

/-! ### Table 13 verification -/

/-- √JOG (pureManner): no template heads entailed.
    The root specifies jogging manner, but v_act still provides
    the activity frame — the root doesn't make it redundant. -/
theorem jog_no_heads :
    Root.Kinds.pureManner.entailedHeads = [] := by decide

/-- √FLAT (propertyConcept): no template heads entailed.
    The root names a state, but doesn't entail change or cause. -/
theorem flat_no_heads :
    Root.Kinds.propertyConcept.entailedHeads = [] := by decide

/-- √BLOSSOM (pureResult): v_become entailed.
    The root entails change — v_become's contribution is redundant. -/
theorem blossom_heads :
    Root.Kinds.pureResult.entailedHeads = [.vBecome] := by decide

/-- √CRACK (causativeResult): v_become + v_cause entailed.
    The root entails change AND causation. -/
theorem crack_heads :
    Root.Kinds.causativeResult.entailedHeads = [.vBecome, .vCause] := by
  decide

/-- √DROWN (fullSpec): v_become + v_cause + v_act entailed.
    The root entails change, causation, AND activity (manner that causes). -/
theorem drown_heads :
    Root.Kinds.fullSpec.entailedHeads = [.vBecome, .vCause, .vAct] := by
  decide

/-- √TOSS (fullSpec + ballistic): v_become + v_cause + v_act + P_loc.
    Verbal heads from entailments + P_loc from ditransitive class. -/
theorem toss_heads :
    Root.Kinds.fullSpec.entailedHeads ++
    DitransitiveRootClass.additionalHeads .ballisticMotion =
    [.vBecome, .vCause, .vAct, .pLoc] := by decide

/-- √HAND (fullSpec + causedPossession): all 5 heads.
    Verbal heads from entailments + P_loc + P_have from ditransitive class. -/
theorem hand_heads :
    Root.Kinds.fullSpec.entailedHeads ++
    DitransitiveRootClass.additionalHeads .causedPossession =
    [.vBecome, .vCause, .vAct, .pLoc, .pHave] := by decide

/-- Monotonicity: more root entailments → weakly more heads entailed.
    Pure result ⊂ causative result ⊂ full spec (by inclusion). -/
theorem heads_monotone :
    Root.Kinds.pureResult.entailedHeads.length ≤
    Root.Kinds.causativeResult.entailedHeads.length ∧
    Root.Kinds.causativeResult.entailedHeads.length ≤
    Root.Kinds.fullSpec.entailedHeads.length := ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 19. Gap Predictions (B&[beavers-koontz-garboden-2020] §5.4.1, Table 12)
-- ════════════════════════════════════════════════════

/-- The attested cells of B&KG's Table 12: five complement types
    (√FLAT, √BLOSSOM, √CRACK, √DROWN, √EXIST) and two adjoined types
    (√JOG, √TOSS/√HAND). -/
def FullRootSpec.attestedCells : List FullRootSpec :=
  [.flat, .blossom, .crack, .drown, .exist, .jog, .toss]

/-- Whether a FullRootSpec cell is attested in B&KG's Table 12. -/
def FullRootSpec.IsAttestedCell (s : FullRootSpec) : Prop :=
  s.WellFormed ∧ s ∈ FullRootSpec.attestedCells

instance (s : FullRootSpec) : Decidable s.IsAttestedCell :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Gap explanations

B&KG (§5.4.1) identify three principled gap types:

1. **Adjoined without manner**: the adjunct position in event structure
   hosts manner modifiers. Without +manner, there's nothing to adjoin.
   This rules out all −manner roots in adjoined position.

2. **+manner +state −result −cause**: the root would need to encode
   both a manner of action and a state, with no causal/change connection
   between them. No known verb has this pattern.

3. **Well-formedness violations**: +result −state and +cause −result
   are ruled out by the entailment constraints (result→state, cause→result). -/

/-- Gap type 1: adjoined position requires manner. -/
theorem gap_adjoined_no_manner :
    ¬ (FullRootSpec.mk Root.Kinds.propertyConcept .adjoined).PositionLicensed := by
  decide

theorem gap_adjoined_result :
    ¬ (FullRootSpec.mk Root.Kinds.pureResult .adjoined).PositionLicensed := by
  decide

theorem gap_adjoined_causativeResult :
    ¬ (FullRootSpec.mk Root.Kinds.causativeResult .adjoined).PositionLicensed := by
  decide

theorem gap_adjoined_minimal :
    ¬ (FullRootSpec.mk Root.Kinds.minimal .adjoined).PositionLicensed := by
  decide

/-- Gap type 2: +manner +state −result −cause is incoherent. -/
theorem gap_manner_state_no_result :
    ¬ (FullRootSpec.mk {.state, .manner} .complement).SemanticallyCoherent := by
  decide

theorem gap_manner_state_no_result_adj :
    ¬ (FullRootSpec.mk {.state, .manner} .adjoined).SemanticallyCoherent := by
  decide

/-- Gap type 3: well-formedness violations. -/
theorem gap_result_no_state :
    ¬ ({.result} : Root.Kinds).WellFormed := by decide

theorem gap_cause_no_result :
    ¬ ({.state, .cause} : Root.Kinds).WellFormed := by decide

/-! ### Attested cells are well-formed and recognized -/

theorem flat_attested : FullRootSpec.flat.IsAttestedCell := by decide
theorem blossom_attested : FullRootSpec.blossom.IsAttestedCell := by decide
theorem crack_attested : FullRootSpec.crack.IsAttestedCell := by decide
theorem jog_attested : FullRootSpec.jog.IsAttestedCell := by decide
theorem drown_attested : FullRootSpec.drown.IsAttestedCell := by decide
theorem toss_attested : FullRootSpec.toss.IsAttestedCell := by decide
theorem exist_attested : FullRootSpec.exist.IsAttestedCell := by decide

/-- The open question: +S +M +R −C (mannerResult without cause) in
    complement position. B&KG note this cell may be inhabited by
    verbs like *slide* — manner of motion + change of location,
    without external causation. Left as NOT attested per Table 12,
    pending further research. -/
theorem mannerResult_complement_unattested :
    ¬ (FullRootSpec.mk Root.Kinds.mannerResult .complement).IsAttestedCell := by
  decide

/-- The complement/adjoined split for fullSpec roots is the only
    case where position differentiates otherwise identical entailments. -/
theorem fullSpec_both_positions :
    FullRootSpec.drown.IsAttestedCell ∧
    FullRootSpec.toss.IsAttestedCell ∧
    FullRootSpec.drown.entailments = FullRootSpec.toss.entailments :=
  ⟨by decide, by decide, rfl⟩

