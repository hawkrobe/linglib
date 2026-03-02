import Linglib.Theories.Semantics.Events.EventStructure
import Linglib.Core.Root

/-!
# Root Typology: States and Changes of State (Beavers et al. 2021, B&KG 2020) @cite{beavers-etal-2021} @cite{beavers-koontz-garboden-2020} @cite{coon-2019}
@cite{arad-2005} @cite{dixon-1982} @cite{embick-2004} @cite{dowty-1991} @cite{embick-2009} @cite{rose-nichols-2021}

Beavers, Everdell, Jerro, Kauhanen, @cite{beavers-etal-2021}
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
- `Primitive.BECOME` = the templatic operator that result roots lexicalize (EventStructure)
- `CoSType.inception` = BECOME as ¬P→P transition (ChangeOfState/Theory)
- `Template.achievement`/`.accomplishment` = templates containing BECOME (EventStructure)
- Crosslinguistic data validates the correlations (Phenomena)

## Unified Root (§§15–17)

Extends the file with the `Root` structure (§16) bundling @cite{coon-2019}'s arity
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

open Semantics.Events.EventStructure
open Semantics.Events.ProtoRoles
open Semantics.Lexical.Verb.ChangeOfState
open Semantics.Lexical.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Root Type Subclasses (Beavers et al. 2021 §3.1)
-- ════════════════════════════════════════════════════

-- RootType, RootArity, RootDenotationType, and Root are defined in Core/Root.lean.

/-- Property concept root subclasses (Dixon 1982; Beavers et al. 2021 ex. 5). -/
inductive PCClass where
  | dimension         -- large/big, small, long, short, deep, wide, tall/high
  | age               -- old/aged
  | value             -- bad/worse, good/improved
  | color             -- white, black, red, green, blue, brown
  | physicalProperty  -- cool/cold, warm/hot, dry/wet, soft/hard, smooth/rough
  | speed             -- fast, slow
  deriving DecidableEq, Repr, BEq

/-- Result root subclasses (Levin 1993; Beavers et al. 2021 ex. 6). -/
inductive ResultClass where
  | entitySpecificCoS          -- burned, melted, frozen, decayed, bloomed, rusted
  | cooking                    -- cooked, baked, fried, roasted, boiled
  | breaking                   -- broken, cracked, crushed, shattered, split, torn
  | bending                    -- bent, folded, wrinkled, creased
  | killing                    -- dead, killed, murdered, drowned
  | destroying                 -- destroyed, ruined
  | calibratableCoS            -- go up, increase, go down, decrease, differ
  | inherentlyDirectedMotion   -- come, go, enter, exit, return
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 1b. Change Restriction (B&KG 2020 §2.4)
-- ════════════════════════════════════════════════════

/-- How a result root's change entailment is restricted (B&KG 2020 §2.4).

    Break-type result roots (√CRACK, √SHATTER) entail change of ANY kind —
    spatial or temporal. A crack can "run from the tree to the house" without
    a temporal becoming event; the state itself extends spatially.

    Cook/kill-type result roots (√COOK, √KILL) entail only TEMPORAL change.
    Cooking, killing, and melting are necessarily temporal processes.
    "✱The meat cooked from the oven to the table" is ruled out.

    This three-way refinement (PC / break-type / cook-type) is invisible to
    the binary `entailsChange` flag but has consequences for spatial predication
    and the interpretation of directional PPs (B&KG 2020 §2.4). -/
inductive ChangeRestriction where
  | anyChange      -- break-type: spatial or temporal (√CRACK, √SHATTER, √BEND)
  | temporalOnly   -- cook/kill-type: temporal change only (√COOK, √KILL, √MELT)
  deriving DecidableEq, Repr, BEq

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

/-- PC root verbs are morphologically marked (deadjectival: wid-en, flat-ten);
    result root verbs are unmarked (basic verbs: break, crack, shatter).

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

/-- **The main theorem of @cite{beavers-etal-2021}.**

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

/-- The Bifurcation Thesis for Roots (Embick 2009:1, Arad 2005:79;
    Beavers et al. 2021 eq. 2):

    "If a component of meaning is introduced by a semantic rule that
    applies to elements in combination [i.e. by templatic operators],
    then that component of meaning cannot be part of the meaning of
    a [lexical semantic] root."

    Under bifurcation, change (= BECOME) is introduced only by templates,
    never by roots. Therefore NO root should entail change. -/
def bifurcationThesis (rootEntailsChange : RootType → Bool) : Prop :=
  ∀ rt, rootEntailsChange rt = false

/-- @cite{beavers-etal-2021} main result: bifurcation does not hold.
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

/-- **B&KG (2020) strengthened bifurcation failure via RootEntailments.**

    @cite{beavers-etal-2021} show roots can entail CHANGE (one templatic notion).
    B&KG (2020) show roots can entail CHANGE, CAUSATION, and MANNER —
    ALL notions traditionally reserved for templates. This is a strictly
    stronger refutation: even if one accepted that change is "special",
    roots encoding manner+cause (√GUILLOTINE, √HAND) violate bifurcation
    on three separate dimensions simultaneously.

    Witness: `RootEntailments.fullSpec` has all four features true. -/
theorem bkg_bifurcation_fails_all_dimensions :
    -- Roots can entail change (result = true)
    RootEntailments.fullSpec.result = true ∧
    -- Roots can entail causation (cause = true)
    RootEntailments.fullSpec.cause = true ∧
    -- Roots can entail manner (manner = true)
    RootEntailments.fullSpec.manner = true ∧
    -- All at once — not just one dimension
    RootEntailments.fullSpec.state = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Multiple Levin classes witness the stronger bifurcation failure. -/
theorem bkg_bifurcation_multiple_witnesses :
    (LevinClass.rootEntailments .cut).result = true ∧
    (LevinClass.rootEntailments .cut).manner = true ∧
    (LevinClass.rootEntailments .give).cause = true ∧
    (LevinClass.rootEntailments .give).manner = true := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. The Markedness Generalization (§8, eq. 44)
-- ════════════════════════════════════════════════════

/-- Whether a form is morphologically marked (=derived/complex) or
    unmarked (=basic/simple). -/
inductive Markedness where
  | unmarked  -- Basic form (no additional morphology)
  | marked    -- Derived form (overt morphological marking: -en, -ed, etc.)
  deriving DecidableEq, Repr, BEq

/-- The Markedness Generalization (Beavers et al. 2021 eq. 44).

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
-- § 7. Root Denotations (§3.6, eq. 20–21)
-- ════════════════════════════════════════════════════

/-- A root's denotation: a state predicate over entities and states.
    @cite{beavers-etal-2021} eq. 20a: ⟦√FLAT⟧ = λx.λs[flat'(x, s)]. -/
abbrev RootDenotation (Entity State : Type) := Entity → State → Prop

/-- A meaning postulate: the root's state predicate entails a prior
    change event. @cite{beavers-etal-2021} eq. 21a:
    ∀x.∀s[cracked'(x, s) → ∃e'[become'(e', s)]]. -/
def MeaningPostulateEntailsChange
    {Entity State Event : Type}
    (rootPred : RootDenotation Entity State)
    (become : Event → State → Prop) : Prop :=
  ∀ x s, rootPred x s → ∃ e, become e s

-- ════════════════════════════════════════════════════
-- § 7b. Root Denotation: Change-in-Denotation Architecture (B&KG 2020 §2.5)
-- ════════════════════════════════════════════════════

/-- Root denotation architecture (B&KG 2020 §2.5, eqs. 37a–b), where
    change is CONSTITUTIVE of the result root's meaning rather than an
    external meaning postulate (cf. Beavers et al. 2021 eq. 21).

    The formal contrast:
    - √FLAT = λxλs[flat'(x,s)] — pure state, no change in truth conditions
    - √CRACK = λxλs[cracked'(x,s) ∧ ∃e'[become'(s,e')]] — change IN the root

    The earlier @cite{beavers-etal-2021} analysis used a separate structure
    with an external meaning postulate constraining result roots. B&KG
    argue the change IS what the root means, not an external constraint.

    The empirical payoff: the *again* diagnostic's reading collapse for result
    roots (§12b below) follows logically from this architecture. If change is
    in the root, scoping *again* over root vs. over vP yields the same
    presupposition — explaining the collapse without stipulation. -/
inductive RootDen (Entity State Event : Type) where
  /-- PC root: pure state predicate. The state can hold without prior change.
      √FLAT = λxλs[flat'(x,s)] — "the table is flat" doesn't presuppose
      any prior flattening event. -/
  | pc (statePred : Entity → State → Prop)
  /-- Result root: state predicate constitutively entailing change.
      √CRACK = λxλs[cracked'(x,s) ∧ ∃e'[become'(s,e')]]
      The existential over becoming events is PART OF the root's truth
      conditions, not a separate meaning postulate. -/
  | result
    (statePred : Entity → State → Prop)
    (become : Event → State → Prop)
    (entailsChange : ∀ x s, statePred x s → ∃ e, become e s)
  /-- Manner+result root: state predicate entailing change AND manner
      restriction on the causing event (B&KG 2020 §4.5.3, eq. 74).
      √GUILLOTINE = λxλs[dead'(x,s) ∧ ∃e'∃v[cause'(v,e') ∧ become'(s,e')
                          ∧ ∀v'[cause'(v',e') → guillotining'(v')]]]
      The root packages both the result state AND a restriction on how
      that result is brought about. This violates Manner/Result
      Complementarity — manner and result coexist in one root. -/
  | mannerResult
    (statePred : Entity → State → Prop)
    (become : Event → State → Prop)
    (manner : Event → Prop)
    (entailsChange : ∀ x s, statePred x s → ∃ e, become e s)
    (entailsManner : ∀ x s, statePred x s → ∃ v, manner v)

/-- Extract the RootType from a BKG denotation.
    Manner+result roots map to `.result` at the Boolean level — they
    entail change, which is all the Chapter 2 typology cares about.
    The manner dimension is only visible at the denotation level. -/
def RootDen.rootType {Entity State Event : Type} :
    RootDen Entity State Event → RootType
  | .pc _ => .propertyConcept
  | .result _ _ _ => .result
  | .mannerResult _ _ _ _ _ => .result

/-- Extract the underlying state predicate from any root type. -/
def RootDen.statePred {Entity State Event : Type} :
    RootDen Entity State Event → (Entity → State → Prop)
  | .pc pred => pred
  | .result pred _ _ => pred
  | .mannerResult pred _ _ _ _ => pred

/-- Whether the root carries its own BECOME relation (built into the denotation). -/
def RootDen.carriesBECOME {Entity State Event : Type} :
    RootDen Entity State Event → Bool
  | .pc _ => false
  | .result _ _ _ => true
  | .mannerResult _ _ _ _ _ => true

/-- Carrying BECOME built-in is the same as entailing change.
    This connects the denotation architecture to the Boolean flag. -/
theorem RootDen.carriesBECOME_iff_entailsChange
    {Entity State Event : Type}
    (rd : RootDen Entity State Event) :
    rd.carriesBECOME = rd.rootType.entailsChange := by
  cases rd <;> rfl

/-- For result roots, the meaning postulate is DERIVED from the denotation —
    not a separate axiom. This is the formal content of B&KG's argument:
    change isn't externally constrained — it's what the root means. -/
theorem RootDen.meaning_postulate_derived
    {Entity State Event : Type}
    (pred : Entity → State → Prop) (become : Event → State → Prop)
    (h : ∀ x s, pred x s → ∃ e, become e s) :
    MeaningPostulateEntailsChange pred become :=
  h

/-- Whether the root carries a manner restriction on causation (B&KG 2020 §4.5.3).
    Only manner+result roots have this — PC and pure result roots do not
    restrict how causation proceeds. -/
def RootDen.carriesMANNER {Entity State Event : Type} :
    RootDen Entity State Event → Bool
  | .pc _ => false
  | .result _ _ _ => false
  | .mannerResult _ _ _ _ _ => true

/-- A root denotation violates MRC iff it carries both BECOME and a manner
    restriction — i.e., it encodes both result and manner in one root.
    Derived from the two independent predicates, not pattern-matched separately. -/
def RootDen.denotationViolatesMRC {Entity State Event : Type}
    (rd : RootDen Entity State Event) : Bool :=
  rd.carriesBECOME && rd.carriesMANNER

/-- Manner+result denotations violate MRC. -/
theorem RootDen.mannerResult_violates {Entity State Event : Type}
    (sp : Entity → State → Prop) (become : Event → State → Prop)
    (manner : Event → Prop)
    (hc : ∀ x s, sp x s → ∃ e, become e s) (hm : ∀ x s, sp x s → ∃ v, manner v) :
    (RootDen.mannerResult sp become manner hc hm :
      RootDen Entity State Event).denotationViolatesMRC = true := rfl

/-- Result-only denotations respect MRC. -/
theorem RootDen.result_respects {Entity State Event : Type}
    (sp : Entity → State → Prop) (become : Event → State → Prop)
    (hc : ∀ x s, sp x s → ∃ e, become e s) :
    (RootDen.result sp become hc :
      RootDen Entity State Event).denotationViolatesMRC = false := rfl

/-- PC denotations respect MRC. -/
theorem RootDen.pc_respects {Entity State Event : Type}
    (sp : Entity → State → Prop) :
    (RootDen.pc sp : RootDen Entity State Event).denotationViolatesMRC = false := rfl

/-- **Bridge: denotation-level MRC → Boolean RootEntailments MRC.**
    MRC violation requires BOTH conditions — having manner alone
    (if such a constructor existed) would not be a violation. -/
theorem RootDen.mrc_requires_both {Entity State Event : Type}
    (rd : RootDen Entity State Event)
    (h : rd.denotationViolatesMRC = true) :
    rd.carriesBECOME = true ∧ rd.carriesMANNER = true := by
  simp [RootDen.denotationViolatesMRC] at h
  exact h

-- ════════════════════════════════════════════════════
-- § 7c. Ditransitive Root Classes (B&KG 2020 Ch. 3)
-- ════════════════════════════════════════════════════

/-- What a ditransitive root entails about possession (B&KG 2020 §3.3).
    Templates always introduce PROSPECTIVE possession (via ◇ modality).
    Whether the ROOT adds actual or prospective possession on top
    determines cancellability:
    "gave X the ball, #but X never had it" vs.
    "sent X the ball, but it never arrived" (OK). -/
inductive PossessionEntailment where
  | none        -- root says nothing about possession (template provides ◇have')
  | prospective -- root entails future/intended possession (√PROMISE, √OWE)
  | actual      -- root entails actual possession transfer (√GIVE, √HAND)
  deriving DecidableEq, Repr, BEq

/-- Six classes of ditransitive verb roots (B&KG 2020 §3.6).
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
  deriving DecidableEq, Repr, BEq

/-- What a ditransitive root entails about the transfer event.
    Each field is a distinct semantic entailment from the ROOT,
    independent of what the template provides. -/
structure DitransitiveEntailments where
  possession    : PossessionEntailment
  causedMotion  : Bool  -- root entails caused motion of theme
  manner        : Bool  -- root specifies manner of transfer/motion
  accompaniment : Bool  -- root entails agent accompanies theme
  deriving DecidableEq, BEq, Repr

/-- Entailment profile for each ditransitive root class (B&KG 2020 §3.6). -/
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

-- ════════════════════════════════════════════════════
-- § 7d. Ditransitive Root Denotations (B&KG 2020 §3.5–3.6)
-- ════════════════════════════════════════════════════

/-- A ditransitive root's denotation (B&KG 2020 §3.5, eqs. 46–55).
    Parallel to `RootDen` for CoS roots (§7b).

    The formal contrast:
    - √SEND = λyλzλe[send'(y,z,e)] — event predicate only
    - √GIVE = λyλzλe[give'(y,z,e) ∧ have'(z,y)] — possession IN the root

    Templates always add prospective possession (via ◇). Whether the root
    ALSO adds actual possession determines cancellation behavior, telicity,
    and *again* readings — the same architecture as CoS roots with BECOME. -/
inductive DitransitiveDen (Entity Event : Type) where
  /-- Root WITHOUT possession entailment. Like PC roots for CoS:
      the template provides the (prospective) possession. -/
  | simple (eventPred : Entity → Entity → Event → Prop)
  /-- Root WITH actual possession entailment. Like result roots for CoS:
      possession is IN the root's truth conditions.
      The `entailsPoss` proof is constitutive — not a meaning postulate. -/
  | withPossession
    (eventPred : Entity → Entity → Event → Prop)
    (possess : Entity → Entity → Prop)
    (entailsPoss : ∀ y z e, eventPred y z e → possess z y)

/-- Whether possession is cancelable for a verb with this root.
    Root-entailed actual possession is NOT cancelable; template-only
    prospective possession IS cancelable.

    Structural parallel to `RootDen.carriesBECOME`: root-constitutive
    content cannot be canceled in either domain. -/
def DitransitiveDen.possessionCancelable {Entity Event : Type} :
    DitransitiveDen Entity Event → Bool
  | .simple _ => true
  | .withPossession _ _ _ => false

/-- A send-type denotation (simple) has cancelable possession. -/
theorem simple_possession_cancelable {Entity Event : Type}
    (ep : Entity → Entity → Event → Prop) :
    (DitransitiveDen.simple ep :
      DitransitiveDen Entity Event).possessionCancelable = true := rfl

/-- A give-type denotation (withPossession) has uncancelable possession. -/
theorem withPossession_not_cancelable {Entity Event : Type}
    (ep : Entity → Entity → Event → Prop) (poss : Entity → Entity → Prop)
    (h : ∀ y z e, ep y z e → poss z y) :
    (DitransitiveDen.withPossession ep poss h :
      DitransitiveDen Entity Event).possessionCancelable = false := rfl

-- ════════════════════════════════════════════════════
-- § 7e. MRC Diagnostics (B&KG 2020 §§4.2–4.3)
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
  deriving DecidableEq, Repr, BEq

/-- Whether a diagnostic tests for result entailment. -/
def MRCDiagnostic.testsResult : MRCDiagnostic → Bool
  | .denialOfResult => true
  | .objectDeletion => true
  | .restrictedResultatives => true
  | _ => false

/-- Whether a diagnostic tests for manner entailment. -/
def MRCDiagnostic.testsManner : MRCDiagnostic → Bool
  | .selectionalRestriction => true
  | .denialOfAction => true
  | .actorParaphrase => true
  | _ => false

/-- Each diagnostic tests for exactly one of manner or result. -/
theorem diagnostic_exclusive (d : MRCDiagnostic) :
    d.testsResult = !d.testsManner := by
  cases d <;> rfl

/-- A verb's diagnostic profile: which of the six diagnostics it passes.
    B&KG (2020 §§4.2–4.3) survey these for each verb class. -/
structure MRCDiagnosticProfile where
  denialOfResult         : Bool
  objectDeletion         : Bool
  restrictedResultatives : Bool
  selectionalRestriction : Bool
  denialOfAction         : Bool
  actorParaphrase   : Bool
  deriving DecidableEq, BEq, Repr

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

/-- Cut is MRC-violating by BOTH diagnostics AND RootEntailments. -/
theorem cut_diagnostics_match_entailments :
    cutDiagnostics.showsMRCViolation =
    (LevinClass.rootEntailments .cut).violatesMRC := rfl

/-- Break is MRC-respecting by BOTH diagnostics AND RootEntailments. -/
theorem break_diagnostics_match_entailments :
    breakDiagnostics.showsMRCViolation =
    (LevinClass.rootEntailments .break_).violatesMRC := rfl

/-- Hit is MRC-respecting by BOTH diagnostics AND RootEntailments. -/
theorem hit_diagnostics_match_entailments :
    hitDiagnostics.showsMRCViolation =
    (LevinClass.rootEntailments .hit).violatesMRC := rfl

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

/-- A result root's object has changeOfState = true. -/
theorem result_object_has_changeOfState :
    (rootTypeFromChangeEntailment kickObjectProfile) = .result := by
  native_decide

/-- Die subject undergoes change → result-type pattern. -/
theorem die_result_pattern :
    (rootTypeFromChangeEntailment dieSubjectProfile) = .result := by
  native_decide

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
-- § 11. Embick (2004) Adjectival Structures (§3.2, eq. 8)
-- ════════════════════════════════════════════════════

/-- @cite{embick-2004} posits two adjectival structures:

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
  deriving DecidableEq, Repr, BEq

/-- PC roots admit both structures; result roots only admit resultStative. -/
def RootType.admitsBasicStative : RootType → Bool
  | .propertyConcept => true
  | .result => false

/-- This is equivalent to NOT entailing change. -/
theorem admitsBasicStative_iff_no_change (rt : RootType) :
    rt.admitsBasicStative = true ↔ rt.entailsChange = false := by
  cases rt <;> simp [RootType.admitsBasicStative, RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 12. The Again Diagnostic (§3.4, eq. 14–16)
-- ════════════════════════════════════════════════════

/-- Sublexical modifier 'again' has two readings:

    (14a) RESTITUTIVE: again attaches to just the root
          → restores a prior state (one sharpening event)
    (14b) REPETITIVE: again attaches to the whole vP (including v_become)
          → repeats the entire change event (two sharpenings)

    Under the non-bifurcated analysis:
    - PC roots: again over √ROOT yields a pure state → restitutive OK
    - Result roots: again over √ROOT still entails change (root has it)
      → restitutive reading collapses into repetitive -/
inductive AgainReading where
  | restitutive   -- again scopes over root only
  | repetitive    -- again scopes over vP (includes BECOME)
  deriving DecidableEq, Repr, BEq

/-- Which readings of 'again' are available for each root type. -/
def RootType.againReadings : RootType → List AgainReading
  | .propertyConcept => [.restitutive, .repetitive]
  | .result => [.repetitive]

/-- PC roots have strictly more 'again' readings than result roots. -/
theorem pc_more_again_readings :
    (RootType.againReadings .propertyConcept).length >
    (RootType.againReadings .result).length := by native_decide

/-- Result roots lack the restitutive reading. -/
theorem result_no_restitutive :
    ¬ AgainReading.restitutive ∈ RootType.againReadings .result := by
  simp [RootType.againReadings]

/-- PC roots have the restitutive reading. -/
theorem pc_has_restitutive :
    AgainReading.restitutive ∈ RootType.againReadings .propertyConcept := by
  simp [RootType.againReadings]

-- ════════════════════════════════════════════════════
-- § 12b. Again Diagnostic: Compositional Derivation (B&KG 2020 §2.5)
-- ════════════════════════════════════════════════════

/-- What *again* presupposes at a given scope position.

    *again* is a presupposition trigger: attaching it to constituent C
    presupposes that C's denotation held at some prior time. The distinction
    between priorState and priorChange determines whether restitutive and
    repetitive readings are distinct or collapse into one. -/
inductive AgainPresupposition where
  | priorState   -- presupposes a prior state held (no change implied)
  | priorChange  -- presupposes a prior change event occurred
  deriving DecidableEq, Repr, BEq

/-- What *again* presupposes when scoping over just the root.

    For PC roots (√FLAT): *again*[√FLAT](x) presupposes x was previously flat.
    This is a pure state presupposition — no change is implied.

    For result roots (√CRACK): *again*[√CRACK](x) presupposes x was previously
    cracked. But √CRACK's denotation INCLUDES ∃e'[become'(s,e')], so this
    presupposition ENTAILS a prior change event.

    For manner+result roots (√GUILLOTINE): *again* over the root presupposes
    prior change+manner. The root packages BECOME + manner restriction,
    so root-scope *again* entails a prior mannered change event (§4.5.2). -/
def RootDen.againOverRoot {Entity State Event : Type} :
    RootDen Entity State Event → AgainPresupposition
  | .pc _ => .priorState
  | .result _ _ _ => .priorChange
  | .mannerResult _ _ _ _ _ => .priorChange

/-- What *again* presupposes when scoping over vP (v_become + root).
    Always presupposes prior change, regardless of root type, because
    v_become introduces BECOME compositionally. -/
def againOverVP : AgainPresupposition := .priorChange

/-- PC roots: root-scope and vP-scope *again* yield DISTINCT presuppositions.
    Root-scope → prior state (no change); vP-scope → prior change.
    Two distinct presuppositions → two available readings. -/
theorem pc_again_distinct {Entity State Event : Type}
    (pred : Entity → State → Prop) :
    (RootDen.pc pred : RootDen Entity State Event).againOverRoot ≠
    (againOverVP : AgainPresupposition) := by
  simp [RootDen.againOverRoot, againOverVP]

/-- Result roots: root-scope and vP-scope *again* yield THE SAME presupposition.
    Both presuppose prior change — root-scope because change is in the
    denotation, vP-scope because v_become introduces it.
    Same presupposition → readings collapse into one. -/
theorem result_again_collapsed {Entity State Event : Type}
    (pred : Entity → State → Prop) (become : Event → State → Prop)
    (h : ∀ x s, pred x s → ∃ e, become e s) :
    (RootDen.result pred become h : RootDen Entity State Event).againOverRoot =
    (againOverVP : AgainPresupposition) := rfl

/-- Predicted *again* readings from the BKG denotation architecture.
    Distinct presuppositions → both readings available.
    Collapsed presuppositions → only repetitive.
    Manner+result roots collapse like result roots — the manner
    restriction adds no new scope point because it's within the root. -/
def RootDen.predictedAgainReadings {Entity State Event : Type} :
    RootDen Entity State Event → List AgainReading
  | .pc _ => [.restitutive, .repetitive]
  | .result _ _ _ => [.repetitive]
  | .mannerResult _ _ _ _ _ => [.repetitive]

/-- **The key bridge**: the BKG denotation architecture predicts the SAME
    again-reading distribution as the Boolean `RootType.againReadings`.

    This validates the compositional explanation: the reading collapse
    for result roots is not stipulated — it follows from change being
    constitutive of the root's meaning. The Boolean function encodes
    the SAME prediction, but the compositional analysis explains WHY. -/
theorem bkg_again_matches_boolean {Entity State Event : Type}
    (rd : RootDen Entity State Event) :
    rd.predictedAgainReadings = rd.rootType.againReadings := by
  cases rd <;> rfl

-- ════════════════════════════════════════════════════
-- § 12c. Ditransitive Telicity and *Again* (B&KG 2020 §§3.7, 3.9)
-- ════════════════════════════════════════════════════

/-- Whether a ditransitive verb is obligatorily telic in the IO frame
    (B&KG 2020 §3.7).

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

/-- What *again* presupposes over the root of a ditransitive denotation.
    Parallel to `RootDen.againOverRoot` (§12b): root-constitutive content
    makes root-scope and vP-scope *again* collapse.

    -.withPossession: root carries possession → *again* over root
      presupposes prior possession (= prior change) → collapse
    -.simple: root has no possession → *again* over root presupposes
      prior event only (= prior state) → distinct readings -/
def DitransitiveDen.againOverRoot {Entity Event : Type} :
    DitransitiveDen Entity Event → AgainPresupposition
  | .simple _ => .priorState
  | .withPossession _ _ _ => .priorChange

/-- *again* over the ditransitive vP always presupposes prior caused
    possession (from template CAUSE + ◇have'). -/
def againOverDitransitiveVP : AgainPresupposition := .priorChange

/-- Give-type: root-scope and vP-scope *again* yield the SAME
    presupposition. Parallel to `result_again_collapsed`. -/
theorem give_den_again_collapsed {Entity Event : Type}
    (ep : Entity → Entity → Event → Prop) (poss : Entity → Entity → Prop)
    (h : ∀ y z e, ep y z e → poss z y) :
    (DitransitiveDen.withPossession ep poss h :
      DitransitiveDen Entity Event).againOverRoot =
    againOverDitransitiveVP := rfl

/-- Send-type: root-scope and vP-scope *again* yield DISTINCT
    presuppositions. Parallel to `pc_again_distinct`. -/
theorem send_den_again_distinct {Entity Event : Type}
    (ep : Entity → Entity → Event → Prop) :
    (DitransitiveDen.simple ep :
      DitransitiveDen Entity Event).againOverRoot ≠
    againOverDitransitiveVP := by
  simp [DitransitiveDen.againOverRoot, againOverDitransitiveVP]

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
-- § 12d. Manner+Result Roots and *Again* (B&KG 2020 §4.5.2)
-- ════════════════════════════════════════════════════

/-- Manner+result roots: root-scope and vP-scope *again* yield THE SAME
    presupposition, just like pure result roots. But the reason is RICHER:
    the root packages BECOME + manner, so root-scope *again* presupposes
    a prior mannered change event — which is strictly MORE than what
    vP-scope presupposes (just prior change).

    Observable prediction: only repetitive reading available.
    Same as result roots, but for a different reason — manner is also
    caught in the collapse because it's inside the root. -/
theorem mannerResult_again_collapsed {Entity State Event : Type}
    (sp : Entity → State → Prop) (become : Event → State → Prop)
    (manner : Event → Prop)
    (hc : ∀ x s, sp x s → ∃ e, become e s) (hm : ∀ x s, sp x s → ∃ v, manner v) :
    (RootDen.mannerResult sp become manner hc hm :
      RootDen Entity State Event).againOverRoot =
    (againOverVP : AgainPresupposition) := rfl

/-- Manner+result roots lack the restitutive reading. -/
theorem mannerResult_no_restitutive {Entity State Event : Type}
    (sp : Entity → State → Prop) (become : Event → State → Prop)
    (manner : Event → Prop)
    (hc : ∀ x s, sp x s → ∃ e, become e s) (hm : ∀ x s, sp x s → ∃ v, manner v) :
    (RootDen.mannerResult sp become manner hc hm :
      RootDen Entity State Event).predictedAgainReadings = [.repetitive] := rfl

/-- The three-way root denotation typology (B&KG 2020 §4.5.5):
    PC, result, and manner+result roots ALL correctly predict *again*
    readings via the unified `bkg_again_matches_boolean` bridge.

    PC roots: two readings (restitutive + repetitive)
    Result roots: one reading (repetitive) — change in root
    Manner+result roots: one reading (repetitive) — change + manner in root -/
theorem three_way_again_summary :
    -- PC roots: two readings (restitutive + repetitive)
    (RootType.againReadings .propertyConcept).length = 2 ∧
    -- Result roots: one reading (repetitive only)
    (RootType.againReadings .result).length = 1 ∧
    -- Manner+result roots: also one reading (from denotation-level collapse)
    ∀ {Entity State Event : Type} (mr : RootDen Entity State Event),
      mr.denotationViolatesMRC = true →
      mr.predictedAgainReadings.length = 1 := by
  refine ⟨rfl, rfl, ?_⟩
  intro Entity State Event mr hmr
  cases mr with
  | pc _ => simp [RootDen.denotationViolatesMRC, RootDen.carriesBECOME, RootDen.carriesMANNER] at hmr
  | result _ _ _ => simp [RootDen.denotationViolatesMRC, RootDen.carriesBECOME, RootDen.carriesMANNER] at hmr
  | mannerResult _ _ _ _ _ => rfl

/-- **Bridge: MRC-violating roots → collapsed *again* readings.**
    If a root denotation violates MRC (manner+result), it has only
    repetitive *again*. The diagnostic MRC violation predicts the
    *again* collapse. -/
theorem mrc_violation_implies_again_collapse {Entity State Event : Type}
    (rd : RootDen Entity State Event)
    (h : rd.denotationViolatesMRC = true) :
    rd.predictedAgainReadings = [.repetitive] := by
  cases rd with
  | pc _ => simp [RootDen.denotationViolatesMRC, RootDen.carriesBECOME, RootDen.carriesMANNER] at h
  | result _ _ _ => simp [RootDen.denotationViolatesMRC, RootDen.carriesBECOME, RootDen.carriesMANNER] at h
  | mannerResult _ _ _ _ _ => rfl

/-- **Bridge: MRC-respecting result roots → collapsed *again* too.**
    Collapsed *again* is necessary but NOT sufficient for MRC violation.
    Pure result roots also collapse, but they don't violate MRC. -/
theorem again_collapse_not_sufficient_for_mrc {Entity State Event : Type}
    (sp : Entity → State → Prop) (become : Event → State → Prop)
    (hc : ∀ x s, sp x s → ∃ e, become e s) :
    (RootDen.result sp become hc :
      RootDen Entity State Event).predictedAgainReadings = [.repetitive] ∧
    (RootDen.result sp become hc :
      RootDen Entity State Event).denotationViolatesMRC = false := ⟨rfl, rfl⟩

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
def Root.verbalMarkedness (r : Root) : Markedness :=
  _root_.verbalMarkedness r.changeType

/-- Predicted stative markedness from change entailment. -/
def Root.stativeMarkedness (r : Root) : Markedness :=
  _root_.stativeMarkedness r.changeType

-- ════════════════════════════════════════════════════
-- § 16. Cross-Classification: Arity × Change Entailment
-- ════════════════════════════════════════════════════

-- Witnesses for all four cells of the 2×2 cross-classification.

/-- √BREAK: selects theme + entails change (result root, Levin 45.1).
    "Break X" — the root obligatorily takes a patient that undergoes
    breaking, and the root lexically entails a prior change event. -/
def Root.break_ : Root :=
  { arity := .selectsTheme, changeType := .result,
    denotationType := some .eventPred, levinClass := some .break_ }

/-- √HIT: selects theme + does not entail change (Levin 18.1).
    "Hit X" — the root takes a contactee, but hitting does not entail
    that the patient undergoes a change of state (Levin 1993 pp. 5–8).
    `.propertyConcept` is used broadly here: the formal content
    (`entailsChange = false`) is what matters, not the label. -/
def Root.hit : Root :=
  { arity := .selectsTheme, changeType := .propertyConcept,
    denotationType := some .eventPred, levinClass := some .hit }

/-- √DIE: no theme + entails change.
    "Die" — intransitive; the dying entity is introduced by functional
    structure (unaccusative vGO/vBE), not selected by the root. Dying
    lexically entails a prior change event (becoming dead). -/
def Root.die : Root :=
  { arity := .noTheme, changeType := .result,
    denotationType := some .eventPred }

/-- √SIT: no theme + does not entail change (positional root).
    "Sit" — Coon's √POS class: denotes a spatial configuration state.
    No internal argument, no entailed change. -/
def Root.sit : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .measureFn, levinClass := some .assumePosition }

/-- **Orthogonality of arity and change entailment.**

    All four cells of the 2×2 cross-classification are inhabited.
    This proves the two dimensions are genuinely independent:
    knowing that a root selects a theme tells you nothing about
    whether it entails change, and vice versa. -/
theorem arity_changeType_orthogonal :
    (∃ r : Root, r.arity = .selectsTheme ∧ r.changeType = .result) ∧
    (∃ r : Root, r.arity = .selectsTheme ∧ r.changeType = .propertyConcept) ∧
    (∃ r : Root, r.arity = .noTheme ∧ r.changeType = .result) ∧
    (∃ r : Root, r.arity = .noTheme ∧ r.changeType = .propertyConcept) :=
  ⟨⟨.break_, rfl, rfl⟩, ⟨.hit, rfl, rfl⟩, ⟨.die, rfl, rfl⟩, ⟨.sit, rfl, rfl⟩⟩

/-- **Change entailment does not determine arity** (and vice versa).

    Beavers et al.'s grand unification (§14) shows that `entailsChange`
    determines ALL morphosyntactic correlates (markedness, simple stative,
    again readings, template requirements). But it determines NOTHING
    about internal argument selection. Coon's arity adds an independent
    dimension of prediction: whether the root will surface with an
    internal argument across voice alternations. -/
theorem change_does_not_determine_arity :
    (∃ r : Root, r.entailsChange = true ∧ r.arity = .selectsTheme) ∧
    (∃ r : Root, r.entailsChange = true ∧ r.arity = .noTheme) ∧
    (∃ r : Root, r.entailsChange = false ∧ r.arity = .selectsTheme) ∧
    (∃ r : Root, r.entailsChange = false ∧ r.arity = .noTheme) :=
  ⟨⟨.break_, rfl, rfl⟩, ⟨.die, rfl, rfl⟩, ⟨.hit, rfl, rfl⟩, ⟨.sit, rfl, rfl⟩⟩

/-- **Theme persistence** (Coon 2019 main empirical claim).

    If a root selects a theme, the internal argument persists regardless
    of what v/Voice⁰ head combines with it. In Chuj, √TV roots surface
    with an internal argument in transitive (Ø), passive (-ch, -j),
    and antipassive (-w) constructions alike.

    This is expressed by design: `arity` is a field of `Root`, not of
    the derived verb. No functional head modifies it. -/
theorem theme_persistence (r : Root) (h : r.arity = .selectsTheme) :
    r.arity.hasInternalArg = true := by
  simp [h, RootArity.hasInternalArg]

/-- Change entailment determines markedness in the unified Root. -/
theorem root_markedness_from_change (r : Root) :
    r.verbalMarkedness = .unmarked ↔ r.entailsChange = true := by
  cases r with | mk arity changeType _ _ _ =>
  cases changeType <;> simp [Root.verbalMarkedness, Root.entailsChange,
    verbalMarkedness, RootType.entailsChange]

/-- Roots with the same change type have identical morphosyntactic
    behavior regardless of arity — markedness, stative forms, and
    again readings are orthogonal to internal argument selection. -/
theorem same_change_same_morphosyntax (r₁ r₂ : Root)
    (h : r₁.changeType = r₂.changeType) :
    r₁.verbalMarkedness = r₂.verbalMarkedness ∧
    r₁.stativeMarkedness = r₂.stativeMarkedness ∧
    r₁.entailsChange = r₂.entailsChange := by
  simp [Root.verbalMarkedness, Root.stativeMarkedness, Root.entailsChange, h]

-- ════════════════════════════════════════════════════
-- § 17. Root Position in Event Structure (B&KG 2020 §5.4.1, Table 12)
-- ════════════════════════════════════════════════════

/-- Where a root sits in event structure (B&KG 2020 §5.4.1).

    - **complement**: under v_become, filling the result/state slot.
      The root provides the state that BECOME operates on.
      Examples: √FLAT, √CRACK, √DROWN.
    - **adjoined**: to v_cause/v_act, modifying the causing event.
      The root specifies the manner of the activity.
      Examples: √JOG, √TOSS, √HAND.

    Position is NOT determined solely by the 4 entailment features.
    √DROWN and √TOSS have identical features (+S,+M,+R,+C) but differ
    in position — √DROWN is complement (manner restricts how the state
    is caused), √TOSS is adjoined (manner is the primary event,
    which happens to cause a state change). -/
inductive RootPosition where
  | complement  -- under v_become: root fills the result/state slot
  | adjoined    -- to v_cause: root modifies the causing event
  deriving DecidableEq, Repr, BEq

/-- Full root specification: entailment features + structural position.
    This is B&KG's (2020) Table 12 in full — the 4 binary entailment
    features × 2 positions give 32 theoretical cells, of which 7 are
    attested and the rest are principled gaps. -/
structure FullRootSpec where
  entailments : RootEntailments
  position : RootPosition
  deriving DecidableEq, BEq, Repr

/-- Adjoined position requires +manner: a root in adjunct position
    must specify a manner of action. Without manner, there is nothing
    to adjoin — the adjunct slot expects an action modifier. -/
def FullRootSpec.positionLicensed (s : FullRootSpec) : Bool :=
  match s.position with
  | .adjoined => s.entailments.manner
  | .complement => true

/-- +manner +state −result −cause is semantically incoherent (B&KG §5.4.1):
    the root would specify both a manner of action and a state, but with
    no result or cause linking them. What would such a verb mean?
    "Perform manner M while in state S" — with no causal connection. -/
def FullRootSpec.semanticallyCoherent (s : FullRootSpec) : Bool :=
  !(s.entailments.manner && s.entailments.state &&
    !s.entailments.result && !s.entailments.cause)

/-- Full well-formedness: entailment constraints + position licensing +
    semantic coherence. -/
def FullRootSpec.wellFormed (s : FullRootSpec) : Bool :=
  s.entailments.wellFormed && s.positionLicensed && s.semanticallyCoherent

/-! ### Attested cells of Table 12 -/

/-- √FLAT: +S −M −R −C, complement. Property concept root. -/
def FullRootSpec.flat : FullRootSpec := ⟨.propertyConcept, .complement⟩

/-- √BLOSSOM: +S −M +R −C, complement. Pure result root. -/
def FullRootSpec.blossom : FullRootSpec := ⟨.pureResult, .complement⟩

/-- √CRACK: +S −M +R +C, complement. Causative result root. -/
def FullRootSpec.crack : FullRootSpec := ⟨.causativeResult, .complement⟩

/-- √JOG: −S +M −R −C, adjoined. Pure manner root. -/
def FullRootSpec.jog : FullRootSpec := ⟨.pureManner, .adjoined⟩

/-- √DROWN: +S +M +R +C, complement. Manner+result in complement position —
    the manner restricts HOW the state is caused. -/
def FullRootSpec.drown : FullRootSpec := ⟨.fullSpec, .complement⟩

/-- √TOSS: +S +M +R +C, adjoined. Manner+result in adjunct position —
    the manner is the primary event that happens to cause a state change. -/
def FullRootSpec.toss : FullRootSpec := ⟨.fullSpec, .adjoined⟩

/-- √HAND: same entailments + position as √TOSS. The difference is in
    the ditransitive layer (DitransitiveRootClass.causedPossession vs
.ballisticMotion), not in FullRootSpec's 4+1 features. -/
abbrev FullRootSpec.hand : FullRootSpec := FullRootSpec.toss

/-- √EXIST: −S −M −R −C, complement. Minimal stative root. -/
def FullRootSpec.exist : FullRootSpec := ⟨.minimal, .complement⟩

-- All attested types are well-formed
theorem flat_wf : FullRootSpec.flat.wellFormed = true := rfl
theorem blossom_wf : FullRootSpec.blossom.wellFormed = true := rfl
theorem crack_wf : FullRootSpec.crack.wellFormed = true := rfl
theorem jog_wf : FullRootSpec.jog.wellFormed = true := rfl
theorem drown_wf : FullRootSpec.drown.wellFormed = true := rfl
theorem toss_wf : FullRootSpec.toss.wellFormed = true := rfl
theorem hand_wf : FullRootSpec.hand.wellFormed = true := rfl
theorem exist_wf : FullRootSpec.exist.wellFormed = true := rfl

/-- √DROWN and √TOSS have identical entailments but different positions. -/
theorem drown_toss_same_entailments :
    FullRootSpec.drown.entailments = FullRootSpec.toss.entailments := rfl

theorem drown_toss_diff_position :
    FullRootSpec.drown.position ≠ FullRootSpec.toss.position := by
  simp [FullRootSpec.drown, FullRootSpec.toss]

-- ════════════════════════════════════════════════════
-- § 18. Root → Templatic Head Prediction (B&KG 2020 Table 13)
-- ════════════════════════════════════════════════════

/-- Templatic functional heads in event structure (B&KG 2020 Table 13).

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
  deriving DecidableEq, Repr, BEq

/-- Bridge to event structure primitives. The three verbal heads
    correspond to R&L (1998) primitives; the prepositional heads
    are not event-structural primitives. -/
def TemplateHead.toPrimitive : TemplateHead → Option Primitive
  | .vAct => some .ACT
  | .vCause => some .CAUSE
  | .vBecome => some .BECOME
  | .pLoc => none
  | .pHave => none

/-- Which template heads a root's entailments make redundant (Table 13).

    The mapping is monotone: more root entailments → more heads entailed.

    - +result → v_become (root entails the change v_become would provide)
    - +cause → v_cause (root entails the causation v_cause would provide)
    - +manner ∧ +cause → v_act (manner that causes = activity)
    - +manner alone → no v_act (manner without causation doesn't entail
      activity — √JOG specifies jogging manner but v_act still provides
      the activity frame) -/
def RootEntailments.entailedHeads (r : RootEntailments) : List TemplateHead :=
  (if r.result then [.vBecome] else []) ++
  (if r.cause then [.vCause] else []) ++
  (if r.manner && r.cause then [.vAct] else [])

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
    RootEntailments.pureManner.entailedHeads = [] := rfl

/-- √FLAT (propertyConcept): no template heads entailed.
    The root names a state, but doesn't entail change or cause. -/
theorem flat_no_heads :
    RootEntailments.propertyConcept.entailedHeads = [] := rfl

/-- √BLOSSOM (pureResult): v_become entailed.
    The root entails change — v_become's contribution is redundant. -/
theorem blossom_heads :
    RootEntailments.pureResult.entailedHeads = [.vBecome] := rfl

/-- √CRACK (causativeResult): v_become + v_cause entailed.
    The root entails change AND causation. -/
theorem crack_heads :
    RootEntailments.causativeResult.entailedHeads = [.vBecome, .vCause] := rfl

/-- √DROWN (fullSpec): v_become + v_cause + v_act entailed.
    The root entails change, causation, AND activity (manner that causes). -/
theorem drown_heads :
    RootEntailments.fullSpec.entailedHeads = [.vBecome, .vCause, .vAct] := rfl

/-- √TOSS (fullSpec + ballistic): v_become + v_cause + v_act + P_loc.
    Verbal heads from entailments + P_loc from ditransitive class. -/
theorem toss_heads :
    RootEntailments.fullSpec.entailedHeads ++
    DitransitiveRootClass.additionalHeads .ballisticMotion =
    [.vBecome, .vCause, .vAct, .pLoc] := rfl

/-- √HAND (fullSpec + causedPossession): all 5 heads.
    Verbal heads from entailments + P_loc + P_have from ditransitive class. -/
theorem hand_heads :
    RootEntailments.fullSpec.entailedHeads ++
    DitransitiveRootClass.additionalHeads .causedPossession =
    [.vBecome, .vCause, .vAct, .pLoc, .pHave] := rfl

/-- Monotonicity: more root entailments → weakly more heads entailed.
    Pure result ⊂ causative result ⊂ full spec (by inclusion). -/
theorem heads_monotone :
    RootEntailments.pureResult.entailedHeads.length ≤
    RootEntailments.causativeResult.entailedHeads.length ∧
    RootEntailments.causativeResult.entailedHeads.length ≤
    RootEntailments.fullSpec.entailedHeads.length := ⟨by native_decide, by native_decide⟩

/-- All entailed heads for verbal template heads correspond to
    event structure primitives. -/
theorem verbal_heads_have_primitives :
    (TemplateHead.vAct.toPrimitive).isSome = true ∧
    (TemplateHead.vCause.toPrimitive).isSome = true ∧
    (TemplateHead.vBecome.toPrimitive).isSome = true := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 19. Gap Predictions (B&KG 2020 §5.4.1, Table 12)
-- ════════════════════════════════════════════════════

/-- Whether a FullRootSpec cell is attested in B&KG's Table 12. -/
def FullRootSpec.isAttestedCell (s : FullRootSpec) : Bool :=
  s.wellFormed &&
  match s.entailments, s.position with
  -- Attested complement types
  | ⟨true, false, false, false⟩, .complement => true   -- √FLAT
  | ⟨true, false, true, false⟩,  .complement => true   -- √BLOSSOM
  | ⟨true, false, true, true⟩,   .complement => true   -- √CRACK
  | ⟨true, true, true, true⟩,    .complement => true   -- √DROWN
  | ⟨false, false, false, false⟩, .complement => true   -- √EXIST
  -- Attested adjoined types
  | ⟨false, true, false, false⟩, .adjoined => true      -- √JOG
  | ⟨true, true, true, true⟩,    .adjoined => true      -- √TOSS/√HAND
  -- Everything else is a gap
  | _, _ => false

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
    (FullRootSpec.mk .propertyConcept .adjoined).positionLicensed = false := rfl

theorem gap_adjoined_result :
    (FullRootSpec.mk .pureResult .adjoined).positionLicensed = false := rfl

theorem gap_adjoined_causativeResult :
    (FullRootSpec.mk .causativeResult .adjoined).positionLicensed = false := rfl

theorem gap_adjoined_minimal :
    (FullRootSpec.mk .minimal .adjoined).positionLicensed = false := rfl

/-- Gap type 2: +manner +state −result −cause is incoherent. -/
theorem gap_manner_state_no_result :
    (FullRootSpec.mk ⟨true, true, false, false⟩ .complement).semanticallyCoherent = false := rfl

theorem gap_manner_state_no_result_adj :
    (FullRootSpec.mk ⟨true, true, false, false⟩ .adjoined).semanticallyCoherent = false := rfl

/-- Gap type 3: well-formedness violations. -/
theorem gap_result_no_state :
    (RootEntailments.mk false false true false).wellFormed = false := rfl

theorem gap_cause_no_result :
    (RootEntailments.mk true false false true).wellFormed = false := rfl

/-! ### Attested cells are well-formed and recognized -/

theorem flat_attested : FullRootSpec.flat.isAttestedCell = true := rfl
theorem blossom_attested : FullRootSpec.blossom.isAttestedCell = true := rfl
theorem crack_attested : FullRootSpec.crack.isAttestedCell = true := rfl
theorem jog_attested : FullRootSpec.jog.isAttestedCell = true := rfl
theorem drown_attested : FullRootSpec.drown.isAttestedCell = true := rfl
theorem toss_attested : FullRootSpec.toss.isAttestedCell = true := rfl
theorem exist_attested : FullRootSpec.exist.isAttestedCell = true := rfl

/-- The open question: +S +M +R −C (mannerResult without cause) in
    complement position. B&KG note this cell may be inhabited by
    verbs like *slide* — manner of motion + change of location,
    without external causation. Left as NOT attested per Table 12,
    pending further research. -/
theorem mannerResult_complement_unattested :
    (FullRootSpec.mk .mannerResult .complement).isAttestedCell = false := rfl

/-- The complement/adjoined split for fullSpec roots is the only
    case where position differentiates otherwise identical entailments. -/
theorem fullSpec_both_positions :
    FullRootSpec.drown.isAttestedCell = true ∧
    FullRootSpec.toss.isAttestedCell = true ∧
    FullRootSpec.drown.entailments = FullRootSpec.toss.entailments := ⟨rfl, rfl, rfl⟩

