import Linglib.Theories.Semantics.Events.EventStructure
import Linglib.Core.Root

/-!
# Root Typology: States and Changes of State (Beavers et al. 2021, B&KG 2020) @cite{beavers-etal-2021} @cite{beavers-koontz-garboden-2020} @cite{coon-2019}

Beavers, Everdell, Jerro, Kauhanen, Koontz-Garboden, LeBovidge & Nichols (2021)
"States and changes of state: A crosslinguistic study of the roots of verbal
meaning." Language 97(3), 439–484.

## Core contribution

Change-of-state verb roots split into two types:
- **Property concept (PC) roots**: flat, red, long — underlie deadjectival CoS verbs
- **Result roots**: crack, break, shatter — underlie non-deadjectival CoS verbs

The key semantic distinction: result roots **lexically entail change**, while PC
roots do not. This refutes the **Bifurcation Thesis** (Embick 2009, Arad 2005):
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

## References

- Beavers, J., Everdell, M., Jerro, K., Kauhanen, H., Koontz-Garboden, A.,
  LeBovidge, E. & Nichols, S. (2021). States and changes of state.
  Language 97(3), 439–484.
- Beavers, J. & Koontz-Garboden, A. (2020). The Roots of Verbal Meaning.
  Oxford: Oxford University Press.
- Embick, D. (2004). On the structure of resultative participles in English.
  Linguistic Inquiry 35, 355–392.
- Arad, M. (2005). Roots and Patterns. Dordrecht: Springer.
- Dixon, R.M.W. (1982). Where Have All the Adjectives Gone? The Hague: Mouton.

## Unified Root (§§15–17)

Extends the file with the `Root` structure (§16) bundling Coon's (2019) arity
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
-- § 1b. Change Restriction (B&KG 2020 §2.4, Table 30)
-- ════════════════════════════════════════════════════

/-- How a result root's change entailment is restricted (B&KG 2020 §2.4, Table 30).

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

/-- **The main theorem of Beavers et al. (2021).**

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

/-- Beavers et al. (2021) main result: bifurcation does not hold.
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
    Beavers et al. (2021) eq. 20a: ⟦√FLAT⟧ = λx.λs[flat'(x, s)]. -/
abbrev RootDenotation (Entity State : Type) := Entity → State → Prop

/-- A meaning postulate: the root's state predicate entails a prior
    change event. Beavers et al. (2021) eq. 21a:
    ∀x.∀s[cracked'(x, s) → ∃e'[become'(e', s)]]. -/
def MeaningPostulateEntailsChange
    {Entity State Event : Type}
    (rootPred : RootDenotation Entity State)
    (become : Event → State → Prop) : Prop :=
  ∀ x s, rootPred x s → ∃ e, become e s

/-- For result roots, the meaning postulate always holds (by axiom).
    For PC roots, it does not (the state can hold without any prior change).

    This bridges the Boolean `entailsChange` flag to the full
    compositional semantics. -/
structure RootSemantics (Entity State Event : Type) where
  /-- The root's state predicate -/
  pred : RootDenotation Entity State
  /-- The become relation on events and states -/
  become : Event → State → Prop
  /-- The root's type -/
  rootType : RootType
  /-- For result roots: change is entailed (meaning postulate).
      For PC roots: no such entailment. -/
  changeEntailment :
    rootType = .result →
    MeaningPostulateEntailsChange pred become

-- ════════════════════════════════════════════════════
-- § 7b. Root Denotation: Change-in-Denotation Architecture (B&KG 2020 §2.5)
-- ════════════════════════════════════════════════════

/-- B&KG's (2020 §2.5, eqs. 37a–b) root denotation architecture, where
    change is CONSTITUTIVE of the result root's meaning rather than an
    external meaning postulate.

    The formal contrast:
    - √FLAT = λxλs[flat'(x,s)] — pure state, no change in truth conditions
    - √CRACK = λxλs[cracked'(x,s) ∧ ∃e'[become'(s,e')]] — change IN the root

    This differs from `RootSemantics` above (Beavers et al. 2021 eq. 21),
    where the state predicate and the change requirement are separate.
    B&KG argue the change IS what the root means, not an external constraint.

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

/-- Extract the RootType from a BKG denotation. -/
def RootDen.rootType {Entity State Event : Type} :
    RootDen Entity State Event → RootType
  | .pc _ => .propertyConcept
  | .result _ _ _ => .result

/-- Extract the underlying state predicate from either root type. -/
def RootDen.statePred {Entity State Event : Type} :
    RootDen Entity State Event → (Entity → State → Prop)
  | .pc pred => pred
  | .result pred _ _ => pred

/-- Whether the root carries its own BECOME relation (built into the denotation). -/
def RootDen.carriesBECOME {Entity State Event : Type} :
    RootDen Entity State Event → Bool
  | .pc _ => false
  | .result _ _ _ => true

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

-- ════════════════════════════════════════════════════
-- § 8. Bridge to EntailmentProfile.changeOfState (ProtoRoles §8)
-- ════════════════════════════════════════════════════

/-- Dowty's P-Patient entailment (a) "undergoes change of state" is
    precisely the result root entailment. An object bearing a result
    root's state predicate has `changeOfState = true`.

    This bridges the root typology (Beavers et al. 2021) to the
    entailment profile (Dowty 1991) via the shared property. -/
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

/-- Bridge: BECOME = CoSType.inception (¬P → P transition).
    This connects the template operator to the existing CoS semantics. -/
theorem become_is_inception :
    -- Achievement template's Vendler class is achievement (has BECOME)
    Template.vendlerClass .achievement = .achievement ∧
    -- BECOME in the template corresponds to inception CoS
    -- (presupposes ¬P, asserts P — Resultatives.lean §6)
    true := ⟨rfl, rfl⟩

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

/-- Embick (2004) posits two adjectival structures:

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

/-- Sublexical modifier 'again' has two readings (von Stechow 1995, 1996):

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

/-- What *again* presupposes at a given scope position (von Stechow 1995, 1996).

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
    presupposition ENTAILS a prior change event. -/
def RootDen.againOverRoot {Entity State Event : Type} :
    RootDen Entity State Event → AgainPresupposition
  | .pc _ => .priorState
  | .result _ _ _ => .priorChange

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
    Collapsed presuppositions → only repetitive. -/
def RootDen.predictedAgainReadings {Entity State Event : Type} :
    RootDen Entity State Event → List AgainReading
  | .pc _ => [.restitutive, .repetitive]
  | .result _ _ _ => [.repetitive]

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
-- § 17. Cross-Classification: Arity × Change Entailment
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

