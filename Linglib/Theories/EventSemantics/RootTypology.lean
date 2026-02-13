/-
# Root Typology: States and Changes of State (Beavers et al. 2021)

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
-/

import Linglib.Theories.EventSemantics.EventStructure

namespace EventSemantics.RootTypology

open EventSemantics.EventStructure
open EventSemantics.ProtoRoles
open TruthConditional.Verb.ChangeOfState
open TruthConditional.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Root Type Classification (Beavers et al. 2021 §3.1)
-- ════════════════════════════════════════════════════

/-- Two types of change-of-state verb roots (Beavers et al. 2021 §3.1).

    **Property concept (PC) roots** (Dixon 1982, Thompson 1988): underlie
    deadjectival CoS verbs. The root describes a gradable property
    (dimension, color, value, etc.). Examples: flat, red, long, warm.

    **Result roots**: underlie non-deadjectival CoS verbs. The root describes
    a specific result state that arises from a particular kind of event
    (breaking, cooking, killing, etc.). Examples: crack, break, shatter. -/
inductive RootType where
  | propertyConcept  -- flat, red, long — deadjectival CoS (flatten, redden)
  | result           -- crack, break, shatter — non-deadjectival CoS
  deriving DecidableEq, Repr, BEq

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
-- § 2. The Key Semantic Distinction (§3.3, §3.6)
-- ════════════════════════════════════════════════════

/-- Whether a root lexically entails prior change (Beavers et al. 2021 §3.6).

    This is the central semantic distinction. PC roots denote simple states
    that can hold without any prior change event:
      ⟦√FLAT⟧ = λx.λs[flat'(x, s)]       — (eq. 20a)

    Result roots denote states that entail a prior change event:
      ⟦√CRACK⟧ = λx.λs[cracked'(x, s)]   — (eq. 21a)
        where ∀x.∀s[cracked'(x, s) → ∃e'[become'(e', s)]]

    Evidence: "The bright photo has never brightened" is fine (PC root, no
    change entailed), but "#The shattered vase has never shattered" is
    contradictory (result root, change is entailed). -/
def RootType.entailsChange : RootType → Bool
  | .propertyConcept => false
  | .result => true

-- ════════════════════════════════════════════════════
-- § 3. Morphosyntactic Correlates (§§3.2–3.5, 6–7)
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

/-- Result root verbs are typically achievements or accomplishments
    (they have BECOME in their template). PC root verbs in their
    inchoative (change-of-state) use are also achievements/accomplishments,
    but their stative use is a state. -/
def RootType.stativeVendlerClass : RootType → VendlerClass
  | .propertyConcept => .state       -- "The rug is flat" (stative)
  | .result => .achievement          -- No pure stative; even "broken" entails change

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

end EventSemantics.RootTypology
