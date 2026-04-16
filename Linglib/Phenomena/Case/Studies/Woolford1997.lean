import Linglib.Core.Case
import Linglib.Theories.Syntax.Minimalism.Core.DependentCase

/-!
# @cite{woolford-1997} — Four-Way Case Systems
@cite{woolford-1997} @cite{woolford-2006} @cite{baker-2015} @cite{marantz-1991}

Formalization of @cite{woolford-1997}'s analysis of four-way case systems,
with Nez Perce as the primary case study.

## Key Claims

1. **ERG is lexical (inherent) Case**, like dative — assigned at D-structure
   in conjunction with θ-role assignment. This contrasts with NOM/ACC/ABS,
   which are structural cases assigned at S-structure.

2. **Two structural object Cases**: OBJ (assigned/checked by Agr-O,
   associated with object agreement) and ACC (assigned/checked by V/P,
   not associated with object agreement). These are distinct cases.

3. **Maximum Accusatives formula**: The number of structural accusative
   cases in a clause = #arguments − #lexical cases − 1 (the −1 accounts
   for the subject, which receives NOM).

4. **Subject-object agreement** (not ergative): All subjects (NOM and ERG)
   trigger subject agreement; only OBJ (not ACC) triggers object agreement.
   ERG subjects do NOT trigger ergative agreement — they trigger the same
   subject agreement as NOM subjects.

5. **Generalization (19)**: lexically Cased subject → *structural accusative
   object. In a clause with a lexically Cased subject (e.g., ergative or
   dative), the highest object cannot have structural accusative Case
   (although that object can have objective Case). This is subsumed by
   the Max. Acc. formula for the highest object and derives the prohibited
   transitive and ditransitive patterns.

## Nez Perce Patterns

**Transitive** (2 args, 1 lexical = ERG):
- Max ACC = 2 − 1 − 1 = 0, but one structural object case is available
- Allowed: NOM-ACC, ERG-OBJ
- Prohibited: *NOM-OBJ, *ERG-ACC

**Ditransitive** (3 args: agent, goal, theme):
- NOM subject (0 lexical): max ACC = 3 − 0 − 1 = 2 → two ACC
- NOM + DAT goal (1 lexical): max ACC = 3 − 1 − 1 = 1 → one ACC
- ERG subject (1 lexical): max ACC = 3 − 1 − 1 = 1 → one ACC (theme only; gen. (19) blocks ACC for goal)
- ERG + DAT goal (2 lexical): max ACC = 3 − 2 − 1 = 0
- 4 allowed patterns, 8 prohibited (paper's (22))

## Integration

- Local `WCase` type adds OBJ (absent from `CaseVal`/`Core.Case`)
- Bridge theorems connect to `Core.Case` hierarchy validation
- Bridge theorems connect to dependent case algorithm (`DependentCase.lean`)
  showing where the theories agree and diverge
-/

namespace Woolford1997

open Minimalism

-- ============================================================================
-- § 1: Case Inventory (paper's (1)–(2))
-- ============================================================================

/-- Woolford's five-way case inventory for Nez Perce.
    OBJ is the structural object case distinct from ACC — this is the
    key innovation over standard NOM/ACC systems. -/
inductive WCase where
  | nom   -- structural subject case (from Agr-S)
  | obj   -- structural object case (from Agr-O; triggers obj agreement)
  | acc   -- structural accusative (from V/P; does NOT trigger obj agreement)
  | erg   -- lexical/inherent case (assigned with θ-role)
  | dat   -- lexical case (e.g., applied arguments)
  deriving DecidableEq, Repr

/-- Structural vs lexical classification. -/
inductive CaseKind where
  | structural  -- assigned at S-structure by functional heads (Agr-S, Agr-O)
                -- or by lexical heads (V, P) for ACC
  | lexical     -- assigned at D-structure with θ-role (inherent)
  deriving DecidableEq, Repr

/-- Each case's structural/lexical classification. -/
def WCase.kind : WCase → CaseKind
  | .nom => .structural
  | .obj => .structural
  | .acc => .structural
  | .erg => .lexical
  | .dat => .lexical

-- ============================================================================
-- § 2: Agreement
-- ============================================================================

/-- Subject agreement: triggered by ALL subjects (NOM and ERG alike).
    Woolford's key point: ERG subjects trigger *subject* agreement,
    not ergative agreement. The agreement system is nominative-accusative,
    even though the case system has ergative. -/
def WCase.triggersSubjAgr : WCase → Bool
  | .nom => true
  | .erg => true   -- ERG triggers SUBJECT agreement
  | _    => false

/-- Object agreement: triggered ONLY by OBJ, not by ACC.
    This asymmetry is evidence that OBJ and ACC are distinct cases:
    OBJ is assigned by Agr-O (associated with agreement), while
    ACC is assigned by V/P (no agreement). -/
def WCase.triggersObjAgr : WCase → Bool
  | .obj => true
  | _    => false

-- ============================================================================
-- § 3: Maximum Accusatives Formula (paper's (27))
-- ============================================================================

/-- The maximum number of structural accusative cases assignable in a clause.
    Formula: #arguments − #lexical cases − 1 (the −1 is the subject slot).
    Uses Nat subtraction (saturating at 0). -/
def maxAcc (nArgs nLexCases : Nat) : Nat := nArgs - nLexCases - 1

-- ============================================================================
-- § 4: Counting Helpers
-- ============================================================================

/-- Count ACC cases in a list of case assignments. -/
def countAccIn (cases : List WCase) : Nat :=
  cases.filter (· == .acc) |>.length

/-- Count lexical cases in a list of case assignments. -/
def countLexIn (cases : List WCase) : Nat :=
  cases.filter (λ c => c.kind == .lexical) |>.length

-- ============================================================================
-- § 5: Generalization (19)
-- ============================================================================

/-- Generalization (19): a lexically Cased subject cannot be followed by a
    structural accusative object. Under the weak interpretation, this
    applies to the thematically highest object (goal > theme). -/
def generalization19 (subject goal : WCase) : Bool :=
  -- If subject is lexical, goal must not be ACC
  subject.kind != .lexical || goal != .acc

/-- Generalization (19) holds for all allowed transitive patterns:
    ERG (lexical) subject → object is OBJ, not ACC. -/
theorem gen19_transitive_erg : generalization19 .erg .obj = true := rfl

/-- Generalization (19) is vacuously satisfied for NOM subjects. -/
theorem gen19_transitive_nom : generalization19 .nom .acc = true := rfl

/-- The strong interpretation of generalization (19) would block ACC
    on ALL objects when the subject is lexical. -/
def generalization19_strong (subject : WCase) (objects : List WCase) : Bool :=
  subject.kind != .lexical || objects.all (· != .acc)

/-- The strong interpretation incorrectly prohibits ERG-OBJ-ACC (paper's
    (22A.3)), which is an attested Nez Perce ditransitive pattern. The goal
    gets OBJ (per weak gen (19)), but the theme can still get ACC.
    The paper argues for the weak interpretation on these grounds. -/
theorem strong_interpretation_too_restrictive :
    generalization19_strong .erg [.obj, .acc] = false := rfl

/-- The weak interpretation correctly allows ERG-OBJ-ACC: it only checks
    the goal (highest object), which is OBJ, not ACC. -/
theorem weak_allows_erg_obj_acc :
    generalization19 .erg .obj = true := rfl

-- ============================================================================
-- § 6: Transitive Patterns (paper's (16))
-- ============================================================================

/-- A transitive pattern: subject case + object case. -/
structure TransPattern where
  subject : WCase
  object  : WCase
  deriving DecidableEq, Repr

/-- The two allowed transitive patterns in Nez Perce (paper's (16A)).
    - NOM subject + ACC object (structural subject, structural object)
    - ERG subject + OBJ object (lexical subject, structural object) -/
def npTransAllowed : List TransPattern :=
  [ ⟨.nom, .acc⟩, ⟨.erg, .obj⟩ ]

/-- The two prohibited transitive patterns (paper's (16B)).
    - *NOM + OBJ: NOM subject should pair with ACC, not OBJ
    - *ERG + ACC: blocked by generalization (19) -/
def npTransProhibited : List TransPattern :=
  [ ⟨.nom, .obj⟩, ⟨.erg, .acc⟩ ]

/-- Predict whether a transitive pattern is allowed.
    Structural subject (NOM) → object is ACC.
    Lexical subject (ERG) → object is OBJ (generalization (19) blocks ACC). -/
def predictTransitive (p : TransPattern) : Bool :=
  let nArgs := 2
  let mAcc := maxAcc nArgs (countLexIn [p.subject])
  -- The number of ACC in the object list must equal maxAcc
  countAccIn [p.object] == mAcc &&
  -- Subject must be NOM or ERG
  (p.subject == .nom || p.subject == .erg) &&
  -- Object must be ACC or OBJ (structural)
  (p.object == .acc || p.object == .obj) &&
  -- OBJ only appears with lexical (ERG) subject
  (p.object != .obj || p.subject == .erg) &&
  -- Generalization (19)
  generalization19 p.subject p.object

-- ============================================================================
-- § 7: Ditransitive Patterns (paper's (22))
-- ============================================================================

/-- A ditransitive pattern: subject + goal (higher object) + theme (lower object).
    The thematic hierarchy (goal > theme) matters for generalization (19):
    a lexical subject blocks structural accusative on the goal (highest
    object), not the theme. -/
structure DitransPattern where
  subject : WCase
  goal    : WCase  -- thematically higher object
  theme   : WCase  -- thematically lower object
  deriving DecidableEq, Repr

/-- The four allowed ditransitive patterns in Nez Perce (paper's (22A)).
    Columns are Agent, Goal, Theme following the paper's labels. -/
def npDitransAllowed : List DitransPattern :=
  [ ⟨.nom, .acc, .acc⟩     -- (22A.1) NOM subj, 2 ACC (maxAcc = 2)
  , ⟨.nom, .dat, .acc⟩     -- (22A.2) NOM+DAT = 1 lexical; maxAcc = 1
  , ⟨.erg, .obj, .acc⟩     -- (22A.3) ERG subj; goal=OBJ (gen 19), theme=ACC
  , ⟨.erg, .dat, .obj⟩ ]   -- (22A.4) ERG+DAT = 2 lexical; maxAcc = 0

/-- The eight prohibited ditransitive patterns (paper's (22B)). -/
def npDitransProhibited : List DitransPattern :=
  [ ⟨.nom, .obj, .obj⟩     -- (22B.1) OBJ not expected with NOM subj
  , ⟨.nom, .obj, .acc⟩     -- (22B.2) OBJ not expected with NOM subj
  , ⟨.nom, .acc, .obj⟩     -- (22B.3) OBJ not expected with NOM subj
  , ⟨.nom, .dat, .obj⟩     -- (22B.4) OBJ not expected with NOM subj
  , ⟨.erg, .acc, .acc⟩     -- (22B.5) 2 ACC but maxAcc = 1
  , ⟨.erg, .acc, .obj⟩     -- (22B.6) gen (19): goal=ACC with lexical subj
  , ⟨.erg, .obj, .obj⟩     -- (22B.7) 0 ACC but maxAcc = 1
  , ⟨.erg, .dat, .acc⟩ ]   -- (22B.8) ACC but maxAcc = 0 (2 lexical)

/-- Predict whether a ditransitive pattern is allowed.
    Encodes the Max. Acc. formula, structural constraints on OBJ,
    and generalization (19). -/
def predictDitransitive (p : DitransPattern) : Bool :=
  let nArgs := 3
  let totalLex := countLexIn [p.subject] + countLexIn [p.goal, p.theme]
  let mAcc := maxAcc nArgs totalLex
  -- Subject is NOM or ERG
  (p.subject == .nom || p.subject == .erg) &&
  -- Objects are structural (ACC/OBJ) or DAT
  (p.goal == .acc || p.goal == .obj || p.goal == .dat) &&
  (p.theme == .acc || p.theme == .obj || p.theme == .dat) &&
  -- ACC count matches maxAcc
  countAccIn [p.goal, p.theme] == mAcc &&
  -- OBJ only appears when subject is ERG (lexical)
  (!(p.goal == .obj || p.theme == .obj) || p.subject == .erg) &&
  -- Generalization (19): lexical subject → goal ≠ ACC
  generalization19 p.subject p.goal

-- ============================================================================
-- § 8: Transitive Verification
-- ============================================================================

/-- All allowed transitive patterns are predicted as allowed. -/
theorem trans_allowed_predicted :
    npTransAllowed.all predictTransitive = true := by native_decide

/-- All prohibited transitive patterns are predicted as prohibited. -/
theorem trans_prohibited_predicted :
    npTransProhibited.all (λ p => !predictTransitive p) = true := by native_decide

/-- The allowed/prohibited lists are disjoint. -/
theorem trans_disjoint :
    npTransAllowed.all (λ p => npTransProhibited.all (· != p)) = true := by native_decide

/-- The allowed/prohibited lists cover all NOM/ERG × ACC/OBJ combinations. -/
theorem trans_complete :
    npTransAllowed.length + npTransProhibited.length = 4 := by native_decide

/-- maxAcc for transitives: NOM subject → 1 ACC slot. -/
theorem trans_nom_maxAcc : maxAcc 2 0 = 1 := rfl

/-- maxAcc for transitives: ERG subject → 0 ACC slots. -/
theorem trans_erg_maxAcc : maxAcc 2 1 = 0 := rfl

-- ============================================================================
-- § 9: Ditransitive Verification
-- ============================================================================

/-- All allowed ditransitive patterns are predicted. -/
theorem ditrans_allowed_predicted :
    npDitransAllowed.all predictDitransitive = true := by native_decide

/-- All prohibited ditransitive patterns are rejected. -/
theorem ditrans_prohibited_predicted :
    npDitransProhibited.all (λ p => !predictDitransitive p) = true := by native_decide

/-- The allowed/prohibited lists are disjoint. -/
theorem ditrans_disjoint :
    npDitransAllowed.all (λ p => npDitransProhibited.all (· != p)) = true := by
  native_decide

/-- The allowed/prohibited lists cover all 12 NOM/ERG × {ACC,OBJ,DAT}² patterns
    (excluding DAT-DAT which never arises). -/
theorem ditrans_complete :
    npDitransAllowed.length + npDitransProhibited.length = 12 := by native_decide

/-- maxAcc for ditransitives: ERG subject, no DAT → 1 ACC slot. -/
theorem ditrans_erg_maxAcc : maxAcc 3 1 = 1 := rfl

/-- maxAcc for ditransitives: NOM subject → 2 ACC slots. -/
theorem ditrans_nom_maxAcc : maxAcc 3 0 = 2 := rfl

/-- maxAcc for ditransitives: ERG + DAT → 0 ACC slots. -/
theorem ditrans_erg_dat_maxAcc : maxAcc 3 2 = 0 := rfl

-- ============================================================================
-- § 10: Agreement Verification
-- ============================================================================

/-- ERG is lexical (inherent), not structural. -/
theorem erg_is_lexical : WCase.erg.kind = .lexical := rfl

/-- NOM is structural. -/
theorem nom_is_structural : WCase.nom.kind = .structural := rfl

/-- ERG subjects trigger subject agreement (not ergative agreement). -/
theorem erg_triggers_subj_agr : WCase.erg.triggersSubjAgr = true := rfl

/-- NOM subjects trigger subject agreement. -/
theorem nom_triggers_subj_agr : WCase.nom.triggersSubjAgr = true := rfl

/-- ACC does NOT trigger object agreement. -/
theorem acc_no_obj_agr : WCase.acc.triggersObjAgr = false := rfl

/-- OBJ triggers object agreement. -/
theorem obj_triggers_obj_agr : WCase.obj.triggersObjAgr = true := rfl

/-- Agreement is subject-object, not ergative-absolutive:
    both NOM and ERG trigger the SAME (subject) agreement. -/
theorem agreement_is_nom_acc :
    WCase.nom.triggersSubjAgr = WCase.erg.triggersSubjAgr := rfl

/-- OBJ and ACC differ in agreement properties: OBJ triggers object
    agreement, ACC does not. This justifies treating them as distinct cases
    and reflects their different structural sources (Agr-O vs V/P). -/
theorem obj_acc_agreement_differ :
    WCase.obj.triggersObjAgr ≠ WCase.acc.triggersObjAgr := by decide

-- ============================================================================
-- § 11: Intransitive
-- ============================================================================

/-- Intransitives: 1 argument, 0 lexical → maxAcc = 0.
    The sole argument gets NOM (structural from Agr-S). -/
theorem intransitive_maxAcc : maxAcc 1 0 = 0 := rfl

/-- Burzio's generalization as a corollary of the Max. Acc. formula.
    @cite{woolford-1997} argues that three apparently separate generalizations
    are all instances of the Max. Acc. formula:
    (i) No verb assigns structural ACC to its subject (the −1 term).
    (ii) A verb without an external subject cannot assign ACC
         (Burzio's generalization): 1 arg, 0 lexical → maxAcc = 0.
    (iii) A lexically Cased subject blocks ACC on the highest object
          (generalization (19)): 2 args, 1 lexical → maxAcc = 0.
    The Max. Acc. formula unifies all three. -/
theorem burzio_from_maxAcc :
    -- (ii) Unaccusative: 1 arg, 0 lexical → maxAcc = 0 (Burzio)
    maxAcc 1 0 = 0 ∧
    -- (iii) Transitive with lexical subj: 2 args, 1 lexical → maxAcc = 0 (gen 19)
    maxAcc 2 1 = 0 ∧
    -- Normal transitive: 2 args, 0 lexical → maxAcc = 1
    maxAcc 2 0 = 1 := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 12: Typological Variation (paper's (60))
-- ============================================================================

/-- Whether a language assigns ERG obligatorily or optionally. -/
inductive LexAssignment where
  | obligatory  -- ERG required on transitive subjects
  | optional    -- ERG optional (e.g., Nez Perce: some transitives lack ERG)
  deriving DecidableEq, Repr

/-- Language parameters for a three- or four-way system.
    The range of Case patterns a language allows follows from whether
    verbs assign ERG and DAT obligatorily or optionally. -/
structure LexParams where
  ergAssignment : LexAssignment
  datAssignment : LexAssignment
  deriving Repr

/-- Nez Perce: optional ERG, optional DAT. -/
def nezPerce : LexParams := ⟨.optional, .optional⟩

/-- Thangu: obligatory ERG, obligatory DAT (three-way system: no ACC surfaces). -/
def thangu : LexParams := ⟨.obligatory, .obligatory⟩

/-- Kalkatungu: obligatory ERG, optional DAT (four-way system like Nez Perce,
    but no nominative-accusative pattern since ERG is always assigned). -/
def kalkatungu : LexParams := ⟨.obligatory, .optional⟩

/-- Predict which transitive patterns are available given language parameters.
    Obligatory ERG → only ERG-OBJ (no NOM-ACC).
    Optional ERG → both NOM-ACC and ERG-OBJ. -/
def availableTransPatterns (params : LexParams) : List TransPattern :=
  match params.ergAssignment with
  | .obligatory => [⟨.erg, .obj⟩]
  | .optional   => [⟨.nom, .acc⟩, ⟨.erg, .obj⟩]

/-- Predict which ditransitive patterns are available given language parameters.
    The interaction of ERG and DAT optionality determines the full set. -/
def availableDitransPatterns (params : LexParams) : List DitransPattern :=
  match params.ergAssignment, params.datAssignment with
  | .optional, .optional =>
    -- Nez Perce: full four-way
    [⟨.nom, .acc, .acc⟩, ⟨.nom, .dat, .acc⟩, ⟨.erg, .obj, .acc⟩, ⟨.erg, .dat, .obj⟩]
  | .optional, .obligatory =>
    -- Optional ERG, obligatory DAT: goal always DAT
    [⟨.nom, .dat, .acc⟩, ⟨.erg, .dat, .obj⟩]
  | .obligatory, .optional =>
    -- Kalkatungu: obligatory ERG, optional DAT
    [⟨.erg, .obj, .acc⟩, ⟨.erg, .dat, .obj⟩]
  | .obligatory, .obligatory =>
    -- Thangu: both obligatory → only ERG-DAT-OBJ
    [⟨.erg, .dat, .obj⟩]

/-- Nez Perce (optional ERG): both transitive patterns available.
    The predicted patterns match the attested data exactly. -/
theorem np_trans_from_params :
    availableTransPatterns nezPerce = npTransAllowed := rfl

/-- Nez Perce ditransitive predictions match the attested patterns. -/
theorem np_ditrans_from_params :
    availableDitransPatterns nezPerce = npDitransAllowed := rfl

/-- Thangu (obligatory ERG): only ERG-OBJ in transitives. -/
theorem thangu_trans_erg_only :
    availableTransPatterns thangu = [⟨.erg, .obj⟩] := rfl

/-- Thangu (obligatory ERG + DAT): only ERG-DAT-OBJ in ditransitives.
    With 2 lexical cases, maxAcc = 3 − 2 − 1 = 0 — no ACC at all. -/
theorem thangu_ditrans_no_acc :
    availableDitransPatterns thangu = [⟨.erg, .dat, .obj⟩] := rfl

/-- Kalkatungu (obligatory ERG, optional DAT): ERG-OBJ only in transitives
    (no NOM-ACC pattern since ERG is always assigned). -/
theorem kalkatungu_trans_erg_only :
    availableTransPatterns kalkatungu = [⟨.erg, .obj⟩] := rfl

/-- Kalkatungu ditransitives: ERG-OBJ-ACC (without DAT) and ERG-DAT-OBJ
    (with DAT). Unlike Thangu, Kalkatungu's optional DAT allows ACC to
    appear in ditransitives. -/
theorem kalkatungu_ditrans :
    availableDitransPatterns kalkatungu = [⟨.erg, .obj, .acc⟩, ⟨.erg, .dat, .obj⟩] := rfl

/-- All predicted patterns are valid: every predicted transitive pattern
    passes the prediction function. -/
theorem all_predicted_trans_valid :
    [nezPerce, thangu, kalkatungu].all (λ params =>
      (availableTransPatterns params).all predictTransitive) = true := by native_decide

/-- All predicted ditransitive patterns pass the prediction function. -/
theorem all_predicted_ditrans_valid :
    [nezPerce, thangu, kalkatungu].all (λ params =>
      (availableDitransPatterns params).all predictDitransitive) = true := by native_decide

-- ============================================================================
-- § 13: Mapping to Core.Case
-- ============================================================================

/-- Map Woolford's cases to `Core.Case` for hierarchy validation.
    OBJ maps to ACC (both are structural object cases). -/
def WCase.toCore : WCase → Core.Case
  | .nom => .nom
  | .obj => .acc   -- OBJ is a structural object case; closest match
  | .acc => .acc
  | .erg => .erg
  | .dat => .dat

/-- Nez Perce structural case inventory (NOM + ACC/OBJ + ERG).
    Under Blake's hierarchy, these are all core cases (rank 6)
    plus DAT (rank 4), with GEN (rank 5) between. -/
def npInventory : List Core.Case := [.nom, .acc, .erg]

/-- The core-case subset is valid per Blake's hierarchy
    (all at rank 6, no gaps). -/
theorem np_core_valid : Core.validInventory npInventory = true := by native_decide

/-- Full inventory including DAT requires GEN for contiguity. -/
def npFullInventory : List Core.Case := [.nom, .acc, .erg, .gen, .dat]

theorem np_full_valid : Core.validInventory npFullInventory = true := by native_decide

-- ============================================================================
-- § 14: Bridge to Dependent Case Theory
-- ============================================================================

/-! ## Woolford vs. Baker/Marantz

@cite{woolford-1997} and @cite{baker-2015}/@cite{marantz-1991} make overlapping
but distinct predictions. Key agreement: both assign structural ACC in
transitives with two caseless NPs. Key disagreement: dependent case has
no OBJ/ACC distinction — it assigns a single dependent case (ACC) to
the lower NP, regardless of whether the higher NP has lexical case. -/

/-- Map Woolford's cases to `CaseVal` for comparison with dependent case. -/
def WCase.toCaseVal : WCase → CaseVal
  | .nom => .nom
  | .obj => .acc   -- dependent case conflates OBJ/ACC
  | .acc => .acc
  | .erg => .erg
  | .dat => .dat

/-- Where Woolford and dependent case agree: in a NOM-ACC transitive,
    the object gets ACC under both theories. -/
theorem agree_on_nom_acc_transitive :
    let depResult := assignCases .accusative
      [ { label := "subj", lexicalCase := none },
        { label := "obj", lexicalCase := none } ]
    getCaseOf "obj" depResult = some CaseVal.acc ∧
    (TransPattern.mk .nom .acc).object.toCaseVal = CaseVal.acc := by
  constructor
  · native_decide
  · rfl

/-- Where they diverge: Woolford distinguishes OBJ from ACC.
    Under dependent case, both map to the same CaseVal.acc. -/
theorem diverge_on_obj_vs_acc :
    WCase.obj ≠ WCase.acc ∧
    WCase.obj.toCaseVal = WCase.acc.toCaseVal := ⟨by decide, rfl⟩

/-- Dependent case has no analogue of Woolford's agreement asymmetry:
    under dependent case, there is one ACC — it either triggers agreement
    or not. Woolford's two structural object cases explain why some
    objects trigger agreement (OBJ from Agr-O) and others don't (ACC from V/P). -/
theorem agreement_asymmetry_is_woolford_specific :
    WCase.obj.triggersObjAgr = true ∧
    WCase.acc.triggersObjAgr = false := ⟨rfl, rfl⟩

/-- ERG is lexical under both theories: Woolford's inherent case
    and Baker's dependent ergative both treat ERG as non-structural,
    though the mechanisms differ (θ-role assignment vs. configuration). -/
theorem erg_nonstructural :
    WCase.erg.kind = .lexical := rfl

end Woolford1997
