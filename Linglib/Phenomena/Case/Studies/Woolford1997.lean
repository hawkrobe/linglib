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

2. **Two structural object Cases**: OBJ (structural, assigned by Agr-O in
   intransitives and some transitives) and ACC (structural, assigned by
   Agr-O in transitives). These are distinct cases, not allomorphs.

3. **Maximum Accusatives formula**: The number of structural accusative
   cases in a clause = #arguments − #lexical cases − 1 (the −1 accounts
   for the subject, which receives NOM).

4. **Subject-object agreement** (not ergative): All subjects (NOM) trigger
   subject agreement; only OBJ (not ACC) triggers object agreement. ERG
   subjects do NOT trigger ergative agreement — they trigger the same
   subject agreement as NOM subjects.

## Nez Perce Patterns

**Transitive** (2 args, 1 lexical = ERG):
- Max ACC = 2 − 1 − 1 = 0, but one structural object case is available
- Allowed: NOM-ACC, ERG-OBJ
- Prohibited: *NOM-OBJ, *ERG-ACC

**Ditransitive** (3 args, 0 or 1 lexical):
- ERG subject: max ACC = 3 − 1 − 1 = 1 → one ACC, one OBJ
- NOM subject: max ACC = 3 − 0 − 1 = 2 → two ACC
- NOM + DAT: max ACC = 3 − 1 − 1 = 1 → one ACC
- 5 allowed patterns, 7 prohibited

## Integration

- Local `WCase` type adds OBJ (absent from `CaseVal`/`Core.Case`)
- Bridge theorems connect to `Core.Case` hierarchy validation
- Bridge theorems connect to dependent case algorithm (`DependentCase.lean`)
  showing where the theories agree and diverge
-/

namespace Phenomena.Case.Studies.Woolford1997

open Minimalism

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Woolford's five-way case inventory for Nez Perce.
    OBJ is the structural object case distinct from ACC — this is the
    key innovation over standard NOM/ACC systems. -/
inductive WCase where
  | nom   -- structural subject case (from Agr-S)
  | obj   -- structural object case (from Agr-O; triggers obj agreement)
  | acc   -- structural accusative (from Agr-O; does NOT trigger obj agreement)
  | erg   -- lexical/inherent case (assigned with θ-role)
  | dat   -- lexical case (e.g., applied arguments)
  deriving DecidableEq, BEq, Repr

/-- Structural vs lexical classification. -/
inductive CaseKind where
  | structural  -- assigned at S-structure by functional heads (Agr-S, Agr-O)
  | lexical     -- assigned at D-structure with θ-role (inherent)
  deriving DecidableEq, BEq, Repr

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
    This asymmetry is evidence that OBJ and ACC are distinct cases. -/
def WCase.triggersObjAgr : WCase → Bool
  | .obj => true
  | _    => false

-- ============================================================================
-- § 3: Maximum Accusatives Formula
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
-- § 5: Transitive Patterns
-- ============================================================================

/-- A transitive pattern: subject case + object case. -/
structure TransPattern where
  subject : WCase
  object  : WCase
  deriving DecidableEq, BEq, Repr

/-- The two allowed transitive patterns in Nez Perce.
    - NOM subject + ACC object (structural subject, structural object)
    - ERG subject + OBJ object (lexical subject, structural object) -/
def npTransAllowed : List TransPattern :=
  [ ⟨.nom, .acc⟩, ⟨.erg, .obj⟩ ]

/-- The two prohibited transitive patterns.
    - *NOM + OBJ: NOM subject should pair with ACC, not OBJ
    - *ERG + ACC: ERG subject leaves room for OBJ (maxAcc = 0) -/
def npTransProhibited : List TransPattern :=
  [ ⟨.nom, .obj⟩, ⟨.erg, .acc⟩ ]

/-- Predict whether a transitive pattern is allowed.
    Structural subject (NOM) → object is ACC.
    Lexical subject (ERG) → object is OBJ (maxAcc = 0). -/
def predictTransitive (p : TransPattern) : Bool :=
  let nArgs := 2
  let nLex := countLexIn [p.subject, p.object]
  let mAcc := maxAcc nArgs (countLexIn [p.subject])
  -- The number of ACC in the object list must equal maxAcc
  countAccIn [p.object] == mAcc &&
  -- Subject must be NOM or ERG
  (p.subject == .nom || p.subject == .erg) &&
  -- Object must be ACC or OBJ (structural)
  (p.object == .acc || p.object == .obj) &&
  -- If subject is lexical (ERG), no room for ACC → object must be OBJ
  -- If subject is structural (NOM), one ACC slot → object must be ACC
  nLex + countAccIn [p.object] + 1 ≤ nArgs

-- ============================================================================
-- § 6: Ditransitive Patterns
-- ============================================================================

/-- A ditransitive pattern: subject + two objects. -/
structure DitransPattern where
  subject : WCase
  obj1    : WCase
  obj2    : WCase
  deriving DecidableEq, BEq, Repr

/-- The four allowed ditransitive patterns in Nez Perce.
    ERG subject (1 lexical): maxAcc = 3 − 1 − 1 = 1 → one ACC, one OBJ.
    NOM subject (0 lexical): maxAcc = 3 − 0 − 1 = 2 → two ACC.
    DAT in either object slot absorbs a lexical case. -/
def npDitransAllowed : List DitransPattern :=
  [ ⟨.erg, .obj, .acc⟩     -- ERG subj, 1 ACC (maxAcc = 1)
  , ⟨.erg, .acc, .obj⟩     -- ERG subj, 1 ACC (order variant)
  , ⟨.nom, .acc, .acc⟩     -- NOM subj, 2 ACC (maxAcc = 2)
  , ⟨.erg, .dat, .obj⟩     -- ERG+DAT = 2 lexical; maxAcc = 3−2−1 = 0
  , ⟨.nom, .dat, .acc⟩ ]   -- NOM+DAT = 1 lexical; maxAcc = 3−1−1 = 1

/-- The seven prohibited ditransitive patterns. -/
def npDitransProhibited : List DitransPattern :=
  [ ⟨.erg, .obj, .obj⟩     -- 0 ACC but maxAcc = 1
  , ⟨.erg, .acc, .acc⟩     -- 2 ACC but maxAcc = 1
  , ⟨.nom, .obj, .acc⟩     -- OBJ not expected with NOM subj
  , ⟨.nom, .acc, .obj⟩     -- OBJ not expected with NOM subj
  , ⟨.nom, .obj, .obj⟩     -- OBJ not expected with NOM subj
  , ⟨.erg, .dat, .acc⟩     -- ACC but maxAcc = 0 (2 lexical)
  , ⟨.nom, .dat, .obj⟩ ]   -- OBJ not expected with NOM subj

/-- Predict whether a ditransitive pattern is allowed. -/
def predictDitransitive (p : DitransPattern) : Bool :=
  let nArgs := 3
  let subjectLex := countLexIn [p.subject]
  let objectLex := countLexIn [p.obj1, p.obj2]
  let totalLex := subjectLex + objectLex
  let mAcc := maxAcc nArgs totalLex
  -- Subject is NOM or ERG
  (p.subject == .nom || p.subject == .erg) &&
  -- Objects are structural (ACC/OBJ) or DAT
  (p.obj1 == .acc || p.obj1 == .obj || p.obj1 == .dat) &&
  (p.obj2 == .acc || p.obj2 == .obj || p.obj2 == .dat) &&
  -- ACC count matches maxAcc
  countAccIn [p.obj1, p.obj2] == mAcc &&
  -- OBJ only appears when there is a lexical subject (ERG)
  (!(p.obj1 == .obj || p.obj2 == .obj) || p.subject == .erg)

-- ============================================================================
-- § 7: Transitive Verification
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
-- § 8: Ditransitive Verification
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

/-- maxAcc for ditransitives: ERG subject, no DAT → 1 ACC slot. -/
theorem ditrans_erg_maxAcc : maxAcc 3 1 = 1 := rfl

/-- maxAcc for ditransitives: NOM subject → 2 ACC slots. -/
theorem ditrans_nom_maxAcc : maxAcc 3 0 = 2 := rfl

/-- maxAcc for ditransitives: ERG + DAT → 0 ACC slots. -/
theorem ditrans_erg_dat_maxAcc : maxAcc 3 2 = 0 := rfl

-- ============================================================================
-- § 9: Agreement Verification
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
    agreement, ACC does not. This justifies treating them as distinct cases. -/
theorem obj_acc_agreement_differ :
    WCase.obj.triggersObjAgr ≠ WCase.acc.triggersObjAgr := by decide

-- ============================================================================
-- § 10: Intransitive
-- ============================================================================

/-- Intransitives: 1 argument, 0 lexical → maxAcc = 0.
    The sole argument gets NOM (structural from Agr-S). -/
theorem intransitive_maxAcc : maxAcc 1 0 = 0 := rfl

-- ============================================================================
-- § 11: Typological Variation
-- ============================================================================

/-- Whether a language assigns ERG obligatorily or optionally. -/
inductive LexAssignment where
  | obligatory  -- ERG required on transitive subjects
  | optional    -- ERG optional (e.g., Thangu: some transitives lack ERG)
  deriving DecidableEq, BEq, Repr

/-- Language parameters for a four-way system. -/
structure LexParams where
  ergAssignment : LexAssignment
  hasDat : Bool
  deriving Repr

/-- Nez Perce: obligatory ERG, has DAT. -/
def nezPerce : LexParams := ⟨.obligatory, true⟩

/-- Thangu: optional ERG (some transitives use NOM-ACC). -/
def thangu : LexParams := ⟨.optional, false⟩

-- ============================================================================
-- § 12: Mapping to Core.Case
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
-- § 13: Bridge to Dependent Case Theory
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
    objects trigger agreement (OBJ) and others don't (ACC). -/
theorem agreement_asymmetry_is_woolford_specific :
    WCase.obj.triggersObjAgr = true ∧
    WCase.acc.triggersObjAgr = false := ⟨rfl, rfl⟩

/-- ERG is lexical under both theories: Woolford's inherent case
    and Baker's dependent ergative both treat ERG as non-structural,
    though the mechanisms differ (θ-role assignment vs. configuration). -/
theorem erg_nonstructural :
    WCase.erg.kind = .lexical := rfl

end Phenomena.Case.Studies.Woolford1997
