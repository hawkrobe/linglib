import Linglib.Core.Logic.OT
import Linglib.Core.Logic.ConstraintEvaluation
import Linglib.Core.Prominence
import Linglib.Phenomena.Case.Typology
import Linglib.Phenomena.Case.Studies.Aissen2003

/-!
# De Hoop & Malchukov (2008): Case-Marking Strategies @cite{de-hoop-malchukov-2008}

Case-Marking Strategies. Linguistic Inquiry 39(4): 565–587.

Derives the basic case-marking typology from two functional constraints and
an economy constraint, evaluated in Blutner's (2000) Bidirectional OT:

- **Identify** (I): Case identifies the role — overt marking should match
  argument strength (markedness principle). Penalizes form/strength mismatch.
- **Distinguish** (D): Case distinguishes A from P — unmarked atypical
  arguments are confusable with the other role. Penalizes zero-marked
  atypical arguments.
- **Economy** (*!) / **PaIP**: Avoid overt case marking (general) or
  specifically protect the primary actant from marking (alignment-sensitive).

## Bidirectional OT (Blutner 2000)

Standard OT selects the best form for a given meaning (speaker). BiOT adds
the hearer's perspective via **superoptimality**: a form–meaning pair ⟨f, m⟩
is superoptimal iff no other superoptimal pair with the same form or same
meaning is strictly more harmonic. This is a fixed-point computation
(`Core.ConstraintEvaluation.superoptimal`).

## Key Results

### 1. DSM divergence (subjects, §2)

Identify and Distinguish make *opposite* predictions for subjects:

| Ranking | Superoptimal pairs | Marking pattern |
|---------|--------------------|-----------------|
| I >> *! | (ERG, strong), (Ø, weak) | Mark strong subjects (Manipuri) |
| D >> *! | (Ø, strong), (ERG, weak) | Mark weak subjects (Fore) |
| *! >> I/D | → Ø | Neutral (no DSM) |

### 2. DOM convergence (objects, §2)

Identify and Distinguish make the *same* prediction for objects:

| Ranking | Superoptimal pairs | Marking pattern |
|---------|--------------------|-----------------|
| I >> *! | (ACC, strong), (Ø, weak) | Mark strong objects |
| D >> *! | (ACC, strong), (Ø, weak) | Mark strong objects |

### 3. Symmetrical ⇒ Identify (§3)

When a language has two overt case forms (e.g., Finnish ACC/PART), Distinguish
is vacuously satisfied by all overt pairs — it cannot drive the choice between
them. Symmetrical marking is necessarily Identify-driven (p. 574–578).

### 4. PaIP and alignment correlation (§4)

The Primary Actant Immunity Principle (PaIP) restricts which argument can
be differentially marked. When PaIP dominates:
- In nom-acc: subject = primary actant → PaIP >> I/D blocks DSM → only DOM
- In ergative: object = primary actant → PaIP >> I/D blocks DOM → only DSM

This derives: DOM ↔ nom-acc, DSM ↔ ergative (p. 580).

## References

- de Hoop, H. & A. Malchukov (2008). Case-Marking Strategies.
  Linguistic Inquiry 39(4): 565–587.
- Blutner, R. (2000). Some Aspects of Optimality in Natural Language
  Interpretation. JOLLI 9(1): 1–25.
- Aissen, J. (2003). Differential Object Marking: Iconicity vs. Economy.
  NLLT 21(3): 435–483.
-/

namespace Phenomena.Case.Studies.DeHoopMalchukov2008

open Core.ConstraintEvaluation
open Core.OT
open Core.Prominence
open Phenomena.Case.Typology
open Phenomena.Case.Studies.Aissen2003

-- ============================================================================
-- § 1: Forms and Meanings
-- ============================================================================

/-- Case forms for a single argument: zero or overt marking.
    Used for asymmetrical differential marking (overt alternates with Ø). -/
inductive CaseForm where
  | zero  : CaseForm   -- Ø (unmarked)
  | overt : CaseForm   -- overtly case-marked (ERG, ACC, etc.)
  deriving DecidableEq, BEq, Repr

/-- Argument strength: prominence relative to role prototypicality.

    "Strong" means prominent (animate, definite, pronominal). The crucial
    insight is that strength interacts differently with each role:
    - Strong A = prototypical agent (inherently distinguishable from P)
    - Strong P = *atypical* patient (confusable with A)

    This reversal is why Distinguish targets weak subjects but strong
    objects, while Identify uniformly targets strong arguments. -/
inductive Strength where
  | strong : Strength   -- prominent
  | weak   : Strength   -- non-prominent
  deriving DecidableEq, BEq, Repr

/-- All form–meaning pairs for asymmetrical marking. -/
def allPairs : List (CaseForm × Strength) :=
  [(.zero, .strong), (.zero, .weak), (.overt, .strong), (.overt, .weak)]

-- ============================================================================
-- § 2: Constraints (de Hoop & Malchukov 2008, §2)
-- ============================================================================

/-- **Identify** (I): Case should identify the argument's role.
    Overt marking matches strong arguments (marking = marked role);
    zero matches weak arguments (no marking = unmarked role).
    Penalizes form/strength mismatch: (overt, weak) and (zero, strong).

    Same for both argument positions — Identify is role-independent.
    Tableau (18) and (29). -/
def identify : NamedConstraint (CaseForm × Strength) :=
  { name := "Identify"
    family := .markedness
    eval := λ p => match p with
      | (.overt, .strong) => 0  -- overt marking identifies strong role
      | (.zero, .weak)    => 0  -- zero matches weak/unmarked
      | (.overt, .weak)   => 1  -- overt on weak = misidentification
      | (.zero, .strong)  => 1  -- strong role unidentified
  }

/-- **Distinguish for subjects** (D_A): Unmarked weak subjects are
    confusable with objects. Strong subjects are inherently distinguishable.
    Only (Ø, weak) violates.

    Weak A is atypical (agent-like properties are low) → confusable with P.
    Strong A is typical → clearly agent, no marking needed.
    Tableau (21), p. 573. -/
def distinguishSubj : NamedConstraint (CaseForm × Strength) :=
  { name := "Distinguish(A)"
    family := .markedness
    eval := λ p => match p with
      | (.zero, .weak) => 1  -- weak subject unmarked = indistinguishable
      | _               => 0
  }

/-- **Distinguish for objects** (D_P): Unmarked strong objects are
    confusable with subjects. Weak objects are inherently distinguishable.
    Only (Ø, strong) violates.

    The reversal from `distinguishSubj` is the key to DOM convergence:
    strong *patients* are atypical (agent-like), so Distinguish targets
    them — the same pattern as Identify.
    Tableau (32)/(35). -/
def distinguishObj : NamedConstraint (CaseForm × Strength) :=
  { name := "Distinguish(P)"
    family := .markedness
    eval := λ p => match p with
      | (.zero, .strong) => 1  -- strong object unmarked = confusable
      | _                 => 0
  }

/-- **Economy** (*!): Penalizes any overt case marker.
    Same as Aissen's (2003) economy family. -/
def economy : NamedConstraint (CaseForm × Strength) :=
  { name := "*!"
    family := .faithfulness
    eval := λ p => match p with
      | (.overt, _) => 1
      | (.zero, _)  => 0
  }

/-- Build the violation profile for a ranking. -/
def profileFor (ranking : List (NamedConstraint (CaseForm × Strength)))
    (p : CaseForm × Strength) : List Nat :=
  ranking.map λ c => c.eval p

-- ============================================================================
-- § 3: DSM — Subject Case (Divergence)
-- ============================================================================

/-! Identify and Distinguish make opposite predictions for subjects.
    This divergence explains the two attested DSM strategies. -/

/-- I >> *! for subjects: strong subjects get ERG (Manipuri pattern).
    Tableau (18), p. 572: Identify drives overt marking of the prototypical
    (strong) agent, because ERG "identifies" the strong agent role. -/
theorem dsm_identify :
    superoptimal allPairs (profileFor [identify, economy])
    = [(.zero, .weak), (.overt, .strong)] := by native_decide

/-- D >> *! for subjects: weak subjects get ERG (Fore pattern).
    Tableau (21), p. 573: Distinguish drives overt marking of the atypical
    (weak) agent, because it's confusable with the patient. -/
theorem dsm_distinguish :
    superoptimal allPairs (profileFor [distinguishSubj, economy])
    = [(.zero, .strong), (.overt, .weak)] := by native_decide

/-- *! >> I for subjects: neutral (no DSM). Economy dominates. -/
theorem dsm_economy_over_identify :
    superoptimal allPairs (profileFor [economy, identify])
    = [(.zero, .weak)] := by native_decide

/-- *! >> D for subjects: neutral (no DSM). Economy dominates. -/
theorem dsm_economy_over_distinguish :
    superoptimal allPairs (profileFor [economy, distinguishSubj])
    = [(.zero, .strong)] := by native_decide

-- ============================================================================
-- § 4: DOM — Object Case (Convergence)
-- ============================================================================

/-! Identify and Distinguish make the **same** prediction for objects:
    mark strong (prominent) patients. This convergence is the paper's
    central result (p. 576) — it explains the universality and robustness
    of DOM compared to the variability of DSM.

    The convergence arises because "strong" objects are atypical patients:
    Identify wants to mark them (overt = strong), and Distinguish also
    wants to mark them (strong P is confusable with A). -/

/-- I >> *! for objects: strong objects get ACC.
    Tableau (31): ACC identifies the prominent patient. -/
theorem dom_identify :
    superoptimal allPairs (profileFor [identify, economy])
    = [(.zero, .weak), (.overt, .strong)] := by native_decide

/-- D >> *! for objects: strong objects get ACC — same as Identify!
    Tableau (32)/(35): ACC distinguishes the prominent (confusable)
    patient from the agent. -/
theorem dom_distinguish :
    superoptimal allPairs (profileFor [distinguishObj, economy])
    = [(.zero, .weak), (.overt, .strong)] := by native_decide

/-- **DOM convergence** (p. 576): Identify and Distinguish produce
    identical superoptimal sets for objects. This is the strongest
    form: the literal output lists are equal. -/
theorem dom_convergence :
    superoptimal allPairs (profileFor [identify, economy]) =
    superoptimal allPairs (profileFor [distinguishObj, economy]) := by
  native_decide

/-- **DSM divergence**: Identify and Distinguish produce different
    superoptimal sets for subjects. Contrast with `dom_convergence`. -/
theorem dsm_divergence :
    superoptimal allPairs (profileFor [identify, economy]) ≠
    superoptimal allPairs (profileFor [distinguishSubj, economy]) := by
  native_decide

-- ============================================================================
-- § 5: Case-Pattern Extraction
-- ============================================================================

/-- Extract the case form assigned to a given strength level from the
    superoptimal set. If no pair matches, defaults to zero (Economy wins
    by default when no superoptimal pair covers this meaning). -/
def extractForm (pairs : List (CaseForm × Strength)) (s : Strength) : CaseForm :=
  match pairs.find? (·.2 == s) with
  | some (f, _) => f
  | none => .zero

/-- A case-marking pattern for one argument position: what form each
    strength level receives. -/
structure MarkingPattern where
  strongForm : CaseForm
  weakForm   : CaseForm
  deriving DecidableEq, BEq, Repr

/-- Derive the marking pattern from a ranking's superoptimal set. -/
def markingPattern (ranking : List (NamedConstraint (CaseForm × Strength)))
    : MarkingPattern :=
  let pairs := superoptimal allPairs (profileFor ranking)
  ⟨extractForm pairs .strong, extractForm pairs .weak⟩

/-- **Complete subject typology** (Table 1, p. 573).
    Exactly 3 patterns: mark strong, mark weak, mark neither. -/
theorem subject_typology :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ ∧
    markingPattern [economy, identify] = ⟨.zero, .zero⟩ ∧
    markingPattern [economy, distinguishSubj] = ⟨.zero, .zero⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Object marking always targets strong** when I or D dominates.
    Both constraints agree on the object pattern; the only variation
    is whether marking occurs at all (functional >> Economy vs. not). -/
theorem object_typology :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [distinguishObj, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [economy, identify] = ⟨.zero, .zero⟩ ∧
    markingPattern [economy, distinguishObj] = ⟨.zero, .zero⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 6: Symmetrical Marking (§3, p. 574–578)
-- ============================================================================

/-! Languages like Finnish (ACC vs. PART for objects) and Lezgian (ERG vs.
    OBL for subjects) use two *overt* case forms that alternate by argument
    strength. This is **symmetrical** differential marking.

    The key theorem: Distinguish cannot derive symmetrical marking. All
    overt forms satisfy Distinguish equally, so Distinguish has no basis
    for assigning different overt forms to different strengths. The result
    is that both overt forms map to the same strength (strong for objects,
    leaving weak uncovered). Only Identify can pair each overt form with
    a distinct strength.

    "asymmetrical differential case marking can sometimes be explained by
    DISTINGUISHABILITY, symmetrical differential case marking is necessarily
    due to IDENTIFY" (p. 576). -/

/-- Case forms for symmetrical marking: two overt forms plus zero. -/
inductive SymForm where
  | zero  : SymForm   -- Ø
  | form1 : SymForm   -- e.g., ACC (Finnish), ERG (Lezgian)
  | form2 : SymForm   -- e.g., PART (Finnish), OBL (Lezgian)
  deriving DecidableEq, BEq, Repr

/-- All symmetrical-marking form–meaning pairs. -/
def symPairs : List (SymForm × Strength) :=
  [(.zero, .strong), (.zero, .weak),
   (.form1, .strong), (.form1, .weak),
   (.form2, .strong), (.form2, .weak)]

/-- Identify for 3-form system: form1 matches strong, form2 matches weak.
    Tableau (29), p. 576: ACC identifies strong P, PART identifies weak P. -/
def identifySym : NamedConstraint (SymForm × Strength) :=
  { name := "Identify"
    family := .markedness
    eval := λ p => match p with
      | (.form1, .strong) => 0  -- form1 identifies strong
      | (.form2, .weak)   => 0  -- form2 identifies weak
      | (.zero, _)        => 1  -- zero doesn't identify
      | (.form1, .weak)   => 1  -- form1 on weak = mismatch
      | (.form2, .strong) => 1  -- form2 on strong = mismatch
  }

/-- Distinguish for objects in 3-form system: only (Ø, strong) violates.
    Both overt forms satisfy Distinguish identically. -/
def distinguishObjSym : NamedConstraint (SymForm × Strength) :=
  { name := "Distinguish(P)"
    family := .markedness
    eval := λ p => match p with
      | (.zero, .strong) => 1
      | _                 => 0
  }

/-- Economy for 3-form system. -/
def economySym : NamedConstraint (SymForm × Strength) :=
  { name := "*!"
    family := .faithfulness
    eval := λ p => match p with
      | (.form1, _) => 1
      | (.form2, _) => 1
      | (.zero, _)  => 0
  }

def symProfileFor (ranking : List (NamedConstraint (SymForm × Strength)))
    (p : SymForm × Strength) : List Nat :=
  ranking.map λ c => c.eval p

/-- **Distinguish cannot discriminate overt forms** (structural theorem).
    Both overt forms receive identical violations from Distinguish for
    any meaning. This is the formal basis for the claim that symmetrical
    marking requires Identify. -/
theorem distinguish_overt_indifferent :
    ∀ (s : Strength),
      distinguishObjSym.eval (.form1, s) = distinguishObjSym.eval (.form2, s) := by
  intro s; cases s <;> rfl

/-- I >> *! in 3-form system: form1 for strong, form2 for weak.
    Tableau (29), p. 576: Finnish ACC/PART alternation.
    Each overt form is paired with a distinct strength. -/
theorem sym_identify :
    superoptimal symPairs (symProfileFor [identifySym, economySym])
    = [(.form1, .strong), (.form2, .weak)] := by native_decide

/-- D >> *! in 3-form system: both overt forms map to strong, zero
    maps to weak. Distinguish cannot differentiate form1 from form2 —
    both satisfy D identically — so both are superoptimal for strong.
    No overt form is paired with weak. -/
theorem sym_distinguish_no_differentiation :
    superoptimal symPairs (symProfileFor [distinguishObjSym, economySym])
    = [(.zero, .weak), (.form1, .strong), (.form2, .strong)] := by native_decide

/-- **Symmetrical marking requires Identify**: under Identify, each
    overt form is paired with a unique strength (form1↔strong, form2↔weak).
    Under Distinguish, no overt form is paired with weak — the
    symmetrical alternation cannot arise. -/
theorem symmetrical_requires_identify :
    -- Identify produces the symmetrical pattern: distinct overt forms for each strength
    let ident := superoptimal symPairs (symProfileFor [identifySym, economySym])
    let dist := superoptimal symPairs (symProfileFor [distinguishObjSym, economySym])
    -- Under Identify: exactly one overt form per strength level
    (ident.any (λ p => p.1 == .form1 && p.2 == .strong) &&
     ident.any (λ p => p.1 == .form2 && p.2 == .weak) &&
    -- Under Distinguish: NO overt form is paired with weak
     dist.all (λ p => !(p.1 != .zero && p.2 == .weak))) = true := by
  native_decide

-- ============================================================================
-- § 7: PaIP and Alignment Correlation (§4, p. 580)
-- ============================================================================

/-! The **Primary Actant Immunity Principle** (PaIP) replaces Economy with
    an alignment-sensitive constraint. The primary actant is the argument
    encoded like the intransitive subject:
    - In nominative-accusative: the A/S subject
    - In ergative-absolutive: the P/S object

    PaIP penalizes overt marking of the primary actant. When PaIP outranks
    the functional constraints (I, D), it blocks differential marking of
    the primary actant. This derives:
    - DOM is found in nom-acc (marking objects doesn't violate PaIP)
    - DSM is found in ergative (marking subjects doesn't violate PaIP)

    "DOM is characteristic of nominative-accusative languages, while DSM
    is found primarily in ergative languages" (p. 580).

    When I/D conflicts with PaIP (e.g., Identify wants to mark the primary
    actant), voice alternation resolves the conflict: passive in nom-acc,
    antipassive in ergative (p. 582). -/

/-- PaIP: Penalizes overt marking of the primary actant.
    Same violation profile as Economy — the difference is that PaIP
    only applies to the primary actant's position. -/
def paip : NamedConstraint (CaseForm × Strength) :=
  { name := "PaIP"
    family := .faithfulness
    eval := λ p => match p with
      | (.overt, _) => 1
      | (.zero, _)  => 0
  }

/-- **Nom-acc: PaIP blocks DSM** (p. 580).
    Subject = primary actant. PaIP >> I for subjects: no marking.
    PaIP >> D for subjects: no marking. -/
theorem nomacc_paip_blocks_dsm :
    markingPattern [paip, identify] = ⟨.zero, .zero⟩ ∧
    markingPattern [paip, distinguishSubj] = ⟨.zero, .zero⟩ := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Nom-acc: DOM proceeds** (p. 580).
    Objects are NOT the primary actant, so PaIP doesn't apply.
    I >> *! for objects: mark strong patients (DOM). -/
theorem nomacc_dom_proceeds :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [distinguishObj, economy] = ⟨.overt, .zero⟩ := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Ergative: PaIP blocks DOM** (p. 580).
    Object = primary actant. PaIP >> I for objects: no marking.
    PaIP >> D for objects: no marking. -/
theorem erg_paip_blocks_dom :
    markingPattern [paip, identify] = ⟨.zero, .zero⟩ ∧
    markingPattern [paip, distinguishObj] = ⟨.zero, .zero⟩ := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Ergative: DSM proceeds** (p. 580).
    Subjects are NOT the primary actant, so PaIP doesn't apply.
    D >> *! for subjects: mark weak agents (DSM). -/
theorem erg_dsm_proceeds :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Alignment correlation** (p. 580): the full picture.
    PaIP + I/D derive the observed distribution of differential marking
    across alignment types: DOM ↔ nom-acc, DSM ↔ ergative. -/
theorem alignment_correlation :
    -- Nom-acc: DOM but not DSM
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧          -- DOM possible
    markingPattern [paip, identify] = ⟨.zero, .zero⟩ ∧              -- DSM blocked
    -- Ergative: DSM but not DOM
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ ∧   -- DSM possible
    markingPattern [paip, distinguishObj] = ⟨.zero, .zero⟩ := by    -- DOM blocked
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 8: Bridge to Aissen (2003)
-- ============================================================================

/-! Economy (*!) is the same constraint across both analyses. The DOM
    convergence result (§4) explains why Aissen's harmonic alignment
    works for DOM: both the Identify and Distinguish motivations predict
    the same monotone pattern.

    Aissen's iconicity family (*Ø/X) corresponds to the Distinguish
    perspective: marking targets atypical arguments first. For P, this
    aligns with Identify (both target strong P). For A, Distinguish
    diverges from Identify (targeting weak A vs. strong A). -/

/-- Economy has the same violation profile as Aissen's economy family:
    1 violation per overt marker, 0 for zero markers. -/
theorem economy_matches_aissen :
    (economy.eval (.overt, .strong) = 1) ∧
    (economy.eval (.zero, .strong) = 0) ∧
    (economy.eval (.overt, .weak) = 1) ∧
    (economy.eval (.zero, .weak) = 0) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- DOM convergence is consistent with Aissen's monotonicity:
    overt marking targets the top of the prominence hierarchy first.
    Under both Identify and Distinguish, strong (prominent) objects
    are marked before weak (non-prominent) ones. -/
theorem dom_targets_prominent :
    let pairs_i := superoptimal allPairs (profileFor [identify, economy])
    let pairs_d := superoptimal allPairs (profileFor [distinguishObj, economy])
    (pairs_i.any (λ p => p.1 == .overt && p.2 == .strong) &&
     pairs_i.any (λ p => p.1 == .zero && p.2 == .weak) &&
     pairs_d.any (λ p => p.1 == .overt && p.2 == .strong) &&
     pairs_d.any (λ p => p.1 == .zero && p.2 == .weak)) = true := by
  native_decide

end Phenomena.Case.Studies.DeHoopMalchukov2008
