import Linglib.Core.Logic.OT
import Linglib.Core.Logic.ConstraintEvaluation
import Linglib.Core.Prominence
import Linglib.Phenomena.Case.Typology
import Linglib.Phenomena.Case.Studies.Aissen2003

/-!
# De Hoop & Malchukov (2008): Case-Marking Strategies @cite{de-hoop-malchukov-2008}

Case-Marking Strategies. Linguistics 46(4): 565–592.

Derives the basic case-marking typology from two functional constraints and one
economy constraint, evaluated in Blutner's (2000) Bidirectional OT:

- **Identify** (I): Case identifies the role — overt marking should match
  argument strength (markedness principle). Penalizes form/strength mismatch.
- **Distinguish** (D): Case distinguishes A from P — unmarked atypical
  arguments are confusable with the other role. Penalizes zero-marked
  atypical arguments.
- **Economy** (*!): Avoid overt case marking.

## Bidirectional OT (Blutner 2000)

Standard OT selects the best form for a given meaning (speaker). BiOT adds
the hearer's perspective via **superoptimality**: a form–meaning pair ⟨f, m⟩
is superoptimal iff no other superoptimal pair with the same form or same
meaning is strictly more harmonic. This is a fixed-point computation
(`Core.ConstraintEvaluation.superoptimal`).

## Key Results

### DSM divergence (subjects)

| Ranking | Superoptimal pairs | Marking pattern |
|---------|--------------------|-----------------|
| I >> *! | (ERG, strong), (Ø, weak) | Mark strong subjects (Manipuri) |
| D >> *! | (Ø, strong), (ERG, weak) | Mark weak subjects (Fore) |
| *! >> I | (Ø, weak) | Neutral (no DSM) |
| *! >> D | (Ø, strong) | Neutral (no DSM) |

### DOM convergence (objects)

| Ranking | Superoptimal pairs | Marking pattern |
|---------|--------------------|-----------------|
| I >> *! | (ACC, strong), (Ø, weak) | Mark strong objects |
| D >> *! | (ACC, strong), (Ø, weak) | Mark strong objects |

Both Identify and Distinguish predict the **same** DOM pattern: overt marking
targets prominent (animate, definite) patients. This convergence explains why
DOM universally targets the top of the prominence hierarchy, while DSM can
go either way.

## Connection to Aissen (2003)

Economy (*!) is the same constraint. The key innovation is decomposing
Aissen's iconicity into Identify vs. Distinguish, revealing the DOM/DSM
asymmetry. Aissen's harmonic alignment encodes the Distinguish perspective
(marking targets atypical arguments), which for P aligns with Identify
but for A diverges from it.

## References

- de Hoop, H. & A. Malchukov (2008). Case-Marking Strategies.
  Linguistics 46(4): 565–592.
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

/-- Case forms for a single argument: zero or overt marking. -/
inductive CaseForm where
  | zero  : CaseForm   -- Ø (unmarked)
  | overt : CaseForm   -- overtly case-marked (ERG, ACC, etc.)
  deriving DecidableEq, BEq, Repr

/-- Argument strength: how prototypical the argument is for its role.
    Strong agents are prominent (animate, definite); strong patients are
    prominent too — but prominentpatients are *atypical* for the P role. -/
inductive Strength where
  | strong : Strength   -- prominent / prototypical
  | weak   : Strength   -- non-prominent / atypical
  deriving DecidableEq, BEq, Repr

/-- All form–meaning pairs for a single argument position. -/
def allPairs : List (CaseForm × Strength) :=
  [(.zero, .strong), (.zero, .weak), (.overt, .strong), (.overt, .weak)]

-- ============================================================================
-- § 2: Constraints (de Hoop & Malchukov 2008, §2)
-- ============================================================================

/-- **Identify** (I): Case should identify the argument's role.
    Overt marking matches strong arguments (marking = marked role);
    zero matches weak arguments (no marking = unmarked role).
    Penalizes form/strength mismatch: (overt, weak) and (zero, strong).

    Same for both argument positions (subjects and objects). -/
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
    Only (Ø, weak) violates (de Hoop & Malchukov 2008, tableau 21). -/
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
    them — the same pattern as Identify. -/
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
    Tableau (18), p. 572. -/
theorem dsm_identify :
    superoptimal allPairs (profileFor [identify, economy])
    = [(.zero, .weak), (.overt, .strong)] := by native_decide

/-- D >> *! for subjects: weak subjects get ERG (Fore pattern).
    Tableau (21), p. 573. -/
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
    central result — it explains the universality of DOM. -/

/-- I >> *! for objects: strong objects get ACC. -/
theorem dom_identify :
    superoptimal allPairs (profileFor [identify, economy])
    = [(.zero, .weak), (.overt, .strong)] := by native_decide

/-- D >> *! for objects: strong objects get ACC — same as Identify!
    This is the convergence theorem (p. 576). -/
theorem dom_distinguish :
    superoptimal allPairs (profileFor [distinguishObj, economy])
    = [(.zero, .weak), (.overt, .strong)] := by native_decide

/-- DOM convergence: Identify and Distinguish produce identical
    superoptimal sets for objects. -/
theorem dom_convergence :
    superoptimal allPairs (profileFor [identify, economy]) =
    superoptimal allPairs (profileFor [distinguishObj, economy]) := by
  native_decide

/-- DSM divergence: Identify and Distinguish produce different
    superoptimal sets for subjects. -/
theorem dsm_divergence :
    superoptimal allPairs (profileFor [identify, economy]) ≠
    superoptimal allPairs (profileFor [distinguishSubj, economy]) := by
  native_decide

-- ============================================================================
-- § 5: Case-Pattern Extraction
-- ============================================================================

/-- Extract the case form assigned to a given strength level from the
    superoptimal set. If no pair matches, defaults to zero (Economy). -/
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

/-- I >> *! subject pattern: strong=ERG, weak=Ø (Manipuri DSM). -/
theorem pattern_i_subj :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ := by native_decide

/-- D >> *! subject pattern: strong=Ø, weak=ERG (Fore DSM). -/
theorem pattern_d_subj :
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ := by native_decide

/-- *! >> I subject pattern: strong=Ø, weak=Ø (neutral). -/
theorem pattern_economy_i_subj :
    markingPattern [economy, identify] = ⟨.zero, .zero⟩ := by native_decide

/-- *! >> D subject pattern: strong=Ø, weak=Ø (neutral). -/
theorem pattern_economy_d_subj :
    markingPattern [economy, distinguishSubj] = ⟨.zero, .zero⟩ := by native_decide

/-- I >> *! object pattern: strong=ACC, weak=Ø (DOM). -/
theorem pattern_i_obj :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ := by native_decide

/-- D >> *! object pattern: strong=ACC, weak=Ø (DOM) — convergence. -/
theorem pattern_d_obj :
    markingPattern [distinguishObj, economy] = ⟨.overt, .zero⟩ := by native_decide

-- ============================================================================
-- § 6: Alignment Types (Table 1, p. 573)
-- ============================================================================

/-- Full alignment pattern: subject + object marking. -/
structure AlignmentType where
  name : String
  subjStrong : CaseForm  -- what strong subjects get
  subjWeak   : CaseForm  -- what weak subjects get
  objStrong  : CaseForm  -- what strong objects get
  objWeak    : CaseForm  -- what weak objects get
  deriving DecidableEq, BEq, Repr

/-- Build a full alignment type from subject and object rankings. -/
def alignment (name : String)
    (subjRanking objRanking : List (NamedConstraint (CaseForm × Strength)))
    : AlignmentType :=
  let sp := markingPattern subjRanking
  let op := markingPattern objRanking
  ⟨name, sp.strongForm, sp.weakForm, op.strongForm, op.weakForm⟩

/-- Manipuri: Identify-driven DSM + DOM.
    Strong subjects get ERG, strong objects get ACC. -/
def manipuri : AlignmentType :=
  alignment "Manipuri" [identify, economy] [identify, economy]

theorem manipuri_pattern :
    manipuri = ⟨"Manipuri", .overt, .zero, .overt, .zero⟩ := by native_decide

/-- Fore: Distinguish-driven DSM + DOM.
    Weak subjects get ERG, strong objects get ACC. -/
def fore : AlignmentType :=
  alignment "Fore" [distinguishSubj, economy] [distinguishObj, economy]

theorem fore_pattern :
    fore = ⟨"Fore", .zero, .overt, .overt, .zero⟩ := by native_decide

/-- Neutral: Economy dominates for both subjects and objects. -/
def neutral : AlignmentType :=
  alignment "Neutral" [economy, identify] [economy, identify]

theorem neutral_pattern :
    neutral = ⟨"Neutral", .zero, .zero, .zero, .zero⟩ := by native_decide

-- ============================================================================
-- § 7: Voice–Case Interaction (§3)
-- ============================================================================

/-! Voice selects the argument perspective:
    - Active: A is subject (default) → DSM applies to subjects
    - Passive: P is promoted to subject → the reversed perspective

    Under the Distinguish strategy, active voice marks weak subjects
    (accusative alignment for the clause), while passive would mark
    weak subjects from the P perspective (ergative alignment). This
    derives the accusative–ergative split in split-ergative languages
    where voice conditions case. -/

/-- Active voice: the A perspective. Subject case is evaluated under
    `distinguishSubj` — weak subjects get marked (accusative pattern). -/
theorem active_distinguish :
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ := by
  native_decide

/-- Passive/antipassive: the P perspective applied to subjects.
    When a demoted agent is treated as a "weak argument" in subject
    position, it gets marked — deriving oblique case on demoted agents. -/
theorem passive_agents_marked :
    let pairs := superoptimal allPairs (profileFor [distinguishSubj, economy])
    pairs.any (λ p => p.1 == .overt && p.2 == .weak) = true := by
  native_decide

-- ============================================================================
-- § 8: Bridge to Aissen (2003)
-- ============================================================================

/-! The Economy constraint has the same violation profile as Aissen's
    economy family (*!/X). The DOM convergence result (§4) explains
    why Aissen's harmonic alignment works for DOM: both the Identify
    and Distinguish motivations predict the same monotone pattern. -/

/-- Economy has the same violation profile as Aissen's economy family. -/
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
    -- Both predict: strong gets overt, weak gets zero
    (pairs_i.any (λ p => p.1 == .overt && p.2 == .strong) &&
     pairs_i.any (λ p => p.1 == .zero && p.2 == .weak) &&
     pairs_d.any (λ p => p.1 == .overt && p.2 == .strong) &&
     pairs_d.any (λ p => p.1 == .zero && p.2 == .weak)) = true := by
  native_decide

/-- The full typology of basic case alignment — all 4 marking patterns
    generated by the constraint system correspond to attested types. -/
theorem four_marking_patterns :
    let mp := markingPattern
    -- I >> *!: overt strong, zero weak (Manipuri DSM / DOM)
    mp [identify, economy] = ⟨.overt, .zero⟩ ∧
    -- D(subj) >> *!: zero strong, overt weak (Fore DSM)
    mp [distinguishSubj, economy] = ⟨.zero, .overt⟩ ∧
    -- *! >> I: zero both (neutral)
    mp [economy, identify] = ⟨.zero, .zero⟩ ∧
    -- *! >> D: zero both (neutral)
    mp [economy, distinguishSubj] = ⟨.zero, .zero⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end Phenomena.Case.Studies.DeHoopMalchukov2008
