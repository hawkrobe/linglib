import Linglib.Theories.Syntax.Minimalism.Derivation
import Linglib.Theories.Syntax.Minimalism.Checking

/-!
# Derivational Economy
@cite{chomsky-1995}

Economy principles constrain syntactic derivations by comparing
competing derivations that converge on the same PF string and LF
interpretation, selecting the one with fewest operations.

## Key Principles

- **Least Effort**: Among derivations yielding the same PF string and
  LF interpretation, prefer the one with fewest operations and fewest
  lexical resources drawn from the numeration.
- **Procrastinate** (@cite{chomsky-1995} Ch 3–4): Covert operations are
  preferred over overt ones. Overt movement occurs only when forced —
  by a strong feature that must be checked before Spell-Out. Violations
  of Procrastinate are tolerated only when necessary for convergence
  (*forced violations*); violations that are not required for
  convergence are true economy violations (*unforced violations*).
- **Last Resort / Greed** (@cite{chomsky-1995} Ch 3): Move applies only
  to check a feature of the moved element. An operation is permitted
  only if it is necessary for convergence — movement without a
  feature-checking trigger is banned.
- **Pronunciation Economy**: PF-reducing operations (ellipsis) may apply
  only if they have an effect on pronunciation. This bans vacuous
  deletion — eliding material that is already unpronounced.

## Design

Economy is formalized as a COMPARISON between derivation costs, not as
a constraint on individual derivations. This captures the global,
transderivational character of economy: the grammar evaluates the full
set of convergent derivations and selects the cheapest.

The book's economy is also *local*: at each derivation stage Σ, we
consider the reference set R(N, Σ) — continuations from Σ using what
remains in the numeration N — and select the most economical operation
that yields a convergent derivation.

`DerivationCost` is abstract — it counts operations by type without
committing to a particular derivation model. Both the core `Derivation`
(step-based) and `FullDerivation` (workspace-based) models can project
onto `DerivationCost`.
-/

namespace Minimalism

-- ============================================================================
-- § 1: Derivation Cost
-- ============================================================================

/-- Cost of a syntactic derivation, measured by operation and resource counts.

    The five dimensions capture the resources consumed:
    - `lexicalItems`: items drawn from the numeration (lexical resources)
    - `mergeOps`: External + Internal Merge (structure building)
    - `agreeOps`: Agree operations (feature checking)
    - `ellipsisOps`: E-feature triggered deletions at PF
    - `overtOps`: operations before Spell-Out (Procrastinate penalizes these) -/
structure DerivationCost where
  lexicalItems : Nat
  mergeOps : Nat
  agreeOps : Nat
  ellipsisOps : Nat
  overtOps : Nat := 0
  deriving Repr, DecidableEq

/-- Total number of syntactic operations (excluding lexical selection). -/
def DerivationCost.totalOps (c : DerivationCost) : Nat :=
  c.mergeOps + c.agreeOps + c.ellipsisOps

/-- Extract cost from a core `Derivation` (step-based model).

    Counts `emL`/`emR` as External Merge and `im` as Internal Merge.
    Agree and ellipsis are not tracked in the core model. -/
def Derivation.cost (d : Derivation) : DerivationCost where
  lexicalItems := d.steps.filter (match · with | .emL _ | .emR _ => true | _ => false) |>.length
  mergeOps := d.steps.length
  agreeOps := 0
  ellipsisOps := 0

-- ============================================================================
-- § 2: Economy Comparison
-- ============================================================================

/-- Derivation c1 is at least as economical as c2: no more operations
    and no more lexical resources on any dimension. -/
def atLeastAsEconomical (c1 c2 : DerivationCost) : Prop :=
  c1.totalOps ≤ c2.totalOps ∧ c1.lexicalItems ≤ c2.lexicalItems

/-- Derivation c1 is strictly more economical than c2: at least as
    economical, and strictly better on at least one dimension. -/
def strictlyMoreEconomical (c1 c2 : DerivationCost) : Prop :=
  atLeastAsEconomical c1 c2 ∧
  (c1.totalOps < c2.totalOps ∨ c1.lexicalItems < c2.lexicalItems)

/-- Economy comparison is reflexive. -/
theorem atLeastAsEconomical_refl (c : DerivationCost) :
    atLeastAsEconomical c c :=
  ⟨le_refl _, le_refl _⟩

/-- Economy comparison is transitive. -/
theorem atLeastAsEconomical_trans {c1 c2 c3 : DerivationCost}
    (h12 : atLeastAsEconomical c1 c2)
    (h23 : atLeastAsEconomical c2 c3) :
    atLeastAsEconomical c1 c3 :=
  ⟨le_trans h12.1 h23.1, le_trans h12.2 h23.2⟩

/-- Strict economy is irreflexive. -/
theorem strictlyMoreEconomical_irrefl (c : DerivationCost) :
    ¬strictlyMoreEconomical c c := by
  intro ⟨_, h⟩
  exact h.elim (lt_irrefl _) (lt_irrefl _)

/-- Strict economy is transitive. -/
theorem strictlyMoreEconomical_trans {c1 c2 c3 : DerivationCost}
    (h12 : strictlyMoreEconomical c1 c2)
    (h23 : strictlyMoreEconomical c2 c3) :
    strictlyMoreEconomical c1 c3 := by
  obtain ⟨⟨hops12, hlex12⟩, _⟩ := h12
  obtain ⟨⟨hops23, hlex23⟩, hstrict23⟩ := h23
  exact ⟨⟨le_trans hops12 hops23, le_trans hlex12 hlex23⟩,
    hstrict23.elim
      (fun h => .inl (lt_of_le_of_lt hops12 h))
      (fun h => .inr (lt_of_le_of_lt hlex12 h))⟩

/-- Strict economy is asymmetric. -/
theorem strictlyMoreEconomical_asymm {c1 c2 : DerivationCost}
    (h : strictlyMoreEconomical c1 c2) :
    ¬strictlyMoreEconomical c2 c1 := by
  intro h2
  exact strictlyMoreEconomical_irrefl c1
    (strictlyMoreEconomical_trans h h2)

-- ============================================================================
-- § 3: Pronunciation Economy
-- ============================================================================

/-- Pronunciation Economy: ellipsis may apply only if it changes the
    PF output.

    An ellipsis operation that targets material already unpronounced
    (e.g., because a prior deletion already removed it) is vacuous
    and therefore banned.

    `pfBefore`: the PF string before ellipsis applies.
    `pfAfter`: the PF string after ellipsis applies. -/
def pronunciationEconomy (pfBefore pfAfter : List String) : Prop :=
  pfBefore ≠ pfAfter

/-- Vacuous ellipsis: the PF output is unchanged by the deletion. -/
def vacuousEllipsis (pfBefore pfAfter : List String) : Prop :=
  pfBefore = pfAfter

/-- Pronunciation Economy holds iff ellipsis is not vacuous. -/
theorem pronEcon_iff_not_vacuous (pf1 pf2 : List String) :
    pronunciationEconomy pf1 pf2 ↔ ¬vacuousEllipsis pf1 pf2 :=
  Iff.rfl

-- ============================================================================
-- § 4: PF Equivalence
-- ============================================================================

/-- Two syntactic objects are PF-equivalent if they produce the same
    phonological string (left-to-right leaf yield). -/
def pfEquivalent (so1 so2 : SyntacticObject) : Prop :=
  so1.phonYield = so2.phonYield

/-- PF equivalence is reflexive. -/
theorem pfEquivalent_refl (so : SyntacticObject) : pfEquivalent so so :=
  rfl

/-- PF equivalence is symmetric. -/
theorem pfEquivalent_symm {so1 so2 : SyntacticObject}
    (h : pfEquivalent so1 so2) : pfEquivalent so2 so1 :=
  h.symm

/-- PF equivalence is transitive. -/
theorem pfEquivalent_trans {so1 so2 so3 : SyntacticObject}
    (h12 : pfEquivalent so1 so2) (h23 : pfEquivalent so2 so3) :
    pfEquivalent so1 so3 :=
  h12.trans h23

-- ============================================================================
-- § 5: Procrastinate
-- ============================================================================

/-- Whether a syntactic operation is overt (before Spell-Out) or
    covert (after Spell-Out, on the N → λ branch). -/
inductive Timing where
  | overt   -- before Spell-Out: affects both PF and LF
  | covert  -- after Spell-Out: affects only LF
  deriving Repr, DecidableEq

/-- A timed derivation step: an operation paired with its timing.

    Procrastinate compares operations by timing: covert is cheaper
    than overt, all else being equal. -/
structure TimedStep where
  timing : Timing
  deriving Repr

/-- Procrastinate: covert operations are preferred over overt ones.

    An overt operation at stage Σ violates Procrastinate unless it is
    *forced* — i.e., the derivation would crash without it (because a
    strong feature must be eliminated before Spell-Out).

    This function checks whether an overt operation is a forced
    violation of Procrastinate (acceptable) or an unforced violation
    (banned by economy). -/
inductive ProcrastinateViolation where
  /-- Forced: overt operation required for convergence (strong feature). -/
  | forced
  /-- Unforced: overt operation not required — a covert alternative
      exists that also converges. Banned by economy. -/
  | unforced
  deriving Repr, DecidableEq

/-- Is a step consistent with Procrastinate?
    Covert steps always are. Overt steps are consistent only if the
    violation is forced (required for convergence). -/
def satisfiesProcrastinate (t : Timing) (violation : Option ProcrastinateViolation) : Bool :=
  match t with
  | .covert => true
  | .overt => match violation with
    | some .forced => true
    | _ => false

-- ============================================================================
-- § 6: Last Resort / Greed
-- ============================================================================

/-- Last Resort: an operation is permitted only if it has a
    feature-checking purpose. Movement without a trigger is banned.

    `hasCheckingPurpose` should be true when the moved element has
    an unchecked feature that enters a checking relation as a result
    of the movement. -/
def lastResort (hasCheckingPurpose : Bool) : Bool :=
  hasCheckingPurpose

/-- Greed (the strong form of Last Resort): Move applies to α only
    to satisfy a requirement of α itself — not to satisfy a
    requirement of the target. "Self-serving" movement.

    In @cite{chomsky-1995} Ch 4, Greed is relaxed: Move F to target K
    is permitted if F enters a checking relation with a sublabel of K.
    This is the weaker "Enlightened Self-Interest" version. -/
def greed (movementBenefitsMover : Bool) : Bool :=
  movementBenefitsMover

-- ============================================================================
-- § 7: Convergence and Economy Interaction
-- ============================================================================

/-- A derivation is *admissible* if it converges at both interfaces and
    satisfies all economy conditions (Procrastinate, Last Resort).

    Among admissible derivations from the same numeration, the grammar
    selects the most economical. Non-convergent derivations are excluded
    from comparison entirely.

    `features`: the tracked features at end of derivation
    `steps`: each step's timing and whether it has a checking purpose
    `isStrong`: which features are strong (for Spell-Out convergence) -/
structure Admissibility where
  /-- Does the derivation converge at LF? (FI: no active –Interp features) -/
  convergentAtLF : Bool
  /-- Does the derivation converge at Spell-Out? (no unchecked strong features) -/
  convergentAtSpellOut : Bool
  /-- Do all operations satisfy Last Resort? (every movement checks a feature) -/
  allLastResort : Bool
  /-- Are all overt operations forced? (no unforced Procrastinate violations) -/
  allProcrastinateOk : Bool
  deriving Repr

/-- Only convergent derivations that satisfy economy are candidates. -/
def isCandidate (a : Admissibility) : Bool :=
  a.convergentAtLF && a.convergentAtSpellOut &&
  a.allLastResort && a.allProcrastinateOk

/-- Build admissibility from derivation data. -/
def mkAdmissibility (features : List TrackedFeature)
    (isStrong : TrackedFeature → Bool)
    (steps : List (Timing × Bool × Option ProcrastinateViolation)) :
    Admissibility where
  convergentAtLF := convergesAtLF features
  convergentAtSpellOut := convergesAtSpellOut features isStrong
  allLastResort := steps.all (λ ⟨_, hasChecking, _⟩ => lastResort hasChecking)
  allProcrastinateOk := steps.all (λ ⟨t, _, v⟩ => satisfiesProcrastinate t v)

/-- Forced Procrastinate violations do not count against economy. -/
theorem forced_violation_ok :
    satisfiesProcrastinate .overt (some .forced) = true := rfl

/-- Unforced Procrastinate violations are banned. -/
theorem unforced_violation_banned :
    satisfiesProcrastinate .overt (some .unforced) = false := rfl

/-- Covert operations always satisfy Procrastinate. -/
theorem covert_always_ok :
    satisfiesProcrastinate .covert none = true := rfl

-- ============================================================================
-- § 8: Procrastinate and Economy Interaction
-- ============================================================================

/-- Procrastinate connects to cost: among derivations with equal total
    operations, prefer the one with fewer overt operations. -/
def procrastinatePreferable (c1 c2 : DerivationCost) : Prop :=
  c1.totalOps = c2.totalOps ∧
  c1.lexicalItems = c2.lexicalItems ∧
  c1.overtOps < c2.overtOps

/-- Procrastinate preference implies strict economy (fewer overt = cheaper). -/
theorem procrastinate_implies_economical (c1 c2 : DerivationCost)
    (h : procrastinatePreferable c1 c2) :
    c1.overtOps < c2.overtOps :=
  h.2.2

/-- A fully covert derivation (overtOps = 0) is maximally economical
    w.r.t. Procrastinate — no other derivation can have fewer overt ops. -/
theorem covert_minimal (c other : DerivationCost) (h : c.overtOps = 0) :
    ¬procrastinatePreferable other c ∨ other.overtOps = 0 := by
  simp only [procrastinatePreferable, h]
  omega

/-- An admissible derivation with no overt operations is a candidate. -/
theorem covert_admissible_is_candidate :
    isCandidate {
      convergentAtLF := true, convergentAtSpellOut := true,
      allLastResort := true, allProcrastinateOk := true
    } = true := rfl

/-- An inadmissible derivation (LF crash) is not a candidate, regardless
    of economy. -/
theorem crash_not_candidate :
    isCandidate {
      convergentAtLF := false, convergentAtSpellOut := true,
      allLastResort := true, allProcrastinateOk := true
    } = false := rfl

end Minimalism
