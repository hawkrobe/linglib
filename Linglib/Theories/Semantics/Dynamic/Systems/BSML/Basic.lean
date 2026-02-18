import Linglib.Theories.Semantics.Dynamic.TeamSemantics

/-!
# Bilateral State-based Modal Logic (BSML) — Core

Core definitions for BSML (Aloni 2022): formulas, models, bilateral support/anti-support,
and double negation elimination.

BSML evaluates formulas bilaterally against teams (sets of worlds):
- **Support** (⊨⁺): positive evaluation
- **Anti-support** (⊨⁻): negative evaluation
- **Negation**: swaps support and anti-support → DNE is definitional

Key innovations over classical modal logic:
- **Split disjunction**: t ⊨ φ ∨ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨ φ ∧ t₂ ⊨ ψ
- **Non-emptiness atom (NE)**: t ⊨ NE iff t ≠ ∅

## References

- Aloni, M. (2022). Logic and conversation: The case of free choice. S&P 15.
  @cite{aloni-2022}
- Aloni, M., Anttila, A. & Yang, F. (2024). State-based Modal Logics for Free Choice.
-/

namespace Semantics.Dynamic.BSML

open Semantics.Dynamic.TeamSemantics

-- ============================================================================
-- Formulas
-- ============================================================================

/--
BSML formulas with bilateral support conditions.

The key innovation is SPLIT DISJUNCTION: a team supports φ ∨ ψ iff
the team can be partitioned into parts supporting each disjunct.
-/
inductive BSMLFormula where
  /-- Atomic proposition -/
  | atom : String → BSMLFormula
  /-- Non-emptiness atom: team is non-empty -/
  | ne : BSMLFormula
  /-- Negation: swap support/anti-support -/
  | neg : BSMLFormula → BSMLFormula
  /-- Conjunction -/
  | conj : BSMLFormula → BSMLFormula → BSMLFormula
  /-- Split disjunction (Aloni's key innovation) -/
  | disj : BSMLFormula → BSMLFormula → BSMLFormula
  /-- Possibility modal -/
  | poss : BSMLFormula → BSMLFormula
  /-- Necessity modal -/
  | nec : BSMLFormula → BSMLFormula
  deriving Repr

-- ============================================================================
-- Model
-- ============================================================================

/--
A BSML model bundles:
- A finite list of worlds
- An accessibility relation R (for modals), given as R[w] = accessible team
- A valuation V (atomic propositions)
-/
structure BSMLModel (W : Type*) where
  /-- The finite universe of worlds -/
  worlds : List W
  /-- Accessibility: R[w] = worlds accessible from w -/
  access : W → Team W
  /-- Valuation: which atoms are true at which worlds -/
  valuation : String → W → Bool

/-- Universal accessibility (S5-like): all worlds accessible from all -/
def BSMLModel.universal {W : Type*} (worlds : List W) : BSMLModel W where
  worlds := worlds
  access := λ _ => Team.full
  valuation := λ _ _ => false

/-- Indisputable accessibility: all worlds in team have same accessible worlds -/
def BSMLModel.isIndisputable {W : Type*} (M : BSMLModel W) (t : Team W) : Bool :=
  let members := t.toList M.worlds
  match members with
  | [] => true
  | w :: rest => rest.all λ v => (M.access w).beq (M.access v) M.worlds

-- ============================================================================
-- Helper Functions for Team Operations
-- ============================================================================

/-- Generate all subsets of a list -/
def allSubsets {α : Type*} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      let withoutX := allSubsets xs
      withoutX ++ withoutX.map (x :: ·)

/-- Generate all possible splits of a team into two parts -/
def generateSplits {W : Type*} [DecidableEq W] (t : Team W) (worlds : List W) :
    List (Team W × Team W) :=
  let members := t.toList worlds
  (allSubsets members).map λ left =>
    let leftTeam : Team W := Team.ofList left
    let rightTeam : Team W := λ w => t w && !leftTeam w
    (leftTeam, rightTeam)

/-- Generate all subteams of a team -/
def generateSubteams {W : Type*} [DecidableEq W] (t : Team W) (worlds : List W) :
    List (Team W) :=
  let members := t.toList worlds
  (allSubsets members).map Team.ofList

-- ============================================================================
-- Support and Anti-Support (Mutually Defined)
-- ============================================================================

/-
Positive support: t ⊨⁺ φ (Definition 2 from Aloni 2022)

Negative support (anti-support): t ⊨⁻ φ

These are mutually defined: negation swaps support and anti-support.
-/
mutual
def support {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W) : Bool :=
  match φ with
  | .atom p => t.all (M.valuation p) M.worlds
  | .ne => t.isNonEmpty M.worlds
  | .neg ψ => antiSupport M ψ t
  | .conj ψ₁ ψ₂ => support M ψ₁ t && support M ψ₂ t
  | .disj ψ₁ ψ₂ =>
      let splits := generateSplits t M.worlds
      splits.any λ (t1, t2) => support M ψ₁ t1 && support M ψ₂ t2
  | .poss ψ =>
      t.all (λ w =>
        let accessible := M.access w
        let subteams := generateSubteams accessible M.worlds
        subteams.any λ t' => t'.isNonEmpty M.worlds && support M ψ t'
      ) M.worlds
  | .nec ψ =>
      t.all (λ w => support M ψ (M.access w)) M.worlds

def antiSupport {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W) : Bool :=
  match φ with
  | .atom p => t.all (λ w => !M.valuation p w) M.worlds
  | .ne => t.isEmpty M.worlds
  | .neg ψ => support M ψ t
  | .conj ψ₁ ψ₂ => antiSupport M ψ₁ t || antiSupport M ψ₂ t
  | .disj ψ₁ ψ₂ => antiSupport M ψ₁ t && antiSupport M ψ₂ t
  | .poss ψ =>
      t.all (λ w =>
        let accessible := M.access w
        let subteams := generateSubteams accessible M.worlds
        subteams.all λ t' => t'.isEmpty M.worlds || antiSupport M ψ t'
      ) M.worlds
  | .nec ψ =>
      t.any (λ w => antiSupport M ψ (M.access w)) M.worlds
end

-- ============================================================================
-- Double Negation Elimination
-- ============================================================================

/--
DNE holds definitionally: ¬¬φ has the same support conditions as φ.

This follows from negation swapping support and anti-support.
-/
theorem dne_support {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W) :
    support M (.neg (.neg φ)) t = support M φ t := by
  simp only [support, antiSupport]

theorem dne_antiSupport {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W) :
    antiSupport M (.neg (.neg φ)) t = antiSupport M φ t := by
  simp only [support, antiSupport]

end Semantics.Dynamic.BSML
