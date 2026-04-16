import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Bilateral State-based Modal Logic (BSML) — Core Definitions
@cite{aloni-2022}

BSML is a bilateral, state-based modal logic in which formulas are evaluated
against **teams** (sets of worlds):
- **Support** (⊨⁺): positive evaluation
- **Anti-support** (⊨⁻): negative evaluation
- **Negation**: swaps support and anti-support → DNE is definitional

Key innovations over classical modal logic:
- **Split disjunction**: t ⊨⁺ φ ∨ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨⁺ φ ∧ t₂ ⊨⁺ ψ
- **Split conjunction (anti-support)**: t ⊨⁻ φ ∧ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨⁻ φ ∧ t₂ ⊨⁻ ψ
- **Non-emptiness atom (NE)**: t ⊨⁺ NE iff t ≠ ∅

Despite being state-based, BSML is a **static** logic (not dynamic):
formulas are evaluated against teams, not updated by them
(@cite{aloni-2022} p. 22).

## Bilateral Symmetry

The support and anti-support clauses exhibit a striking duality:

| Connective | Support (⊨⁺) | Anti-support (⊨⁻) |
|-----------|-------------|-------------------|
| p (atom) | ∀w∈s: V(w,p)=1 | ∀w∈s: V(w,p)=0 |
| ¬φ | s ⊨⁻ φ | s ⊨⁺ φ |
| φ ∧ ψ | s ⊨⁺ φ ∧ s ⊨⁺ ψ | ∃t,u: t∪u=s ∧ t ⊨⁻ φ ∧ u ⊨⁻ ψ |
| φ ∨ ψ | ∃t,u: t∪u=s ∧ t ⊨⁺ φ ∧ u ⊨⁺ ψ | s ⊨⁻ φ ∧ s ⊨⁻ ψ |
| ◇φ | ∀w∈s: ∃ ne t⊆R[w]: t ⊨⁺ φ | ∀w∈s: R[w] ⊨⁻ φ |
| □φ | ∀w∈s: R[w] ⊨⁺ φ | ∀w∈s: ∃ ne t⊆R[w]: t ⊨⁻ φ |
| NE | s ≠ ∅ | s = ∅ |

∧/∨ are swapped; ◇/□ are swapped; atoms are dual.

## Implementation

Teams are `Finset W` (with `[DecidableEq W] [Fintype W]`).
Support and anti-support are unified into a single `eval` function
parameterized by a `Bool` polarity. This makes DNE definitional
(`eval M true (.neg (.neg φ)) t` reduces to `eval M true φ t` by
two applications of the negation clause).

`eval` returns `Prop`, with a `Decidable` instance provided for
computational verification via `#guard decide (...)`.
-/

namespace Semantics.BSML

-- ============================================================================
-- §1: Formulas (Definition 1)
-- ============================================================================

/-- BSML formula language (Definition 1 from @cite{aloni-2022}).

    The base language is: p | ¬φ | φ∧ψ | φ∨ψ | ◇φ | NE.
    □ is NOT a primitive — it is defined as an abbreviation:
    □φ := ¬◇¬φ (see `BSMLFormula.nec`). -/
inductive BSMLFormula where
  /-- Atomic proposition -/
  | atom : String → BSMLFormula
  /-- Non-emptiness atom: team is non-empty -/
  | ne : BSMLFormula
  /-- Negation: swap support/anti-support -/
  | neg : BSMLFormula → BSMLFormula
  /-- Conjunction -/
  | conj : BSMLFormula → BSMLFormula → BSMLFormula
  /-- Split disjunction -/
  | disj : BSMLFormula → BSMLFormula → BSMLFormula
  /-- Possibility modal -/
  | poss : BSMLFormula → BSMLFormula
  deriving Repr

/-- □φ := ¬◇¬φ — necessity as an abbreviation, not a primitive.
    The derived support/anti-support conditions are:
    - s ⊨⁺ □φ iff ∀w∈s, R[w] ⊨⁺ φ
    - s ⊨⁻ □φ iff ∀w∈s, ∃ ne t⊆R[w], t ⊨⁻ φ
    These follow from the definitions of ¬, ◇, and ¬ applied to φ. -/
def BSMLFormula.nec (φ : BSMLFormula) : BSMLFormula :=
  .neg (.poss (.neg φ))

/-- A formula is NE-free if it does not contain the NE atom.
    For NE-free formulas, BSML reduces to classical modal logic
    on singleton teams (Fact 15, @cite{aloni-2022}). -/
def BSMLFormula.isNEFree : BSMLFormula → Bool
  | .atom _ => true
  | .ne => false
  | .neg φ => φ.isNEFree
  | .conj φ ψ => φ.isNEFree && ψ.isNEFree
  | .disj φ ψ => φ.isNEFree && ψ.isNEFree
  | .poss φ => φ.isNEFree

/-- A formula is positive if it contains no negation. -/
def BSMLFormula.isPositive : BSMLFormula → Bool
  | .atom _ => true
  | .ne => true
  | .neg _ => false
  | .conj φ ψ => φ.isPositive && ψ.isPositive
  | .disj φ ψ => φ.isPositive && ψ.isPositive
  | .poss φ => φ.isPositive

/-- A formula is atomic (a single propositional variable). -/
def BSMLFormula.isAtom : BSMLFormula → Bool
  | .atom _ => true
  | _ => false

/-- Atoms are NE-free. -/
theorem BSMLFormula.isAtom_implies_isNEFree (φ : BSMLFormula)
    (h : φ.isAtom = true) : φ.isNEFree = true := by
  cases φ <;> simp_all [isAtom, isNEFree]

-- ============================================================================
-- §2: Models
-- ============================================================================

/-- A BSML model: accessibility and valuation over a finite type of worlds
    (Definition 1, @cite{aloni-2022}). The universe of worlds is given by
    `[Fintype W]` — use `Finset.univ` for the full set. -/
structure BSMLModel (W : Type*) [DecidableEq W] [Fintype W] where
  /-- Accessibility: R[w] = worlds accessible from w -/
  access : W → Finset W
  /-- Valuation: which atoms are true at which worlds -/
  val : String → W → Bool

-- ============================================================================
-- §3: Evaluation (Definition 2)
-- ============================================================================

variable {W : Type*} [DecidableEq W] [Fintype W]

/-- Bilateral evaluation with polarity parameter (Definition 2, @cite{aloni-2022}).

    `eval M true φ t` is support (⊨⁺), `eval M false φ t` is anti-support (⊨⁻).
    Negation flips polarity, making DNE definitional:
    `eval M true (.neg (.neg φ)) t` = `eval M true φ t` by computation. -/
def eval (M : BSMLModel W) : Bool → BSMLFormula → Finset W → Prop
  | true,  .atom p,       t => ∀ w ∈ t, M.val p w = true
  | false, .atom p,       t => ∀ w ∈ t, M.val p w = false
  | true,  .ne,           t => t.Nonempty
  | false, .ne,           t => t = ∅
  | true,  .neg ψ,        t => eval M false ψ t
  | false, .neg ψ,        t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,  t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,  t => ∃ t₁ t₂ : Finset W, t₁ ∪ t₂ = t ∧ eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂
  | true,  .disj ψ₁ ψ₂,  t => ∃ t₁ t₂ : Finset W, t₁ ∪ t₂ = t ∧ eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂,  t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,       t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s
  | false, .poss ψ,       t => ∀ w ∈ t, eval M false ψ (M.access w)

/-- Support: positive evaluation. -/
abbrev support (M : BSMLModel W) (φ : BSMLFormula) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : BSMLModel W) (φ : BSMLFormula) (t : Finset W) : Prop :=
  eval M false φ t

-- ============================================================================
-- §4: Double Negation Elimination (Fact 6)
-- ============================================================================

/-- DNE: ¬¬φ has the same support as φ. Definitional with the polarity design. -/
theorem dne_support (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    support M (.neg (.neg φ)) t ↔ support M φ t := Iff.rfl

/-- DNE: ¬¬φ has the same anti-support as φ. -/
theorem dne_antiSupport (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    antiSupport M (.neg (.neg φ)) t ↔ antiSupport M φ t := Iff.rfl

-- ============================================================================
-- §5: Unfolding Lemmas
-- ============================================================================

@[simp] lemma support_neg (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_conj (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_disj (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

/-- Empty team supports all atoms (vacuous truth). -/
lemma empty_supports_atom (M : BSMLModel W) (p : String) :
    support M (.atom p) ∅ := by
  intro w hw; exact absurd hw (by simp)

-- ============================================================================
-- §6: Frame Properties
-- ============================================================================

/-- Indisputable accessibility: all worlds in team see the same accessible worlds.
    Required for wide-scope FC (Fact 5, @cite{aloni-2022}). -/
def BSMLModel.isIndisputable (M : BSMLModel W) (t : Finset W) : Prop :=
  ∀ w₁ ∈ t, ∀ w₂ ∈ t, M.access w₁ = M.access w₂

/-- State-based accessibility: every world in team has the team itself as
    accessible worlds. Strictly stronger than indisputability. -/
def BSMLModel.isStateBased (M : BSMLModel W) (t : Finset W) : Prop :=
  ∀ w ∈ t, M.access w = t

instance (M : BSMLModel W) (t : Finset W) : Decidable (M.isIndisputable t) := by
  unfold BSMLModel.isIndisputable; infer_instance

instance (M : BSMLModel W) (t : Finset W) : Decidable (M.isStateBased t) := by
  unfold BSMLModel.isStateBased; infer_instance

-- ============================================================================
-- §7: Semantic Relations
-- ============================================================================

/-- Semantic consequence: φ ⊨ ψ if every team supporting φ also supports ψ. -/
def consequence (φ ψ : BSMLFormula) : Prop :=
  ∀ (M : BSMLModel W) (t : Finset W), support M φ t → support M ψ t

/-- Semantic equivalence: same support and anti-support conditions. -/
def equivalent (φ ψ : BSMLFormula) : Prop :=
  ∀ (M : BSMLModel W) (t : Finset W),
    (support M φ t ↔ support M ψ t) ∧ (antiSupport M φ t ↔ antiSupport M ψ t)

-- ============================================================================
-- §8: BSML* Consequence (non-empty teams only)
-- ============================================================================

/-- BSML* support: like standard BSML support but ∅ is excluded from all
    intermediate states. The only difference from `eval M true` is in
    disjunction, where both parts of the split must be non-empty.
    (@cite{aloni-2022} §6.3.1). -/
def supportStar (M : BSMLModel W) : BSMLFormula → Finset W → Prop
  | .atom p, t => ∀ w ∈ t, M.val p w = true
  | .ne, t => t.Nonempty
  | .neg _, _ => True
  | .conj φ ψ, t => supportStar M φ t ∧ supportStar M ψ t
  | .disj φ ψ, t => ∃ t₁ t₂ : Finset W,
      t₁ ∪ t₂ = t ∧ t₁.Nonempty ∧ t₂.Nonempty ∧
      supportStar M φ t₁ ∧ supportStar M ψ t₂
  | .poss φ, t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ supportStar M φ s

/-- BSML* consequence: consequence using BSML* support (non-empty intermediate
    states) on non-empty teams. In BSML*, the empty set ∅ is not among the
    possible states (@cite{aloni-2022} §6.3.1). -/
def consequenceStar (φ ψ : BSMLFormula) : Prop :=
  ∀ (M : BSMLModel W) (t : Finset W), t.Nonempty → supportStar M φ t → supportStar M ψ t

-- ============================================================================
-- §9: Decidable Instance
-- ============================================================================

/-- Decidability of `eval` by structural recursion on the formula. -/
def decidableEval (M : BSMLModel W) :
    (pol : Bool) → (φ : BSMLFormula) → (t : Finset W) → Decidable (eval M pol φ t)
  | true,  .atom _, t => by unfold eval; infer_instance
  | false, .atom _, t => by unfold eval; infer_instance
  | true,  .ne,     t => by unfold eval; infer_instance
  | false, .ne,     t => by unfold eval; infer_instance
  | true,  .neg ψ,  t => by unfold eval; exact decidableEval M false ψ t
  | false, .neg ψ,  t => by unfold eval; exact decidableEval M true ψ t
  | true,  .conj ψ₁ ψ₂, t => by
      unfold eval
      exact @instDecidableAnd _ _ (decidableEval M true ψ₁ t) (decidableEval M true ψ₂ t)
  | false, .conj ψ₁ ψ₂, t => by
      unfold eval
      exact @Fintype.decidableExistsFintype (Finset W)
        (fun t₁ => ∃ t₂ : Finset W, t₁ ∪ t₂ = t ∧ eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂)
        (fun t₁ => @Fintype.decidableExistsFintype (Finset W)
          (fun t₂ => t₁ ∪ t₂ = t ∧ eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂)
          (fun t₂ => @instDecidableAnd _ _
            (decEq _ _)
            (@instDecidableAnd _ _
              (decidableEval M false ψ₁ t₁)
              (decidableEval M false ψ₂ t₂)))
          inferInstance)
        inferInstance
  | true,  .disj ψ₁ ψ₂, t => by
      unfold eval
      exact @Fintype.decidableExistsFintype (Finset W)
        (fun t₁ => ∃ t₂ : Finset W, t₁ ∪ t₂ = t ∧ eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂)
        (fun t₁ => @Fintype.decidableExistsFintype (Finset W)
          (fun t₂ => t₁ ∪ t₂ = t ∧ eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂)
          (fun t₂ => @instDecidableAnd _ _
            (decEq _ _)
            (@instDecidableAnd _ _
              (decidableEval M true ψ₁ t₁)
              (decidableEval M true ψ₂ t₂)))
          inferInstance)
        inferInstance
  | false, .disj ψ₁ ψ₂, t => by
      unfold eval
      exact @instDecidableAnd _ _ (decidableEval M false ψ₁ t) (decidableEval M false ψ₂ t)
  | true,  .poss ψ, t => by
      unfold eval
      exact @Finset.decidableDforallFinset _ t
        (fun w _ => ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s)
        (fun w _ => @Fintype.decidableExistsFintype (Finset W)
          (fun s => s ⊆ M.access w ∧ s.Nonempty ∧ eval M true ψ s)
          (fun s => @instDecidableAnd _ _
            inferInstance
            (@instDecidableAnd _ _
              inferInstance
              (decidableEval M true ψ s)))
          inferInstance)
  | false, .poss ψ, t => by
      unfold eval
      exact @Finset.decidableDforallFinset _ t
        (fun w _ => eval M false ψ (M.access w))
        (fun w _ => decidableEval M false ψ (M.access w))

instance instDecidableEval (M : BSMLModel W) (pol : Bool) (φ : BSMLFormula) (t : Finset W) :
    Decidable (eval M pol φ t) := decidableEval M pol φ t

end Semantics.BSML
