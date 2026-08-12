import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Linglib.Logic.Team.Algebra
import Linglib.Logic.Bilateral.Defs
import Linglib.Logic.Modal.Kripke

/-!
# Bilateral state-based modal logic: core definitions

Bilateral state-based modal logic (BSML, [aloni-2022]) evaluates formulas
against **teams** — finite sets of worlds of a Kripke model — with two
polarities: support (`⊨⁺`) and anti-support (`⊨⁻`). Negation swaps the
polarities, so double-negation elimination holds definitionally, and the
non-emptiness atom `NE` (supported exactly by non-empty teams) is the
ingredient from which the free-choice effects derive. Despite being
state-based, BSML is a static logic: formulas are evaluated against teams,
not updated by them ([aloni-2022] p. 22). QBSML ([aloni-vanormondt-2023])
runs the same recursion over quantified atoms.

## Main declarations

* `Formula` — atoms, `NE`, `¬`, `∧`, split `∨`, and `◇`; `□` is the
  abbreviation `Formula.nec` (`□φ := ¬◇¬φ`).
* `eval` — bilateral evaluation, the two polarities unified by a `Bool`
  parameter; `support`/`antiSupport` fix the polarity.
* `Formula.NEFree`, `Formula.Positive` — the `NE`-free and negation-free
  syntactic fragments.
* `ModalLogic.KripkeModel.IsIndisputable`, `ModalLogic.KripkeModel.IsStateBased` —
  the frame conditions governing wide-scope free choice.
* `consequence`, `equivalent` — support consequence and bilateral
  equivalence.
* `evalStar`, `consequenceStar` — BSML*, the variant excluding `∅` from
  the possible states; `supportStar`/`antiSupportStar` fix the polarity.

## Implementation notes

The support and anti-support clauses are dual — `∧`/`∨` swap, `◇`/`□` swap,
atoms flip truth value:

| Connective | Support (⊨⁺) | Anti-support (⊨⁻) |
|-----------|-------------|-------------------|
| p (atom) | ∀w∈s: V(w,p)=1 | ∀w∈s: V(w,p)=0 |
| ¬φ | s ⊨⁻ φ | s ⊨⁺ φ |
| φ ∧ ψ | s ⊨⁺ φ ∧ s ⊨⁺ ψ | ∃t,u: t∪u=s ∧ t ⊨⁻ φ ∧ u ⊨⁻ ψ |
| φ ∨ ψ | ∃t,u: t∪u=s ∧ t ⊨⁺ φ ∧ u ⊨⁺ ψ | s ⊨⁻ φ ∧ s ⊨⁻ ψ |
| ◇φ | ∀w∈s: ∃ ne t⊆R[w]: t ⊨⁺ φ | ∀w∈s: R[w] ⊨⁻ φ |
| □φ | ∀w∈s: R[w] ⊨⁺ φ | ∀w∈s: ∃ ne t⊆R[w]: t ⊨⁻ φ |
| NE | s ≠ ∅ | s = ∅ |

Encoding both polarities in one `eval` makes the duality a single recursion
and double-negation elimination a `rfl`: `eval M true (.neg (.neg φ)) t`
reduces to `eval M true φ t` by two negation clauses. Models are the shared
`ModalLogic.KripkeModel` carrier; teams are `Finset W`; `eval` is `Prop`-valued
with a `Decidable` instance, so concrete claims close by `decide`.
-/

namespace BSML

open ModalLogic (KripkeModel)

/-! ### Formulas -/

/-- BSML formulas over an atom type: `p | NE | ¬φ | φ∧ψ | φ∨ψ | ◇φ`.
    `□` is not primitive — see `Formula.nec`. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition -/
  | atom : Atom → Formula Atom
  /-- Non-emptiness atom: team is non-empty -/
  | ne : Formula Atom
  /-- Negation: swap support/anti-support -/
  | neg : Formula Atom → Formula Atom
  /-- Conjunction -/
  | conj : Formula Atom → Formula Atom → Formula Atom
  /-- Split disjunction -/
  | disj : Formula Atom → Formula Atom → Formula Atom
  /-- Possibility modal -/
  | poss : Formula Atom → Formula Atom
  deriving Repr

variable {Atom : Type*}

/-- Necessity as an abbreviation: `Formula.nec φ = ¬◇¬φ`, giving the derived
    clauses `s ⊨⁺ □φ ↔ ∀ w ∈ s, R[w] ⊨⁺ φ` and
    `s ⊨⁻ □φ ↔ ∀ w ∈ s, ∃ nonempty t ⊆ R[w], t ⊨⁻ φ`. -/
def Formula.nec (φ : Formula Atom) : Formula Atom :=
  .neg (.poss (.neg φ))

/-! ### Syntactic fragments -/

/-- `Formula.NEFree φ` holds when `φ` contains no `NE` atom — the fragment
    on which BSML collapses to classical modal logic on singleton teams
    (`BSML/Bridge.lean`). -/
def Formula.NEFree : Formula Atom → Prop
  | .atom _ => True
  | .ne => False
  | .neg φ => φ.NEFree
  | .conj φ ψ => φ.NEFree ∧ ψ.NEFree
  | .disj φ ψ => φ.NEFree ∧ ψ.NEFree
  | .poss φ => φ.NEFree

instance instDecidableNEFree : (φ : Formula Atom) → Decidable φ.NEFree
  | .atom _ => .isTrue trivial
  | .ne => .isFalse id
  | .neg φ => instDecidableNEFree φ
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidableNEFree φ) (instDecidableNEFree ψ)
  | .disj φ ψ => @instDecidableAnd _ _ (instDecidableNEFree φ) (instDecidableNEFree ψ)
  | .poss φ => instDecidableNEFree φ

/-- `Formula.Positive φ` holds when `φ` contains no negation. -/
def Formula.Positive : Formula Atom → Prop
  | .atom _ => True
  | .ne => True
  | .neg _ => False
  | .conj φ ψ => φ.Positive ∧ ψ.Positive
  | .disj φ ψ => φ.Positive ∧ ψ.Positive
  | .poss φ => φ.Positive

instance instDecidablePositive : (φ : Formula Atom) → Decidable φ.Positive
  | .atom _ => .isTrue trivial
  | .ne => .isTrue trivial
  | .neg _ => .isFalse id
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidablePositive φ) (instDecidablePositive ψ)
  | .disj φ ψ => @instDecidableAnd _ _ (instDecidablePositive φ) (instDecidablePositive ψ)
  | .poss φ => instDecidablePositive φ

/-! ### Bilateral evaluation -/

variable {W : Type*} [DecidableEq W]

/-- Bilateral evaluation with polarity parameter: `eval M true φ t` is
    support (`⊨⁺`), `eval M false φ t` is anti-support (`⊨⁻`), and negation
    flips the polarity. The split clauses (disjunction-support,
    conjunction-anti-support) quantify over `Team.splitsAs` decompositions
    `t₁ ∪ t₂ = t`. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,       t => ∀ w ∈ t, M.val p w = true
  | false, .atom p,       t => ∀ w ∈ t, M.val p w = false
  | true,  .ne,           t => t.Nonempty
  | false, .ne,           t => t = ∅
  | true,  .neg ψ,        t => eval M false ψ t
  | false, .neg ψ,        t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,  t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,  t => ∃ t₁ t₂ : Finset W,
                                Team.splitsAs t t₁ t₂ ∧
                                eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂
  | true,  .disj ψ₁ ψ₂,  t => ∃ t₁ t₂ : Finset W,
                                Team.splitsAs t t₁ t₂ ∧
                                eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂,  t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,       t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s
  | false, .poss ψ,       t => ∀ w ∈ t, eval M false ψ (M.access w)

/-- Support: positive evaluation. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

/-! ### Double-negation elimination -/

/-- `¬¬φ` has the same support as `φ`, definitionally. -/
theorem dne_support (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    support M (.neg (.neg φ)) t ↔ support M φ t := Iff.rfl

/-- `¬¬φ` has the same anti-support as `φ`, definitionally. -/
theorem dne_antiSupport (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg (.neg φ)) t ↔ antiSupport M φ t := Iff.rfl

/-! ### Unfolding lemmas -/

@[simp] lemma support_neg (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

/-- BSML's `support` and `antiSupport` form a paraconsistent bilateral
    logic (`Bilateral.IsBilateral`) under `Formula.neg`. -/
theorem isBilateral (M : KripkeModel W Atom) :
    Bilateral.IsBilateral
      (support M) (antiSupport M) Formula.neg :=
  Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

@[simp] lemma support_conj (M : KripkeModel W Atom)
    (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_disj (M : KripkeModel W Atom)
    (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

/-- The empty team supports every atom, vacuously. -/
lemma empty_supports_atom (M : KripkeModel W Atom) (p : Atom) :
    support M (.atom p) ∅ :=
  fun w hw => absurd hw (Finset.notMem_empty w)

/-! ### Frame conditions -/

/-- Indisputable accessibility: all worlds in the team see the same
    accessible worlds — the frame condition for wide-scope free choice.
    Defined via `Team.IsIndisputable`, sharing substrate with QBSML. -/
def _root_.ModalLogic.KripkeModel.IsIndisputable (M : KripkeModel W Atom) (t : Finset W) : Prop :=
  Team.IsIndisputable M.access t

/-- State-based accessibility: every world in the team has the team itself
    as its accessible worlds. Strictly stronger than indisputability.
    Defined via `Team.IsStateBased`. -/
def _root_.ModalLogic.KripkeModel.IsStateBased (M : KripkeModel W Atom) (t : Finset W) : Prop :=
  Team.IsStateBased M.access t

instance (M : KripkeModel W Atom) (t : Finset W) : Decidable (M.IsIndisputable t) :=
  inferInstanceAs (Decidable (Team.IsIndisputable M.access t))

instance (M : KripkeModel W Atom) (t : Finset W) : Decidable (M.IsStateBased t) :=
  inferInstanceAs (Decidable (Team.IsStateBased M.access t))

/-! ### Consequence and equivalence -/

/-- Semantic consequence: every team supporting `φ` supports `ψ`. -/
def consequence (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (t : Finset W), support M φ t → support M ψ t

/-- Semantic equivalence: same support and anti-support conditions. -/
def equivalent (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (t : Finset W),
    (support M φ t ↔ support M ψ t) ∧ (antiSupport M φ t ↔ antiSupport M ψ t)

/-! ### BSML* -/

/-- Bilateral evaluation for BSML* ([aloni-2022] §6.3.1): like `eval`, but
    `∅` is not among the possible states, so the split clauses
    (disjunction-support, conjunction-anti-support) quantify over
    `Team.splitsAsNE` decompositions into non-empty parts. The exclusion is
    imposed wherever states are quantified — the splits here and the outer
    team in `consequenceStar` — while the atom, `ne`, and modal clauses
    keep their BSML form. -/
def evalStar (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,       t => ∀ w ∈ t, M.val p w = true
  | false, .atom p,       t => ∀ w ∈ t, M.val p w = false
  | true,  .ne,           t => t.Nonempty
  | false, .ne,           t => t = ∅
  | true,  .neg ψ,        t => evalStar M false ψ t
  | false, .neg ψ,        t => evalStar M true ψ t
  | true,  .conj ψ₁ ψ₂,  t => evalStar M true ψ₁ t ∧ evalStar M true ψ₂ t
  | false, .conj ψ₁ ψ₂,  t => ∃ t₁ t₂ : Finset W,
                                Team.splitsAsNE t t₁ t₂ ∧
                                evalStar M false ψ₁ t₁ ∧ evalStar M false ψ₂ t₂
  | true,  .disj ψ₁ ψ₂,  t => ∃ t₁ t₂ : Finset W,
                                Team.splitsAsNE t t₁ t₂ ∧
                                evalStar M true ψ₁ t₁ ∧ evalStar M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂,  t => evalStar M false ψ₁ t ∧ evalStar M false ψ₂ t
  | true,  .poss ψ,       t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ evalStar M true ψ s
  | false, .poss ψ,       t => ∀ w ∈ t, evalStar M false ψ (M.access w)

/-- BSML* support: positive evaluation with non-empty intermediate states. -/
abbrev supportStar (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  evalStar M true φ t

/-- BSML* anti-support. -/
abbrev antiSupportStar (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  evalStar M false φ t

@[simp] lemma supportStar_neg (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    supportStar M (.neg φ) t ↔ antiSupportStar M φ t := Iff.rfl

@[simp] lemma antiSupportStar_neg (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    antiSupportStar M (.neg φ) t ↔ supportStar M φ t := Iff.rfl

/-- BSML* consequence: `supportStar` consequence on non-empty teams — in
    BSML*, `∅` is not among the possible states. -/
def consequenceStar (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (t : Finset W), t.Nonempty → supportStar M φ t → supportStar M ψ t

/-! ### Decidability of evaluation -/

/-- Decidability of `eval` by structural recursion on the formula. -/
def decidableEval (M : KripkeModel W Atom) :
    (pol : Bool) → (φ : Formula Atom) → (t : Finset W) → Decidable (eval M pol φ t)
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
        (fun t₁ => ∃ t₂ : Finset W,
            Team.splitsAs t t₁ t₂ ∧
            eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂)
        (fun t₁ => @Fintype.decidableExistsFintype (Finset W)
          (fun t₂ => Team.splitsAs t t₁ t₂ ∧
                     eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂)
          (fun t₂ => @instDecidableAnd _ _
            inferInstance
            (@instDecidableAnd _ _
              (decidableEval M false ψ₁ t₁)
              (decidableEval M false ψ₂ t₂)))
          inferInstance)
        inferInstance
  | true,  .disj ψ₁ ψ₂, t => by
      unfold eval
      exact @Fintype.decidableExistsFintype (Finset W)
        (fun t₁ => ∃ t₂ : Finset W,
            Team.splitsAs t t₁ t₂ ∧
            eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂)
        (fun t₁ => @Fintype.decidableExistsFintype (Finset W)
          (fun t₂ => Team.splitsAs t t₁ t₂ ∧
                     eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂)
          (fun t₂ => @instDecidableAnd _ _
            inferInstance
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

instance instDecidableEval (M : KripkeModel W Atom) (pol : Bool) (φ : Formula Atom)
    (t : Finset W) : Decidable (eval M pol φ t) := decidableEval M pol φ t

end BSML
