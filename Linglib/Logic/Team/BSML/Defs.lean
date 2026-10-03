module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Kripke

/-!
# Bilateral state-based modal logic

Aloni's bilateral state-based modal logic (BSML) evaluates formulas against teams, finite sets of
worlds of a Kripke model, in two polarities: support (`⊨⁺`) and anti-support (`⊨⁻`). Negation
swaps the polarities, and the non-emptiness atom `NE`, supported exactly by the non-empty teams,
is the source of the free-choice effects. BSML is static: formulas are evaluated against teams,
not updated by them. QBSML runs the same recursion over quantified atoms.

## Main definitions

* `Formula`: atoms, `NE`, `¬`, `∧`, split `∨` and `◇`; `□` is the abbreviation `Formula.nec`.
* `eval`: bilateral evaluation, with the polarity a `Bool`; `support` and `antiSupport` fix it.
* `Formula.NEFree`, `Formula.Positive`: the `NE`-free and the negation-free fragments.
* `Formula.falsum`, `Formula.strongFalsum`: the weak contradiction `p ∧ ¬p` and the strong
  contradiction `⊥ ∧ NE`.
* `consequence`, `equivalent`: support consequence and bilateral equivalence.
* `evalStar`, `consequenceStar`: BSML*, which excludes `∅` from the possible states.

## Implementation notes

The support and anti-support clauses are dual: `∧` and `∨` swap, `◇` and `□` swap, and atoms flip
their truth value.

| Connective | Support (⊨⁺) | Anti-support (⊨⁻) |
|-----------|-------------|-------------------|
| p (atom) | ∀w∈s: V(w,p)=1 | ∀w∈s: V(w,p)=0 |
| ¬φ | s ⊨⁻ φ | s ⊨⁺ φ |
| φ ∧ ψ | s ⊨⁺ φ ∧ s ⊨⁺ ψ | ∃t,u: t∪u=s ∧ t ⊨⁻ φ ∧ u ⊨⁻ ψ |
| φ ∨ ψ | ∃t,u: t∪u=s ∧ t ⊨⁺ φ ∧ u ⊨⁺ ψ | s ⊨⁻ φ ∧ s ⊨⁻ ψ |
| ◇φ | ∀w∈s: ∃ ne t⊆R[w]: t ⊨⁺ φ | ∀w∈s: R[w] ⊨⁻ φ |
| □φ | ∀w∈s: R[w] ⊨⁺ φ | ∀w∈s: ∃ ne t⊆R[w]: t ⊨⁻ φ |
| NE | s ≠ ∅ | s = ∅ |

Each clause applies an operation of `Team/Operations.lean` to the support sets of the
subformulas, so the closure properties of `Properties.lean` are folds over the per-connective
lemmas there. One `eval` for both polarities makes double-negation elimination `rfl`. `eval` is
`Prop`-valued with a `Decidable` instance, so concrete claims close by `decide`.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [aloni-vanormondt-2023] Aloni and van Ormondt, Modified Numerals and Split Disjunction: The
  First-Order Case
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

/-! ### Formulas -/

/-- The formulas of BSML over an atom type are built from atoms and `NE` by `¬`, `∧`, split `∨`
    and `◇`; `□` is the abbreviation `Formula.nec`. -/
inductive Formula (Atom : Type*) where
  /-- An atomic proposition. -/
  | atom : Atom → Formula Atom
  /-- The non-emptiness atom, supported by the non-empty teams. -/
  | ne : Formula Atom
  /-- Negation, which swaps support and anti-support. -/
  | neg : Formula Atom → Formula Atom
  /-- Conjunction. -/
  | conj : Formula Atom → Formula Atom → Formula Atom
  /-- Split disjunction. -/
  | disj : Formula Atom → Formula Atom → Formula Atom
  /-- The possibility modality. -/
  | poss : Formula Atom → Formula Atom
  deriving Repr

variable {Atom : Type*}

/-- Necessity `□φ` abbreviates `¬◇¬φ`. A team supports it when the successors of each of its
    worlds support `φ`, and anti-supports it when each world has a non-empty set of successors
    anti-supporting `φ`. -/
def Formula.nec (φ : Formula Atom) : Formula Atom :=
  .neg (.poss (.neg φ))

/-! ### Syntactic fragments -/

/-- `Formula.NEFree φ` holds when `φ` contains no `NE` atom — the fragment
    on which BSML collapses to classical modal logic on singleton teams
    (`BSML/Classical.lean`). -/
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

/-! ### Contradictions -/

/-- The weak contradiction `⊥ := p ∧ ¬p` for a fixed atom `p`, the default one
    ([aloni-2022]; [aloni-anttila-yang-2024] take `⊥` as primitive instead). -/
def Formula.falsum [Inhabited Atom] : Formula Atom :=
  .conj (.atom default) (.neg (.atom default))

/-- The strong contradiction `⊥⊥ := ⊥ ∧ NE` ([aloni-anttila-yang-2024]). -/
def Formula.strongFalsum [Inhabited Atom] : Formula Atom :=
  .conj .falsum .ne

@[simp] theorem Formula.neFree_falsum [Inhabited Atom] : (Formula.falsum : Formula Atom).NEFree :=
  ⟨trivial, trivial⟩

/-! ### Bilateral evaluation -/

variable {W : Type*} [DecidableEq W]

/-- Bilateral evaluation `eval M b φ t` is support (`⊨⁺`) when `b` is `true` and anti-support
    (`⊨⁻`) when `b` is `false`. Negation flips the polarity, and the split clauses, support of
    `∨` and anti-support of `∧`, are `Team.tensor`. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,       t => t ∈ Team.flat fun w ↦ M.val p w = true
  | false, .atom p,       t => t ∈ Team.flat fun w ↦ M.val p w = false
  | true,  .ne,           t => t ∈ Team.ne
  | false, .ne,           t => t ∈ ({∅} : Team.TeamProperty W)
  | true,  .neg ψ,        t => eval M false ψ t
  | false, .neg ψ,        t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,  t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,  t => t ∈ Team.tensor {s | eval M false ψ₁ s} {s | eval M false ψ₂ s}
  | true,  .disj ψ₁ ψ₂,  t => t ∈ Team.tensor {s | eval M true ψ₁ s} {s | eval M true ψ₂ s}
  | false, .disj ψ₁ ψ₂,  t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,       t => t ∈ Team.poss M.access {s | eval M true ψ s}
  | false, .poss ψ,       t => t ∈ Team.nec M.access {s | eval M false ψ s}

/-- Support is evaluation in the positive polarity. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support is evaluation in the negative polarity. -/
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

/-- The weak contradiction is supported by the empty team only. -/
@[simp] theorem support_falsum [Inhabited Atom] (M : KripkeModel W Atom) (t : Finset W) :
    support M .falsum t ↔ t = ∅ where
  mp := fun ⟨h₁, h₂⟩ ↦ Finset.eq_empty_iff_forall_notMem.mpr fun w hw ↦ by
    simpa [h₁ w hw] using h₂ w hw
  mpr := by rintro rfl; exact ⟨Team.empty_mem_flat _, Team.empty_mem_flat _⟩

/-- The strong contradiction is supported by no team. -/
theorem not_support_strongFalsum [Inhabited Atom] (M : KripkeModel W Atom) (t : Finset W) :
    ¬ support M .strongFalsum t := fun ⟨h, hne⟩ ↦ hne.ne_empty ((support_falsum M t).mp h)

/-! ### Consequence and equivalence -/

/-- `ψ` is a consequence of `φ` when every team supporting `φ` supports `ψ`. -/
def consequence (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (t : Finset W), support M φ t → support M ψ t

/-- Two formulas are equivalent when they have the same support and anti-support. -/
def equivalent (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (t : Finset W),
    (support M φ t ↔ support M ψ t) ∧ (antiSupport M φ t ↔ antiSupport M ψ t)

/-! ### BSML* -/

/-- Bilateral evaluation for BSML* ([aloni-2022] §6.3.1) differs from `eval` in that `∅` is not
    among the possible states, so each part of a split is intersected with `Team.ne`. The
    exclusion applies wherever states are quantified, in the splits here and on the outer team in
    `consequenceStar`; the atom, `ne` and modal clauses keep their BSML form. -/
def evalStar (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,       t => t ∈ Team.flat fun w ↦ M.val p w = true
  | false, .atom p,       t => t ∈ Team.flat fun w ↦ M.val p w = false
  | true,  .ne,           t => t ∈ Team.ne
  | false, .ne,           t => t ∈ ({∅} : Team.TeamProperty W)
  | true,  .neg ψ,        t => evalStar M false ψ t
  | false, .neg ψ,        t => evalStar M true ψ t
  | true,  .conj ψ₁ ψ₂,  t => evalStar M true ψ₁ t ∧ evalStar M true ψ₂ t
  | false, .conj ψ₁ ψ₂,  t =>
      t ∈ Team.tensor ({s | evalStar M false ψ₁ s} ∩ Team.ne)
        ({s | evalStar M false ψ₂ s} ∩ Team.ne)
  | true,  .disj ψ₁ ψ₂,  t =>
      t ∈ Team.tensor ({s | evalStar M true ψ₁ s} ∩ Team.ne)
        ({s | evalStar M true ψ₂ s} ∩ Team.ne)
  | false, .disj ψ₁ ψ₂,  t => evalStar M false ψ₁ t ∧ evalStar M false ψ₂ t
  | true,  .poss ψ,       t => t ∈ Team.poss M.access {s | evalStar M true ψ s}
  | false, .poss ψ,       t => t ∈ Team.nec M.access {s | evalStar M false ψ s}

/-- BSML* support is `evalStar` in the positive polarity. -/
abbrev supportStar (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  evalStar M true φ t

/-- BSML* anti-support is `evalStar` in the negative polarity. -/
abbrev antiSupportStar (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  evalStar M false φ t

@[simp] lemma supportStar_neg (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    supportStar M (.neg φ) t ↔ antiSupportStar M φ t := Iff.rfl

@[simp] lemma antiSupportStar_neg (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    antiSupportStar M (.neg φ) t ↔ supportStar M φ t := Iff.rfl

/-- In BSML*, `ψ` is a consequence of `φ` when every non-empty team supporting `φ` supports
    `ψ`. -/
def consequenceStar (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (t : Finset W), t.Nonempty → supportStar M φ t → supportStar M ψ t

/-! ### Decidability of evaluation -/

/-- Decidability of `eval` by structural recursion on the formula, through the operators'
    instances. -/
def decidableEval [Fintype W] (M : KripkeModel W Atom) :
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
      exact @Team.tensor.instDecidableMem _ _ _ _ _
        (decidableEval M false ψ₁) (decidableEval M false ψ₂) t
  | true,  .disj ψ₁ ψ₂, t => by
      unfold eval
      exact @Team.tensor.instDecidableMem _ _ _ _ _
        (decidableEval M true ψ₁) (decidableEval M true ψ₂) t
  | false, .disj ψ₁ ψ₂, t => by
      unfold eval
      exact @instDecidableAnd _ _ (decidableEval M false ψ₁ t) (decidableEval M false ψ₂ t)
  | true,  .poss ψ, t => by
      unfold eval
      exact @Team.poss.instDecidableMem _ _ _ _ _ (decidableEval M true ψ) t
  | false, .poss ψ, t => by
      unfold eval
      exact @Team.nec.instDecidableMem _ _ _ (decidableEval M false ψ) t

instance instDecidableEval [Fintype W] (M : KripkeModel W Atom) (pol : Bool) (φ : Formula Atom)
    (t : Finset W) : Decidable (eval M pol φ t) := decidableEval M pol φ t

end BSML
