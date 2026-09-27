module

public import Linglib.Logic.Team.BSML.Defs
public import Linglib.Logic.Modal.Defs

/-!
# The classical fragment of BSML

The `NE`-free fragment of BSML, Aloni's BSML∅, behaves like classical modal logic
([aloni-2022]). This file defines classical (single-world) Kripke truth of a BSML
formula, `Realize`, with the modal clause taken from the shared `ModalLogic.diamond`,
and proves that on `NE`-free formulas team support is pointwise classical truth
([anttila-2021] Proposition 2.2.16, both polarities). Consequence and equivalence
then coincide with their classical definitions: this is [aloni-2022]'s Fact 15 and
[anttila-2021]'s Fact 2.2.17.

## Main declarations

* `Realize M φ w` — classical truth of `φ` at the world `w` of `M`: split disjunction
  is pointwise, `◇` is `ModalLogic.diamond` over `M.Accessible`, and `NE` is true.
* `eval_iff_forall_realize`, `support_iff_forall_realize`,
  `antiSupport_iff_forall_not_realize` — Proposition 2.2.16: an `NE`-free formula is
  supported by a team iff it is true at each of its worlds, and anti-supported iff false
  at each.
* `support_singleton_iff_realize` — its singleton case: `{w} ⊨⁺ φ ↔ M, w ⊨ φ`.
* `classicalConsequence`, `consequence_iff_classicalConsequence` — Fact 15: on `NE`-free
  formulas, BSML consequence is classical modal consequence.
* `equivalent_iff_classicalConsequence` — Fact 2.2.17: bilateral equivalence of `NE`-free
  formulas is mutual classical consequence.

## Implementation notes

`Realize` is total: `NE` is true at every world, since singletons are non-empty, so the
equations of Proposition 2.2.16 are stated for `NE`-free formulas only, as in the sources.
The proposition is one induction over the polarity parameter of `eval`, with the split
clauses discharged by `Team.exists_splitsAs_forall_iff` and the `◇`-support clause by
`Team.exists_nonempty_subset_forall_iff`. Flatness of the `NE`-free fragment is also
derived from its closure properties in `Properties.lean` (`isFlat_support_of_neFree`).

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal
  Logics
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)
open scoped ModalLogic

variable {W : Type*} {Atom : Type*}

/-! ### Classical truth -/

/-- Classical Kripke truth of a BSML formula at a single world: split disjunction is
    pointwise, `◇` is `ModalLogic.diamond` over `M.Accessible`, and `NE` is true. -/
def Realize (M : KripkeModel W Atom) : Formula Atom → W → Prop
  | .atom p, w => M.val p w = true
  | .ne, _ => True
  | .neg ψ, w => ¬ Realize M ψ w
  | .conj ψ₁ ψ₂, w => Realize M ψ₁ w ∧ Realize M ψ₂ w
  | .disj ψ₁ ψ₂, w => Realize M ψ₁ w ∨ Realize M ψ₂ w
  | .poss ψ, w => ◇[M.Accessible] (Realize M ψ) w

instance instDecidableRealize (M : KripkeModel W Atom) :
    (φ : Formula Atom) → (w : W) → Decidable (Realize M φ w)
  | .atom _, _ => inferInstanceAs (Decidable (_ = true))
  | .ne, _ => .isTrue trivial
  | .neg ψ, w => @instDecidableNot _ (instDecidableRealize M ψ w)
  | .conj ψ₁ ψ₂, w =>
    @instDecidableAnd _ _ (instDecidableRealize M ψ₁ w) (instDecidableRealize M ψ₂ w)
  | .disj ψ₁ ψ₂, w =>
    @instDecidableOr _ _ (instDecidableRealize M ψ₁ w) (instDecidableRealize M ψ₂ w)
  | .poss ψ, w =>
    @Finset.decidableExistsAndFinset _ (M.access w) _ (fun v ↦ instDecidableRealize M ψ v)

variable {M : KripkeModel W Atom} {φ ψ ψ₁ ψ₂ : Formula Atom} {w : W}

@[simp] theorem realize_atom {p : Atom} : Realize M (.atom p) w ↔ M.val p w = true := Iff.rfl

@[simp] theorem realize_ne : Realize M .ne w := trivial

@[simp] theorem realize_neg : Realize M (.neg ψ) w ↔ ¬ Realize M ψ w := Iff.rfl

@[simp] theorem realize_conj :
    Realize M (.conj ψ₁ ψ₂) w ↔ Realize M ψ₁ w ∧ Realize M ψ₂ w := Iff.rfl

@[simp] theorem realize_disj :
    Realize M (.disj ψ₁ ψ₂) w ↔ Realize M ψ₁ w ∨ Realize M ψ₂ w := Iff.rfl

/-- The `◇` clause is `ModalLogic.diamond` over `M.Accessible`, definitionally. -/
theorem realize_poss : Realize M (.poss ψ) w ↔ ∃ v ∈ M.access w, Realize M ψ v := Iff.rfl

theorem realize_nec : Realize M ψ.nec w ↔ □[M.Accessible] (Realize M ψ) w := by
  simp [Formula.nec, Realize]

/-! ### Support is pointwise truth (Proposition 2.2.16) -/

variable [DecidableEq W] {t : Finset W}

/-- [anttila-2021] Proposition 2.2.16, both polarities at once: an `NE`-free formula is
    supported by `t` iff it is true at every world of `t`, and anti-supported iff it is
    false at every world of `t`. -/
theorem eval_iff_forall_realize (hNE : φ.NEFree) (b : Bool) (t : Finset W) :
    eval M b φ t ↔ ∀ w ∈ t, (Realize M φ w ↔ b) := by
  induction φ generalizing b t with
  | atom p => cases b <;> simp [eval, Realize]
  | ne => exact hNE.elim
  | neg ψ ih =>
    cases b
    · simpa [eval, Realize] using ih hNE true t
    · simpa [eval, Realize] using ih hNE false t
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [eval, Team.mem_tensor, Set.mem_ofPred_eq, ih₁ hNE.1, ih₂ hNE.2,
        Team.exists_splitsAs_forall_iff, Realize]
      simp [imp_iff_not_or]
    · simp [eval, ih₁ hNE.1, ih₂ hNE.2, Realize, forall_and]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp [eval, ih₁ hNE.1, ih₂ hNE.2, Realize, forall_and, not_or]
    · simp only [eval, Team.mem_tensor, Set.mem_ofPred_eq, ih₁ hNE.1, ih₂ hNE.2,
        Team.exists_splitsAs_forall_iff, Realize]
      simp
  | poss ψ ih =>
    cases b
    · simp [eval, ih hNE, realize_poss]
    · simp [eval, ih hNE, Team.exists_nonempty_subset_forall_iff, realize_poss]

theorem support_iff_forall_realize (hNE : φ.NEFree) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w := by
  simpa using eval_iff_forall_realize hNE true t

theorem antiSupport_iff_forall_not_realize (hNE : φ.NEFree) :
    antiSupport M φ t ↔ ∀ w ∈ t, ¬ Realize M φ w := by
  simpa using eval_iff_forall_realize hNE false t

/-- The singleton case of Proposition 2.2.16: `{w} ⊨⁺ φ ↔ M, w ⊨ φ`. -/
theorem support_singleton_iff_realize (hNE : φ.NEFree) :
    support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hNE]

theorem antiSupport_singleton_iff_not_realize (hNE : φ.NEFree) :
    antiSupport M φ {w} ↔ ¬ Realize M φ w := by
  simp [antiSupport_iff_forall_not_realize hNE]

/-! ### Consequence is classical consequence (Fact 15) -/

/-- Classical modal consequence: every world of every model realizing `φ` realizes `ψ`. -/
def classicalConsequence (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (w : W), Realize M φ w → Realize M ψ w

/-- [aloni-2022] Fact 15 ([anttila-2021] Fact 2.2.17): on `NE`-free formulas, BSML
    consequence is classical modal consequence. -/
theorem consequence_iff_classicalConsequence (hφ : φ.NEFree) (hψ : ψ.NEFree) :
    consequence (W := W) φ ψ ↔ classicalConsequence (W := W) φ ψ where
  mp h M w hw :=
    (support_singleton_iff_realize hψ).mp (h M {w} ((support_singleton_iff_realize hφ).mpr hw))
  mpr h M _ ht :=
    (support_iff_forall_realize hψ).mpr fun w hw ↦
      h M w ((support_iff_forall_realize hφ).mp ht w hw)

/-- [anttila-2021] Fact 2.2.17: bilateral equivalence of `NE`-free formulas is mutual
    classical consequence. -/
theorem equivalent_iff_classicalConsequence (hφ : φ.NEFree) (hψ : ψ.NEFree) :
    equivalent (W := W) φ ψ ↔
      classicalConsequence (W := W) φ ψ ∧ classicalConsequence (W := W) ψ φ where
  mp h :=
    ⟨fun M w hw ↦ (support_singleton_iff_realize hψ).mp
        ((h M {w}).1.mp ((support_singleton_iff_realize hφ).mpr hw)),
      fun M w hw ↦ (support_singleton_iff_realize hφ).mp
        ((h M {w}).1.mpr ((support_singleton_iff_realize hψ).mpr hw))⟩
  mpr := fun ⟨h₁, h₂⟩ M _ ↦ by
    rw [support_iff_forall_realize hφ, support_iff_forall_realize hψ,
      antiSupport_iff_forall_not_realize hφ, antiSupport_iff_forall_not_realize hψ]
    exact ⟨forall₂_congr fun w _ ↦ ⟨h₁ M w, h₂ M w⟩,
      forall₂_congr fun w _ ↦ not_congr ⟨h₁ M w, h₂ M w⟩⟩

end BSML
