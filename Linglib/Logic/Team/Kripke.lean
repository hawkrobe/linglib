module

public import Mathlib.Data.Finset.Basic

/-!
# Kripke models

This file defines `KripkeModel`, the finite Kripke carrier — successor
`Finset`s and a `Bool` valuation — that the team-semantic modal logics
(BSML, QBSML, modal dependence and inclusion logic, InqML) evaluate on.
It is the decidable specialization of the relational primitives of
`Logic/Modal/Defs.lean`: `KripkeModel.Accessible` is the successor
function as the `W → W → Prop` relation those primitives take.

The file also states Aloni's two conditions on the accessibility relation relative to a team
([aloni-2022] Definition 5), which distinguish epistemic from deontic modals: indisputability,
that every world of the team sees the same worlds, and state-basedness, that every world of the
team sees exactly the team.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [vaananen-2008] Väänänen, Modal Dependence Logic
-/

@[expose] public section

namespace ModalLogic

/-- A **Kripke model** over worlds `W` and atoms `Atom`. -/
structure KripkeModel (W : Type*) (Atom : Type*) where
  /-- Accessibility: `access w` is the set of worlds accessible from `w`. -/
  access : W → Finset W
  /-- Valuation: `val p w` is the truth value of atom `p` at world `w`. -/
  val : Atom → W → Bool

variable {W : Type*} {Atom : Type*}

/-- The accessibility relation of `M`: `v` is accessible from `w` when `v ∈ M.access w`.
    This is the relation that `box` and `diamond` of `Logic/Modal/Defs.lean` take. -/
def KripkeModel.Accessible (M : KripkeModel W Atom) (w v : W) : Prop :=
  v ∈ M.access w

instance [DecidableEq W] (M : KripkeModel W Atom) : DecidableRel M.Accessible :=
  fun w v ↦ inferInstanceAs (Decidable (v ∈ M.access w))

end ModalLogic

/-! ### Conditions on accessibility relative to a team -/

namespace Team

variable {W : Type*}

/-- `R` is **indisputable** on the team `t` when all worlds of `t` see the same worlds
([aloni-2022] Definition 5). -/
def IsIndisputable (R : W → Finset W) (t : Finset W) : Prop :=
  ∀ w₁ ∈ t, ∀ w₂ ∈ t, R w₁ = R w₂

/-- `R` is **state-based** on the team `t` when every world of `t` sees exactly `t`
([aloni-2022] Definition 5). -/
def IsStateBased (R : W → Finset W) (t : Finset W) : Prop :=
  ∀ w ∈ t, R w = t

theorem IsStateBased.isIndisputable {R : W → Finset W} {t : Finset W}
    (h : IsStateBased R t) : IsIndisputable R t :=
  fun w₁ hw₁ w₂ hw₂ ↦ (h w₁ hw₁).trans (h w₂ hw₂).symm

instance [DecidableEq W] (R : W → Finset W) (t : Finset W) : Decidable (IsIndisputable R t) :=
  inferInstanceAs (Decidable (∀ w₁ ∈ t, ∀ w₂ ∈ t, _))

instance [DecidableEq W] (R : W → Finset W) (t : Finset W) : Decidable (IsStateBased R t) :=
  inferInstanceAs (Decidable (∀ w ∈ t, _))

end Team

namespace ModalLogic

variable {W : Type*} {Atom : Type*}

/-- `M` is indisputable on the team `t`: its accessibility is `Team.IsIndisputable` there. -/
def KripkeModel.IsIndisputable (M : KripkeModel W Atom) (t : Finset W) : Prop :=
  Team.IsIndisputable M.access t

/-- `M` is state-based on the team `t`: its accessibility is `Team.IsStateBased` there. -/
def KripkeModel.IsStateBased (M : KripkeModel W Atom) (t : Finset W) : Prop :=
  Team.IsStateBased M.access t

instance [DecidableEq W] (M : KripkeModel W Atom) (t : Finset W) :
    Decidable (M.IsIndisputable t) :=
  inferInstanceAs (Decidable (Team.IsIndisputable M.access t))

instance [DecidableEq W] (M : KripkeModel W Atom) (t : Finset W) :
    Decidable (M.IsStateBased t) :=
  inferInstanceAs (Decidable (Team.IsStateBased M.access t))

end ModalLogic
