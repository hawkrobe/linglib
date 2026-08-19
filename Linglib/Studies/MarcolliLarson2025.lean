import Linglib.Syntax.Minimalist.Theta.Basic

/-!
# Marcolli & Larson (2025): Theta theory, operads, and coloring

[marcolli-larson-2025] gives the explicit generating set of the colored
operad that implements theta theory in mathematical Minimalism
([marcolli-chomsky-berwick-2025] §3.8): theta-role assignment is a
coloring algorithm on structures freely formed by Merge, and filtering by
the coloring rules is equivalent to structure formation by a colored
Merge. The generating system, its local conservation law, the derived
External/Internal Merge dichotomy, and the derivability of the bare theta
combs live in `Syntax/Minimalist/Theta/Basic.lean`; this file runs them on
the paper's ditransitive example — *Brian gave the book to Mary*, whose
verb assigns the grid (agent, theme, goal) with the internal hierarchy
theme before goal — and on a movement generator.
-/

namespace MarcolliLarson2025

open Minimalist.Theta

/-- The example's internal theta hierarchy: theme outranks goal, per the
    ditransitive grid the paper builds for *give*. -/
def giveHier : ThetaRole → ThetaRole → Prop :=
  fun a b => a = .theme ∧ b = .goal

/-- The *give* comb: agent, then theme, then goal discharge one node at a
    time; the head leaf carries the full giver grid. Colors only — the
    lexical anchoring of terminal leaves is orthogonal to the theta
    structure. -/
def giveComb : Bud.Tree (Color Unit) :=
  comb [] .agent [.theme, .goal]

/-- The *give* comb is derivable in the complete theta bud system: the
    three-role grid discharges against the theme-before-goal hierarchy. -/
theorem giveComb_derivable :
    (system (L := Unit) giveHier).Derives (.free []) giveComb :=
  comb_derivable [] .agent [.theme, .goal]
    (List.isChain_pair.mpr ⟨rfl, rfl⟩)

/-- Every vertex of the *give* comb is a generator instance: the recursive
    form of the theta criterion, checked structure-wide. -/
theorem giveComb_thetaLocal :
    giveComb.NodeLocal (ThetaLocal (L := Unit) giveHier) :=
  derives_thetaLocal giveComb_derivable

/-- A movement landing site over the residual agent grid. -/
def moveRule : Bud.Tree (Color Unit) :=
  gen .nontheta (.free (upGrid [.agent])) .emptyTree

theorem moveRule_mem : moveRule ∈ rules (L := Unit) giveHier :=
  ⟨[], _, _, .move _ (by simp), .inl rfl⟩

/-- Movement lands only in non-theta positions, at the example rule:
    the empty-tree input forces the non-theta output. -/
theorem moveRule_out_nontheta : moveRule.out = Color.nontheta :=
  rules_emptyTree_out moveRule_mem (by simp [moveRule, gen])

end MarcolliLarson2025
