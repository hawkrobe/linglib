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
theme before goal — on a movement generator, and on [siloni-2012]'s
parasitic assignment, recast as a language-specific generator whose
absence from the standard rule set is the sole-role requirement and whose
addition is the *se* marking.
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

/-- The *give* comb satisfies the theta criterion: agent, theme, and goal
    receivers exactly match the head's grid. -/
theorem giveComb_criterion : SatisfiesCriterion giveComb :=
  comb_satisfiesCriterion [] .agent [.theme, .goal]

/-! ### A language-specific generator: parasitic assignment

[siloni-2012]'s syntactic reciprocalization assigns a retained internal
role together with the external role to one argument — parasitic
assignment, a last resort licensed by the *se* morphology. In the coloring
model this is a dual-receiver generator: one argument receives two roles
against a dual-giver residue, as in the ECM derivation where *Jean* ends
with the matrix experiencer role and the embedded verb's retained agent
role. The generator is absent from the standard rule set
(`parasiticGen_notMem` — the model's form of the sole-role requirement),
and adding it, as the *se* marking does, makes the dual-role structure
derivable (`parasiticGen_derivable`). -/

/-- Parasitic assignment as a generator: a dual-receiver argument
    discharges a dual-giver residue in one step. -/
def parasiticGen : Bud.Tree (Color Unit) :=
  gen .nontheta (.free [.down .experiencer, .down .agent])
    (.free (upGrid [.experiencer, .agent]))

/-- The standard theta bud system contains no parasitic generator: every
    generator discharges at most one role per argument. -/
theorem parasiticGen_notMem : parasiticGen ∉ rules (L := Unit) giveHier := by
  rintro ⟨g₀, a, b, hg, hor⟩
  cases hg with
  | close g₀' ρE ha hb =>
    rcases hor with heq | heq <;>
      simp only [parasiticGen, gen, Bud.Tree.node.injEq,
        Bud.Tree.leaf.injEq] at heq <;>
      obtain ⟨-, h2, h3⟩ := heq
    · subst h2
      simp at ha
    · subst h3
      simp [upGrid, PolarizedRole.up, PolarizedRole.down] at ha
  | discharge g ρ hg' hchain ha hb =>
    rcases hor with heq | heq <;>
      simp only [parasiticGen, gen, Bud.Tree.node.injEq,
        Bud.Tree.leaf.injEq] at heq <;>
      obtain ⟨-, h2, h3⟩ := heq
    · subst h2
      simp at ha
    · subst h3
      simp [upGrid, PolarizedRole.up, PolarizedRole.down] at ha
  | adjunct g₀' =>
    rcases hor with heq | heq <;>
      simp only [parasiticGen, gen, Bud.Tree.node.injEq,
        Bud.Tree.leaf.injEq] at heq <;>
      obtain ⟨-, h2, h3⟩ := heq
    · simp [Color.nontheta, upGrid] at h3
    · simp [Color.nontheta] at h2
  | move c' hc' =>
    rcases hor with heq | heq <;>
      simp only [parasiticGen, gen, Bud.Tree.node.injEq,
        Bud.Tree.leaf.injEq] at heq <;>
      obtain ⟨-, h2, h3⟩ := heq
    · simp at h3
    · simp at h2

/-- The system extended by the parasitic generator: the *se*-marked
    grammar. -/
def seSystem : Bud.System (Color Unit) :=
  ⟨insert parasiticGen (rules giveHier), {c | c.IsTerminal}⟩

/-- With the marking, the dual-role discharge is derivable: *Jean* ends
    with both the matrix experiencer role and the retained embedded
    agent role. -/
theorem parasiticGen_derivable :
    seSystem.Derives Color.nontheta parasiticGen := by
  have hunit : seSystem.Derives Color.nontheta (.leaf .nontheta) :=
    .unit (by simp [seSystem, Color.IsTerminal])
  simpa using hunit.graft 0 (Set.mem_insert ..)
    (by simp [parasiticGen, gen])

end MarcolliLarson2025
