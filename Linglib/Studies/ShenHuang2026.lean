import Linglib.Semantics.Definiteness.Defs
import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Syntax.Minimalist.Linearization.Cyclic
import Mathlib.Data.Finset.Card

/-!
# Shen and Huang (2026): The Role of Phases and Specificity in Definite Islands

This file formalizes the paper's two-constraint theory of the definite island effect, the
degradation of a wh-dependency into a definite depiction nominal. A DP phasehood account makes
the definite DP a phase without a landing site at its edge, so overt movement out of it violates
the Phase Impenetrability Condition unless a verb of creation has incorporated the determiner
and collapsed the phase, adapting [davies-dubinsky-2003] after [boskovic-2015]. The Specificity
Condition (13) forbids binding a variable inside a specific DP from outside, specificity being
familiarity after [fiengo-1987], and constrains a moved wh-phrase binding its trace and an
in-situ wh-phrase bound by a question operator alike ([huang-1982b], [li-1992]). The two
accounts diverge (Table 1): phasehood predicts no island under a verb of creation and none for
wh-in-situ, which never moves, while the Specificity Condition predicts an island in both
languages and no verb effect. The parallel acceptability experiments on English and Mandarin
find an island in both languages, a partial neutralization by verbs of creation in English only,
and, in a third experiment, that Chinese wh-indefinites are degraded inside demonstrative DPs.

The proposal (§4.1) keeps both constraints and stacks them (`Constraint.Violated`,
`violations`): the English non-creation case violates both, the creation case and every Chinese
case violate the Specificity Condition alone, and indefinites violate nothing (Table 3,
`violations_movement_definite`, `violations_binding_definite`, `violations_indefinite`). Verb
choice matters exactly for movement out of a definite DP (`voc_effect_iff`), a definite object
always costs the Specificity Condition (`one_le_violations_definite`), and each single-constraint
account misses one of the observed contrasts (`phasehood_predictions`,
`specificity_predictions`). Binding escapes the PIC because, under the cyclic linearization of
[fox-pesetsky-2005], it adds no precedence statement (`binding_no_new_precedences`), whereas
movement that skips a phase edge contradicts the order fixed at Spell-out
(`phase_skip_inconsistent`, `edge_stop_consistent`, the derivations (27)).

## Implementation notes

* Effect sizes stay in prose. Experiments 1 and 2 report difference-in-difference scores of 0.56
  for English non-creation verbs and 0.23 for creation verbs, the latter still above zero, and
  1.15 and 0.97 for Chinese with no significant verb interaction; Experiment 3 reports a
  significant negative interaction of definiteness with the presence of a wh-indefinite. The
  theory predicts the presence and direction of these contrasts, not their magnitude, which the
  paper notes differs across the two languages.
* Incorporation is read off the verb: a verb of creation incorporates the determiner. The
  conditions on incorporation the paper leaves open, and the information-structure and
  LF-movement rivals of §5, are not formalized.

## References

* [shen-huang-2026]
* [davies-dubinsky-2003]
* [boskovic-2015]
* [fiengo-1987]
* [huang-1982b]
* [li-1992]
* [fox-pesetsky-2005]
-/

namespace ShenHuang2026

open Definiteness Minimalist.Linearization ArgumentStructure

/-- How a wh-dependency is established: overt movement of the wh-phrase, which binds its
trace, or unselective binding of an in-situ wh-phrase by an operator, a question operator or
existential closure, after [li-1992]. -/
inductive Dependency
  | movement | binding
  deriving DecidableEq, Repr

/-- A cell of the factorial design (20), (21): the dependency, the definiteness of the object
DP the wh-element sits in, the demonstrative being specific, and whether the main verb is a verb
of creation. -/
structure Config where
  dependency : Dependency
  object : Definiteness
  creation : Bool
  deriving DecidableEq, Repr

/-- The two constraints. -/
inductive Constraint
  | pic | specificity
  deriving DecidableEq, Repr

/-- The Phase Impenetrability Condition is violated when movement leaves a definite DP, a phase
whose edge offers no landing site, unless a verb of creation has incorporated the determiner and
collapsed the phase (§2.1); the Specificity Condition (13) is violated when a variable inside a
specific DP is bound from outside, whatever the binder. -/
def Constraint.Violated : Constraint → Config → Prop
  | .pic, c => c.dependency = .movement ∧ c.object = .definite ∧ c.creation = false
  | .specificity, c => c.object = .definite

instance (k : Constraint) : DecidablePred k.Violated := λ c =>
  match k with
  | .pic =>
    inferInstanceAs
      (Decidable (c.dependency = .movement ∧ c.object = .definite ∧ c.creation = false))
  | .specificity => inferInstanceAs (Decidable (c.object = .definite))

/-- Constraint stacking (§4.1): the number of constraints of an account that a configuration
violates, the more the less acceptable. -/
def violations (account : Finset Constraint) (c : Config) : ℕ :=
  (account.filter (·.Violated c)).card

/-- The DP phasehood account. -/
def phasehood : Finset Constraint := {.pic}

/-- The Specificity Condition account. -/
def specificity : Finset Constraint := {.specificity}

/-- The paper's proposal: both constraints. -/
def combined : Finset Constraint := {.pic, .specificity}

/-- An indefinite object violates nothing under any account: it is neither a phase without a
landing site nor specific. -/
theorem violations_indefinite (account : Finset Constraint) (d : Dependency) (v : Bool) :
    violations account ⟨d, .indefinite, v⟩ = 0 :=
  Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr λ k _ => by
    cases k <;> simp [Constraint.Violated])

/-- Table 3, English: movement out of a definite DP violates both constraints under a
non-creation verb and the Specificity Condition alone under a verb of creation, the residual
definite island effect. -/
theorem violations_movement_definite :
    violations combined ⟨.movement, .definite, false⟩ = 2 ∧
      violations combined ⟨.movement, .definite, true⟩ = 1 := by
  decide

/-- Table 3, Chinese: binding into a definite DP violates the Specificity Condition alone,
whatever the verb. -/
theorem violations_binding_definite (v : Bool) :
    violations combined ⟨.binding, .definite, v⟩ = 1 := by
  cases v <;> decide

/-- Verb choice lowers the count exactly for movement out of a definite DP: the verb-of-creation
effect of English and its absence in Chinese. -/
theorem voc_effect_iff (d : Dependency) (o : Definiteness) :
    violations combined ⟨d, o, true⟩ < violations combined ⟨d, o, false⟩ ↔
      d = .movement ∧ o = .definite := by
  cases d <;> cases o <;> decide

/-- A definite object always costs the Specificity Condition: the definite island effect in both
languages and under both verb classes. -/
theorem one_le_violations_definite (d : Dependency) (v : Bool) :
    1 ≤ violations combined ⟨d, .definite, v⟩ := by
  cases d <;> cases v <;> decide

/-- DP phasehood alone (Table 1): a verb of creation neutralizes the island entirely, and
wh-in-situ is never an island. Experiments 1 and 2 found a residual island under verbs of
creation in English and an island in Chinese. -/
theorem phasehood_predictions (o : Definiteness) (v : Bool) :
    violations phasehood ⟨.movement, .definite, true⟩ = 0 ∧
      violations phasehood ⟨.binding, o, v⟩ = 0 := by
  cases o <;> cases v <;> decide

/-- The Specificity Condition alone (Table 1): no verb effect anywhere. Experiment 1 found one
in English. -/
theorem specificity_predictions (d : Dependency) (o : Definiteness) :
    violations specificity ⟨d, o, true⟩ = violations specificity ⟨d, o, false⟩ := by
  cases d <;> cases o <;> decide

/-! ### Binding and the PIC under cyclic linearization (§4.2) -/

/-- The terminals of *What do you think Mary would eat?* (27). -/
inductive Word
  | what | «do» | you | think | mary | would | eat
  deriving DecidableEq, Repr

open Word in
/-- (27a): the wh-phrase stops at the edge of the embedded CP, so the order fixed there is
preserved at the matrix Spell-out and the derivation linearizes. -/
theorem edge_stop_consistent :
    Consistent [[what, mary, would, eat], [what, «do», you, think, mary, would, eat]] := by
  refine consistent_of_forall_sublist (q := [what, «do», you, think, mary, would, eat])
    (λ p hp => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> decide

open Word in
/-- (27b): the wh-phrase stays in situ when the embedded CP is spelled out, so it follows
*Mary* there and precedes her at the matrix Spell-out, an ordering contradiction: the
cyclic-linearization content of the PIC on movement. -/
theorem phase_skip_inconsistent :
    ¬ Consistent [[mary, would, eat, what], [what, «do», you, think, mary, would, eat]] :=
  not_consistent_of_pair (p := [mary, would, eat, what])
    (q := [what, «do», you, think, mary, would, eat]) (a := mary) (b := what)
    (List.mem_cons_self ..) (by simp) (by decide) (by decide)

/-- Binding adds no precedence statement: an empty Spell-out snapshot leaves the induced order
unchanged, so a dependency established by binding cannot run into the ordering contradiction
that enforces the PIC on movement. -/
theorem binding_no_new_precedences {α : Type*} (phases : List (List α)) :
    spelloutOrder (phases ++ [[]]) = spelloutOrder phases := by
  funext a b
  refine propext ⟨λ h => Relation.TransGen.mono ?_ a b h,
    λ h => Relation.TransGen.mono ?_ a b h⟩ <;>
    rintro x y ⟨p, hp, hs⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact ⟨p, hp, hs⟩
    · rw [List.mem_singleton] at hp
      subst hp
      simp at hs
  · exact ⟨p, List.mem_append_left _ hp, hs⟩

/-- Binding never creates an ordering contradiction. -/
theorem binding_preserves_consistency {α : Type*} (phases : List (List α))
    (h : Consistent phases) : Consistent (phases ++ [[]]) := by
  intro a
  rw [binding_no_new_precedences]
  exact h a

/-! ### Verbs of creation in the Fragment -/

open English.Predicates.Verbal in
/-- The configuration of an experimental item whose main verb is a Fragment entry: a verb of
creation is one whose Levin class is a class of creation. -/
def Config.ofVerb (d : Dependency) (o : Definiteness) (v : VerbEntry) : Config :=
  ⟨d, o, v.levinClass.any LevinClass.isVerbOfCreation⟩

open English.Predicates.Verbal in
/-- The predicted English contrast within a sentence frame (23): subextraction from a definite
object costs one violation more under the non-creation verb than under the creation verb. -/
theorem violations_ofVerb {v u : VerbEntry}
    (hv : v.levinClass.any LevinClass.isVerbOfCreation = true)
    (hu : u.levinClass.any LevinClass.isVerbOfCreation = false) :
    violations combined (Config.ofVerb .movement .definite u) =
      violations combined (Config.ofVerb .movement .definite v) + 1 := by
  simp only [Config.ofVerb, hv, hu]
  decide

end ShenHuang2026
