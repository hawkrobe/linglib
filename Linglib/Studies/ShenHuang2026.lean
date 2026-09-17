import Linglib.Semantics.Reference.Definiteness
import Linglib.Fragments.English.Predicates
import Linglib.Syntax.Minimalist.Linearization.Cyclic
import Linglib.Syntax.Minimalist.Phase.Domain
import Linglib.Data.Examples.ShenHuang2026
import Mathlib.Data.Finset.Card

/-!
# Shen and Huang (2026): The Role of Phases and Specificity in Definite Islands

This file formalizes [shen-huang-2026]'s two-constraint theory of the definite island effect,
the degradation of a wh-dependency into a definite depiction nominal. The Phase Impenetrability
Condition (4) freezes the wh-phrase in the complement of a definite determiner ((5),
`impenetrable`) unless a verb of creation has incorporated the determiner and collapsed the
phase, after [davies-dubinsky-2003] and [boskovic-2015]; the Specificity Condition (13) forbids
binding a variable inside a specific DP from outside, whether by a moved wh-phrase or by a
question operator ([fiengo-1987], [huang-1982b], [li-1992]). Constraint stacking (§4.1) counts
the constraints of an account that a configuration violates (`violations`); of the accounts
built from the two constraints, only their combination predicts the observed pattern, a definite
island in both English and Mandarin with a verb-of-creation effect for movement alone
(`observed_iff`). Binding escapes the PIC because it adds no ordering statement under cyclic
linearization (§4.2, `binding_consistent`).

## Implementation notes

* The experiments' effect sizes stay out of the formalization: the theory predicts the presence
  and direction of the contrasts, not their magnitude, which the paper notes differs across the
  two languages.
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

open Reference Minimalist Minimalist.Linearization ArgumentStructure Data.Examples

/-- How a wh-dependency is established: overt movement of the wh-phrase, which binds its
trace, or unselective binding of an in-situ wh-phrase by an operator, a question operator or
existential closure, after [li-1992]. -/
inductive Dependency
  | movement | binding
  deriving DecidableEq, Repr, Fintype

/-- A cell of the factorial design (20), (21): the dependency, the definiteness of the object
DP the wh-element sits in, the demonstrative being specific, and whether the main verb is a verb
of creation. -/
structure Config where
  dependency : Dependency
  object : Definiteness
  creation : Bool
  deriving DecidableEq, Repr

/-! ### The object DP (5) -/

/-- The wh-phrase, the complement of *about*. -/
def wh : LIToken := ⟨.simple .D [] "what" true, 0⟩

/-- The preposition of the depiction nominal. -/
def about : LIToken := ⟨.simple .P [.D] "about", 1⟩

/-- The head noun, selecting the depiction PP. -/
def book : LIToken := ⟨.simple .N [.P] "book", 2⟩

/-- The demonstrative determiner of a definite object. -/
def that : LIToken := ⟨.simple .D [.N] "that", 3⟩

/-- The indefinite determiner. -/
def a : LIToken := ⟨.simple .D [.N] "a", 4⟩

/-- The main verb. -/
def verb : LIToken := ⟨.simple .V [.D], 5⟩

/-- The determiner of the object: the demonstrative when it is definite. -/
def determiner : Definiteness → LIToken
  | .definite => that
  | .indefinite => a

/-- The object DP of (25): the wh-phrase in the complement of the determiner. -/
def dp (o : Definiteness) : PlanarSyntacticObject := determiner o * (book * (about * wh))

/-- The verb phrase of (25). -/
def vp (o : Definiteness) : PlanarSyntacticObject := verb * dp o

/-- (5): the wh-phrase lies in the domain of the determiner, so the PIC (4) freezes it in any
phase the determiner heads. -/
theorem impenetrable (o : Definiteness) :
    (vp o : SyntacticObject).Impenetrable (determiner o) wh := by
  cases o <;> decide

/-- The escape hatch the account denies (§2.1): the verb phrase with the wh-phrase moved to
Spec,DP. -/
def vpEdge : PlanarSyntacticObject := verb * (wh * (that * (book * (about * .traceOf wh))))

/-- At the edge of the phase, the wh-phrase would be outside the reach of the PIC. -/
theorem edge_not_impenetrable : ¬ (vpEdge : SyntacticObject).Impenetrable that wh := by
  decide

/-! ### The two constraints -/

/-- The DP phasehood account (§2.1): the demonstrative heads a phase, which a verb of creation
collapses by incorporating it. -/
def Config.phaseHead (c : Config) : Option LIToken :=
  if c.object = .definite ∧ c.creation = false then some that else none

/-- The DP that is specific, in [fiengo-1987]'s sense of familiar: the demonstrative-marked one. -/
def Config.specific (c : Config) : Option SyntacticObject :=
  if c.object = .definite then some (dp c.object) else none

/-- The two constraints. -/
inductive Constraint
  | pic | specificity
  deriving DecidableEq, Repr, Fintype

/-- The Phase Impenetrability Condition (4) is violated when movement extracts the wh-phrase
from the interior of a phase; the Specificity Condition (13) when a variable inside a specific
DP is bound from outside, whatever the binder. -/
def Constraint.Violated : Constraint → Config → Prop
  | .pic, c => c.dependency = .movement ∧
      ∃ ℓ ∈ c.phaseHead, (vp c.object : SyntacticObject).Impenetrable ℓ wh
  | .specificity, c => ∃ d ∈ c.specific, d.contains wh

instance (k : Constraint) : DecidablePred k.Violated := fun _ ↦ by
  cases k <;> unfold Constraint.Violated <;> infer_instance

/-- Movement out of a definite object under a verb that is not a verb of creation, and nothing
else, violates the PIC. -/
theorem pic_violated_iff (c : Config) :
    Constraint.Violated .pic c ↔
      c.dependency = .movement ∧ c.object = .definite ∧ c.creation = false := by
  obtain ⟨d, o, v⟩ := c
  cases d <;> cases o <;> cases v <;> decide

/-- A definite object, and nothing else, violates the Specificity Condition. -/
theorem specificity_violated_iff (c : Config) :
    Constraint.Violated .specificity c ↔ c.object = .definite := by
  obtain ⟨d, o, v⟩ := c
  cases d <;> cases o <;> cases v <;> decide

/-! ### Constraint stacking (§4.1) -/

/-- The number of constraints of an account that a configuration violates, the more the less
acceptable. -/
def violations (account : Finset Constraint) (c : Config) : ℕ :=
  (account.filter (·.Violated c)).card

/-- The DP phasehood account. -/
def phasehood : Finset Constraint := {.pic}

/-- The Specificity Condition account. -/
def specificity : Finset Constraint := {.specificity}

/-- The paper's proposal: both constraints. -/
def combined : Finset Constraint := {.pic, .specificity}

/-- An indefinite object violates nothing under any account: it is neither a phase nor
specific. -/
theorem violations_indefinite (account : Finset Constraint) (d : Dependency) (v : Bool) :
    violations account ⟨d, .indefinite, v⟩ = 0 :=
  Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k _ ↦ by
    cases k <;> cases d <;> cases v <;> decide)

/-- An account predicts a definite island effect for a dependency and a verb class when the
definite object violates more of its constraints than the indefinite one. -/
def IslandEffect (account : Finset Constraint) (d : Dependency) (v : Bool) : Prop :=
  violations account ⟨d, .indefinite, v⟩ < violations account ⟨d, .definite, v⟩

/-- An account predicts a verb-of-creation effect for a dependency when a verb of creation
lowers the count for a definite object; an indefinite one violates nothing either way. -/
def VOCEffect (account : Finset Constraint) (d : Dependency) : Prop :=
  violations account ⟨d, .definite, true⟩ < violations account ⟨d, .definite, false⟩

instance (account : Finset Constraint) (d : Dependency) (v : Bool) :
    Decidable (IslandEffect account d v) := inferInstanceAs (Decidable (_ < _))

instance (account : Finset Constraint) (d : Dependency) : Decidable (VOCEffect account d) :=
  inferInstanceAs (Decidable (_ < _))

/-- The pattern Experiments 1 and 2 found (Table 2): a definite island for every dependency and
verb class, and a verb-of-creation effect for movement alone. -/
def Observed (account : Finset Constraint) : Prop :=
  (∀ d v, IslandEffect account d v) ∧ VOCEffect account .movement ∧ ¬ VOCEffect account .binding

instance (account : Finset Constraint) : Decidable (Observed account) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- DP phasehood alone (Table 1): an island for movement under a verb that is not a verb of
creation only, hence a verb-of-creation effect, and no island for binding. -/
theorem phasehood_predictions :
    IslandEffect phasehood .movement false ∧ ¬ IslandEffect phasehood .movement true ∧
      VOCEffect phasehood .movement ∧ ∀ v, ¬ IslandEffect phasehood .binding v := by
  decide

/-- The Specificity Condition alone (Table 1): an island for every dependency and verb class,
and no verb-of-creation effect. -/
theorem specificity_predictions :
    (∀ d v, IslandEffect specificity d v) ∧ ∀ d, ¬ VOCEffect specificity d := by
  decide

/-- Of the accounts built from the two constraints, exactly the combination predicts the
observed pattern (Table 2): one constraint is not empirically adequate. -/
theorem observed_iff (account : Finset Constraint) : Observed account ↔ account = combined := by
  revert account
  decide

/-! ### The cited judgments -/

/-- The configuration an example's features record. -/
def Config.ofExample (ex : LinguisticExample) : Option Config := do
  let d ← ex.parse? "dependency" [("movement", Dependency.movement), ("binding", .binding)]
  let o ← ex.parse? "object" [("definite", Definiteness.definite), ("indefinite", .indefinite)]
  let v ← ex.parse? "creation" [("yes", true), ("no", false)]
  pure ⟨d, o, v⟩

/-- Constraint stacking on the paper's cited judgments: within a language, an example violating
strictly more constraints of the combined account is judged no better. -/
theorem stacking : ∀ ex₁ ∈ Examples.all, ∀ ex₂ ∈ Examples.all, ex₁.language = ex₂.language →
    ∀ c₁ ∈ Config.ofExample ex₁, ∀ c₂ ∈ Config.ofExample ex₂,
      violations combined c₁ < violations combined c₂ →
        ex₂.judgment.rank ≤ ex₁.judgment.rank := by
  decide

/-! ### Binding and the PIC under cyclic linearization (§4.2) -/

/-- The terminals of *What do you think Mary would eat?* (27). -/
inductive Terminal
  | what | «do» | you | think | mary | would | eat
  deriving DecidableEq, Repr

open Terminal

/-- (27a): the wh-phrase stops at the edge of the embedded CP, so the order fixed there is
preserved at the matrix Spell-out and the derivation linearizes. -/
theorem edge_stop_consistent :
    Consistent [[what, mary, would, eat], [what, «do», you, think, mary, would, eat]] :=
  consistent_of_forall_sublist (l := [what, «do», you, think, mary, would, eat]) (by decide)
    (by decide)

/-- (27b): the wh-phrase stays in situ when the embedded CP is spelled out, so it follows
*Mary* there and precedes her at the matrix Spell-out, an ordering contradiction: the
cyclic-linearization content of the PIC on movement. -/
theorem phase_skip_inconsistent :
    ¬ Consistent [[mary, would, eat, what], [what, «do», you, think, mary, would, eat]] :=
  not_consistent_of_pair mary what ⟨[mary, would, eat, what], by simp, by decide⟩
    ⟨[what, «do», you, think, mary, would, eat], by simp, by decide⟩

/-- Binding leaves the word order alone: with the wh-phrase in situ at both Spell-outs, no
ordering statement is added and the derivation linearizes, so a dependency established by
binding never meets the contradiction that enforces the PIC on movement. -/
theorem binding_consistent :
    Consistent [[mary, would, eat, what], [«do», you, think, mary, would, eat, what]] :=
  consistent_of_forall_sublist (l := [«do», you, think, mary, would, eat, what]) (by decide)
    (by decide)

/-! ### Verbs of creation in the Fragment -/

/-- A Fragment verb is a verb of creation when its Levin class is a class of creation. -/
def IsVerbOfCreation (v : English.Verb) : Prop := ∃ c ∈ v.levinClasses, c.IsVerbOfCreation

instance : DecidablePred IsVerbOfCreation := fun v ↦
  inferInstanceAs (Decidable (∃ c ∈ v.levinClasses, c.IsVerbOfCreation))

/-- The configuration of an item whose main verb is a Fragment entry. -/
def Config.ofVerb (d : Dependency) (o : Definiteness) (v : English.Verb) : Config :=
  ⟨d, o, decide (IsVerbOfCreation v)⟩

/-- (25): *read that book about* violates both constraints and *write that book about* the
Specificity Condition alone, the residual definite island under a verb of creation. -/
theorem read_write :
    violations combined (Config.ofVerb .movement .definite English.read) = 2 ∧
      violations combined (Config.ofVerb .movement .definite English.write) = 1 := by
  decide

end ShenHuang2026
