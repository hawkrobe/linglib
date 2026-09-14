import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Modality.Subjectivity
import Linglib.Data.Examples.Traugott2010

/-!
# Traugott (2010): (Inter)subjectivity and (Inter)subjectification: A Reassessment

This file formalizes the diachronic cline of [traugott-2010]. Subjectivity, an expression's
indexing of the speaker's attitude or viewpoint, and intersubjectivity, its indexing of the
speaker's attention to the addressee's self-image, are synchronic states arranged on the
cline (2), the substrate's `Modality.SubjectivityLevel`. Subjectification and
intersubjectification are the diachronic processes, (3), by which an item acquires newly
coded polysemies at those levels, and the claim is the cline (4): subjectified polysemies of
an item arise later than ideational ones and intersubjectified ones later than subjectified
ones, a coded intersubjective meaning arising by hypothesis from a previously subjectified
one, as the Japanese addressee honorific of (6) arose from a referent honorific. A `History`
lists the levels of an item's coded polysemies in the order they arose, `Unidirectional` is
the cline, and `subjective_mem_of_intersubjective_mem` derives that an item with an
intersubjective polysemy has a subjective one. The heuristic (4′) separates pragmatic
(inter)subjectivity, arising in context, from coded meaning: *a bit of* is used
intersubjectively as a hedge, (19), but codes only the subjective downtoner, so its history
stops at the subjective level. The case studies *a piece of*, *a bit of* and *a shred of* run
from Partitive through Extended Partitive to Degree Modifier, (12)–(25), `Stage`, the Degree
Modifier being the subjectification to scalar meaning, `Stage.level` and
`stages_unidirectional`, and each stage adds expansions of the kind [himmelmann-2004] makes
criterial for grammaticalization, host-class at Stage II and syntactic and semantic-pragmatic
at Stage III, `Expansion.stage`, so that the Degree Modifier alone is grammaticalized by all
three, `isGrammaticalized_iff`. Neither process entails grammaticalization, illocutionary
uses of speech act verbs subjectifying without it, but the two correlate, since
grammaticalization develops markers of speaker attitude.

## Implementation notes

A history records coded meanings only, so pragmatic intersubjectivity in context does not
add a level, and layering, the coexistence of earlier and later polysemies, is why a history
is a list rather than a replacement. The stages are those the three case studies share; *a
bit of* continues to the Adverb Degree Modifier and Adjunct stages, (20)–(21), further
syntactic expansions, while *a piece of* remains mainly a Partitive and *a shred of*, as a
Degree Modifier, is restricted to positively evaluated heads and largely to negative
polarity. The structural correlates of subjectification that the paper surveys, first-person
subjects, transitivity, polarity and peripheral position, are not modelled. The examples are
the rows of `Data.Examples.Traugott2010`.

## References

* [traugott-2010]
* [traugott-dasher-2002]
* [himmelmann-2004]
* [israel-1996]
-/

namespace Traugott2010

open Modality

/-! ### The diachronic cline (section 2) -/

/-- (3): a newly coded polysemy is at least as subjective as the one it arose from and at most
one level more so, a coded intersubjective meaning arising from a subjectified one. -/
def Step (a b : SubjectivityLevel) : Prop := a ≤ b ∧ b.toNat ≤ a.toNat + 1

instance : DecidableRel Step := λ a b => inferInstanceAs (Decidable (a ≤ b ∧ _ ≤ _))

/-- The levels of an item's coded polysemies in the order they arose. -/
abbrev History := List SubjectivityLevel

/-- (4): the cline, each newly coded polysemy arising by a step from the previous one. -/
def Unidirectional (h : History) : Prop := h.IsChain Step

instance : DecidablePred Unidirectional := λ h => inferInstanceAs (Decidable (h.IsChain Step))

/-- An item whose history begins at or below the subjective level and reaches an
intersubjective polysemy has a subjective one: intersubjectification presupposes
subjectification. -/
theorem subjective_mem_of_intersubjective_mem :
    ∀ {a : SubjectivityLevel} {h : History}, Unidirectional (a :: h) → a ≤ .subjective →
      .intersubjective ∈ a :: h → .subjective ∈ a :: h
  | a, [], _, ha, hi => by
    rw [List.mem_singleton] at hi
    exact absurd ha (hi ▸ by decide)
  | a, b :: h, hc, ha, hi => by
    rw [Unidirectional, List.isChain_cons_cons] at hc
    rcases List.mem_cons.1 hi with rfl | hi'
    · exact absurd ha (by decide)
    · cases a with
      | subjective => exact List.mem_cons.2 (Or.inl rfl)
      | intersubjective => exact absurd ha (by decide)
      | nonSubjective =>
        have hb : b ≤ .subjective := by
          cases b <;> first | decide | exact absurd hc.1.2 (by decide)
        exact List.mem_cons_of_mem _ (subjective_mem_of_intersubjective_mem hc.2 hb hi')

/-! ### Partitive to Degree Modifier (section 4) -/

/-- The stages the three case studies share: the Partitive, the Extended Partitive with
non-food and abstract complements, and the Degree Modifier. -/
inductive Stage where
  | partitive
  | extendedPartitive
  | degreeModifier
  deriving DecidableEq, Fintype, Repr

/-- Order of the stages. -/
def Stage.rank : Stage → ℕ
  | .partitive => 0
  | .extendedPartitive => 1
  | .degreeModifier => 2

instance : LinearOrder Stage := LinearOrder.lift' Stage.rank (by decide)

/-- The coded level at each stage: the Extended Partitive's implication that the unit is small
is an invited inference, and the Degree Modifier's scalar meaning is its semanticization, the
subjectification. -/
def Stage.level : Stage → SubjectivityLevel
  | .partitive => .nonSubjective
  | .extendedPartitive => .nonSubjective
  | .degreeModifier => .subjective

/-- The stages' coded levels follow the cline. -/
theorem stages_unidirectional :
    Unidirectional ([.partitive, .extendedPartitive, .degreeModifier].map Stage.level) := by
  decide

/-- The three expansions of [himmelmann-2004]. -/
inductive Expansion where
  | hostClass
  | syntactic
  | semanticPragmatic
  deriving DecidableEq, Fintype, Repr

/-- The stage at which each expansion first occurs: the complement generalizes at Stage II,
and at Stage III the string gains a second syntactic analysis and its first noun is bleached
of partitive meaning and enriched as a quantifier. -/
def Expansion.stage : Expansion → Stage
  | .hostClass => .extendedPartitive
  | .syntactic => .degreeModifier
  | .semanticPragmatic => .degreeModifier

/-- A stage is grammaticalized, by [himmelmann-2004]'s criteria, once every expansion has
occurred. -/
def Stage.IsGrammaticalized (s : Stage) : Prop := ∀ e : Expansion, e.stage ≤ s

instance (s : Stage) : Decidable s.IsGrammaticalized := inferInstanceAs (Decidable (∀ _, _))

/-- The Degree Modifier is the grammaticalized stage. -/
theorem isGrammaticalized_iff {s : Stage} : s.IsGrammaticalized ↔ s = .degreeModifier := by
  cases s <;> decide

end Traugott2010
