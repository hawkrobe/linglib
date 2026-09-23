module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Syntax.Category.Coordinator
public import Linglib.Fragments.English.Coordination
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Hungarian.Coordination
public import Linglib.Fragments.Georgian.Coordination
public import Linglib.Fragments.Latin.Coordination
public import Linglib.Fragments.Korean.Coordination

/-!
# Mitrović and Sauerland (2016): Two Conjunctions Are Better Than One

This file formalizes the universal two-head structure for the conjunction of noun phrases
proposed by [mitrovic-sauerland-2016]. The head μ combines with a predicate and denotes the
subset relation, (12a), and the head J′ intersects two quantifiers, (12b); an individual reaches
μ through the shift to its characteristic property. The subset relation is the generalized
quantifier *every* (`mu_eq_every_sem`), which is why a μ particle on an indeterminate, Japanese
*dare-mo*, is a universal quantifier (`dare_mo_denotes_mu`), and μ of a shifted individual is its
Montague lift (`mu_shift`). The structure J′(μ(↑a))(μ(↑b)) of (13) therefore denotes the meet of
the two lifts (`conjunction_eq`), true of a predicate that holds of each conjunct
(`conjunction_apply`), with no collective reading. Both μ heads are needed: J′ applied to the
shifted individuals directly is contradictory unless the conjuncts are identical
(`shift_inf_shift_eq_bot_iff`).

Languages differ in which heads they pronounce. Coordinators of the J kind, such as English
*and*, have propositional uses and lack additive and quantificational uses; coordinators of the
μ kind, such as Japanese *mo*, combine noun phrases, double, and have them (`mu_has_other_use`,
`j_has_no_other_use`). Some languages pronounce all three heads at once, triadic exponency,
which the paper attests in Southeastern Macedonian, Hungarian, and Avar
(`hasAllThreeStrategies`, `hungarian_triadic`), and every language of the sample has a strategy
pronouncing J alone (`j_is_universal`).

## Implementation notes

Which coordinator of a language is J and which is μ is the paper's classification, recorded in
the language records here; the Fragment entries they point to carry only the descriptive facts
the generalizations are checked against, whether a form is also an additive particle or builds
quantifiers. Georgian, Korean, and Slovenian follow [mitrovic-2021], and Southeastern
Macedonian, Avar, and Serbo-Croatian are not in the sample. The typological table of languages
with distinct nominal and verbal conjunctions is not formalized.

## References

* [mitrovic-sauerland-2016]
* [mitrovic-sauerland-2014]
* [mitrovic-2021]
-/

@[expose] public section

namespace MitrovicSauerland2016

open Quantifier Semantics

/-! ### The two heads, (12) -/

section Semantics

variable {α : Type*}

/-- The head μ denotes the subset relation between two predicates, (12a). -/
def mu (R S : α → Prop) : Prop := R ≤ S

/-- The shift from an individual to its characteristic property, the singleton. -/
def shift (a : α) : α → Prop := (· = a)

/-- The subset relation is the generalized quantifier *every*, so a μ particle on a restrictor
is a universal quantifier, (15). -/
theorem mu_eq_every_sem : (mu : GQ α) = GQ.every_sem := rfl

/-- μ of a shifted individual is its Montague lift. -/
theorem mu_shift (a : α) : mu (shift a) = NP.individual a :=
  funext fun _ ↦ propext ⟨fun h ↦ h a rfl, fun h _ hx ↦ hx ▸ h⟩

/-- The conjunction of two individuals, (13): J′, intersection, of the μ phrases of the shifted
conjuncts is the meet of their Montague lifts. -/
theorem conjunction_eq (a b : α) :
    Coordinator.op .conjunctive (mu (shift a)) (mu (shift b)) =
      NP.individual a ⊓ NP.individual b := by
  rw [mu_shift, mu_shift, Coordinator.op_conjunctive]

/-- The conjunction holds of a predicate that holds of each conjunct, so it has no collective
reading, (14). -/
theorem conjunction_apply (a b : α) (P : α → Prop) :
    Coordinator.op .conjunctive (mu (shift a)) (mu (shift b)) P ↔ P a ∧ P b := by
  rw [conjunction_eq]; rfl

/-- J′ cannot apply to the shifted individuals without μ: the intersection of two singletons is
empty unless the conjuncts are identical. -/
theorem shift_inf_shift_eq_bot_iff {a b : α} : shift a ⊓ shift b = ⊥ ↔ a ≠ b := by
  constructor
  · rintro h rfl
    exact (congrFun h a).mp ⟨rfl, rfl⟩
  · intro h
    funext x
    exact propext ⟨fun ⟨ha, hb⟩ ↦ h (ha.symm.trans hb), False.elim⟩

end Semantics

/-- The universal reading of Japanese *dare-mo* 'everyone' is μ, (1a) and (15). -/
theorem dare_mo_denotes_mu {α : Type} [Fintype α] {d : GQ.Family}
    (h : d ∈ ⟦Japanese.Determiners.dare_mo⟧) : d α = mu := by
  obtain rfl : d = GQ.Family.every := h
  rfl

/-! ### Exponence -/

/-- Which heads of the structure a conjunction strategy pronounces: J alone, *A and B*; the two
μ heads, *A-mo B-mo*; or all three. -/
inductive ConjunctionStrategy where
  | jOnly
  | muOnly
  | jMu
  deriving DecidableEq, Repr

/-- The number of heads a strategy pronounces. -/
def ConjunctionStrategy.overtMorphemeCount : ConjunctionStrategy → ℕ
  | .jOnly => 1
  | .muOnly => 2
  | .jMu => 3

/-- The number of heads in the structure: J and the two μ heads. -/
def ConjunctionStrategy.semanticPieceCount : ℕ := 3

/-- A language's exponents of the two heads, which the paper classifies, and the strategies it
allows. -/
structure ConjunctionSystem where
  language : String
  j : Option Coordinator
  mu : Option Coordinator
  strategies : List ConjunctionStrategy
  deriving Repr

/-- English has only J, *and*. -/
def english : ConjunctionSystem :=
  { language := "English", j := some English.Coordination.and_, mu := none,
    strategies := [.jOnly] }

/-- Japanese *to* is J and *mo* is μ. -/
def japanese : ConjunctionSystem :=
  { language := "Japanese", j := some Japanese.Coordination.to_,
    mu := some Japanese.Coordination.mo, strategies := [.jOnly, .muOnly] }

/-- Hungarian *és* is J and *is* is μ; the language pronounces J and the two μ heads at once,
*Kati is és Mari is*, (28). -/
def hungarian : ConjunctionSystem :=
  { language := "Hungarian", j := some Hungarian.Coordination.es,
    mu := some Hungarian.Coordination.is_, strategies := [.jOnly, .muOnly, .jMu] }

/-- Georgian *da* is J and *-c* is μ; the triadic classification follows [mitrovic-2021]. -/
def georgian : ConjunctionSystem :=
  { language := "Georgian", j := some Georgian.Coordination.da,
    mu := some Georgian.Coordination.c_, strategies := [.jOnly, .muOnly, .jMu] }

/-- Latin *et* is J and the enclitic *-que* is μ, §3.3. -/
def latin : ConjunctionSystem :=
  { language := "Latin", j := some Latin.Coordination.et, mu := some Latin.Coordination.que,
    strategies := [.jOnly, .muOnly] }

/-- Korean *-(i)rang* is J and *-to* is μ, following [mitrovic-2021]. -/
def korean : ConjunctionSystem :=
  { language := "Korean", j := some Korean.Coordination.irang,
    mu := some Korean.Coordination.to_, strategies := [.jOnly, .muOnly] }

/-- Slovenian *in* is J. -/
def slovenian : ConjunctionSystem :=
  { language := "Slovenian",
    j := some { form := "in", gloss := "and", role := .conjunctive, kind := .free },
    mu := none, strategies := [.jOnly] }

/-- The seven-language sample. -/
def msLanguages : List ConjunctionSystem :=
  [english, japanese, hungarian, georgian, latin, korean, slovenian]

/-- Triadic exponency: the J-only, μ-only, and J-with-μ strategies are all attested. -/
def hasAllThreeStrategies (sys : ConjunctionSystem) : Prop :=
  .jOnly ∈ sys.strategies ∧ .muOnly ∈ sys.strategies ∧ .jMu ∈ sys.strategies

instance (sys : ConjunctionSystem) : Decidable (hasAllThreeStrategies sys) := by
  unfold hasAllThreeStrategies; infer_instance

/-- Hungarian realizes all three strategies, *Kati is (és) Mari is*. -/
theorem hungarian_triadic : hasAllThreeStrategies hungarian := by decide

/-- Every μ coordinator of the sample has a use outside conjunction, as an additive particle or
in quantifiers, §3. -/
theorem mu_has_other_use : ∀ sys ∈ msLanguages, ∀ c ∈ sys.mu,
    c.alsoAdditive = true ∨ c.alsoQuantifier = true := by
  decide

/-- No J coordinator of the sample has an additive or a quantificational use, §3. -/
theorem j_has_no_other_use : ∀ sys ∈ msLanguages, ∀ c ∈ sys.j,
    c.alsoAdditive = false ∧ c.alsoQuantifier = false := by
  decide

/-- Every coordinator the paper classifies as J or μ is conjunctive in the Fragments. -/
theorem heads_conjunctive : ∀ sys ∈ msLanguages,
    (∀ c ∈ sys.j, c.role = .conjunctive) ∧ ∀ c ∈ sys.mu, c.role = .conjunctive := by
  decide

/-- Every language in the sample has a J-only strategy. -/
theorem j_is_universal : ∀ sys ∈ msLanguages, .jOnly ∈ sys.strategies := by
  decide

end MitrovicSauerland2016
