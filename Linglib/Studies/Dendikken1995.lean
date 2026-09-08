import Linglib.Syntax.Minimalist.Verbal.SmallClause

/-!
# den Dikken (1995): Particles

This file formalizes the analysis of English particle constructions in chapter 2 of
[dendikken-1995]. Particles are independent, ergative, non-lexical prepositions heading a small
clause in the verb's complement, (176), so a complex particle construction such as *make John
out a liar* has the small clause within a small clause of (177), `[VP V [SC1 ec [PP Prt [SC2 NP
Pred]]]]`, and a simplex one such as *look up the information* the structure `[VP V [SC ec [PP
Prt NP]]]`, the "object" generated as the particle's complement, (130c). By the generalization
of [burzio-1986] the ergative particle assigns no Case, so its Case-dependent complement is
licensed in one of two ways, (48) and (57): it raises to the specifier of the particle's small
clause, where the verb governs it, giving the outer order V-NP-Prt, or it stays in situ and
receives the verb's Case through reanalysis of verb and particle, an LF incorporation that
extends the verb's government by the Government Transparency Corollary of [baker-1988], giving
the inner order V-Prt-NP; by Economy exactly one of the two applies, §2.3.3.2. The particle
being non-lexical, it does not L-mark its complement, so SC2 is a barrier unless its head is
categorially non-distinct from the particle, prepositional or the infinitival marker *to*, (59);
reanalysis therefore licenses the inner order in prepositional and infinitival complex
constructions but not in nominal and adjectival ones, (49)–(53), and never with a weak pronoun,
which cannot be Case-marked through a chain, (163), nor with a modified particle, whose bare
modifier cannot be stranded under incorporation, (169). Clause-final placement of the particle
has no derivation at all, §2.3.3.3. The trace of an extracted predicate of SC2 needs a lexical
governor, which only the reanalysed verb-particle complex provides, so the predicate is
extractable exactly when the particle is verb-adjacent, (66) and (67), and never in a nominal
construction, (60); the same holds of its extraposition, (69).

## Implementation notes

The derivational calculus is stated over the Case-licensing strategy and the parameters the
chapter's principles read: the particle's complement, an object or a small clause whose
predicate has one of the substrate's `SCPredCategory`s, with the infinitival marker counted
prepositional, (58); whether the object is a weak pronoun; and whether the particle carries a
bare modifier such as *right*. Word order is the placement of the particle that the strategy
yields. Government, barriers and L-marking enter through the principles (59), (163) and (169)
they motivate rather than through a representation of the trees, which the chapter also leaves
to a neutral label, (44). The arguments for the small-clause constituency of particle and object
from [kayne-1984], (13) and (14), for the ergativity of particles from verb-particle idioms,
§2.4.4, and the Norwegian parallel, §2.3.3.5, are recorded in the data and not formalized.

## References

* [dendikken-1995]
* [baker-1988]
* [burzio-1986]
* [kayne-1984]
* [kayne-1985]
* [johnson-1991]
-/

namespace Dendikken1995

open Minimalist

/-- The particle's complement: the object of a simplex construction, §2.4, or the small clause
SC2 of a complex one, (43), with a predicate of the given category; the infinitival marker
*to* counts as prepositional, (58). -/
inductive Complement
  /-- The object NP of a simplex particle construction. -/
  | np
  /-- The inner small clause of a complex particle construction. -/
  | sc (pred : SCPredCategory)
  deriving DecidableEq

/-- (59a–c): particles are non-lexical prepositions and do not L-mark their complements, so a
small clause complement is a barrier unless its head is categorially non-distinct from the
particle. -/
def Complement.IsBarrier : Complement → Prop
  | .np => False
  | .sc c => c ≠ .P

instance : DecidablePred Complement.IsBarrier := λ k => by
  cases k <;> unfold Complement.IsBarrier <;> infer_instance

/-- The two ways the Case-dependent NP in the particle's complement is licensed, (48) and
(57): raising to the specifier of the particle's small clause, where the verb governs it, or
reanalysis of verb and particle, which transmits the verb's Case to the NP in situ. -/
inductive Strategy
  | raising
  | reanalysis
  deriving DecidableEq

/-- The particle's surface position relative to the NP and the predicate of SC2, the a-, b-
and c-examples of (49)–(53). -/
inductive Placement
  /-- V-Prt-NP(-Pred), the "inner particle" order. -/
  | inner
  /-- V-NP-Prt(-Pred), the "outer particle" order. -/
  | outer
  /-- V-NP-Pred-Prt. -/
  | final
  deriving DecidableEq

/-- The word order a strategy yields: a raised NP precedes the particle and an in-situ one
follows it. No strategy places the particle after the predicate of SC2, §2.3.3.3: small
clauses do not move, heads do not adjoin to maximal projections, and adjoining the predicate
would leave the NP-trace improperly bound. -/
def Strategy.placement : Strategy → Placement
  | .raising => .outer
  | .reanalysis => .inner

section Licensing

variable (k : Complement) (weak modified : Prop)

/-- A strategy licenses the NP. Raising always does. Reanalysis transmits the verb's Case
along the incorporation chain, which requires that the particle's complement not be a barrier,
(59d), that the NP not be a weak pronoun, which must agree directly with an Agr head, (163),
and that the particle carry no bare modifier, which incorporation cannot strand, (169). -/
def Licensed : Strategy → Prop
  | .raising => True
  | .reanalysis => ¬ k.IsBarrier ∧ ¬ weak ∧ ¬ modified

/-- A placement is derivable when a licensed strategy yields it; by Economy the derivation
uses exactly one strategy, §2.3.3.2. -/
def Derivable (p : Placement) : Prop := ∃ s, Licensed k weak modified s ∧ s.placement = p

/-- The outer order is always derivable: the a-examples of (49)–(53), (155a), (161a), (162a)
and (167a). -/
theorem derivable_outer : Derivable k weak modified .outer := ⟨.raising, trivial, rfl⟩

/-- The inner order is derivable iff the complement is no barrier and neither a weak pronoun
nor a modifier blocks reanalysis. -/
theorem derivable_inner_iff :
    Derivable k weak modified .inner ↔ ¬ k.IsBarrier ∧ ¬ weak ∧ ¬ modified :=
  ⟨λ ⟨s, hs, hp⟩ => by cases s <;> simp_all [Strategy.placement, Licensed],
    λ h => ⟨.reanalysis, h, rfl⟩⟩

/-- Clause-final placement is never derivable: the c-examples of (49)–(53). -/
theorem not_derivable_final : ¬ Derivable k weak modified .final :=
  λ ⟨s, _, hp⟩ => by cases s <;> cases hp

end Licensing

/-- (49)–(53): nominal and adjectival complex particle constructions have the outer order
only, prepositional and infinitival ones both, and none the clause-final order. -/
theorem complex_paradigm (c : SCPredCategory) :
    Derivable (.sc c) False False .outer ∧ (Derivable (.sc c) False False .inner ↔ c = .P) ∧
      ¬ Derivable (.sc c) False False .final :=
  ⟨derivable_outer _ _ _, by rw [derivable_inner_iff]; simp [Complement.IsBarrier],
    not_derivable_final _ _ _⟩

/-- (155): a simplex construction has both orders with a full NP, but *look up it* has no
derivation, since a weak pronoun cannot be Case-marked through the reanalysis chain; a
stressed, conjoined or deictic pronoun is not weak and patterns with full NPs, (156). -/
theorem weak_pronoun_outer_only :
    Derivable .np False False .inner ∧ Derivable .np True False .outer ∧
      ¬ Derivable .np True False .inner :=
  ⟨(derivable_inner_iff _ _ _).2 (by simp [Complement.IsBarrier]), derivable_outer _ _ _,
    λ h => ((derivable_inner_iff _ _ _).1 h).2.1 trivial⟩

/-- (161) and (162): the ban on weak pronouns carries over to the inner order of prepositional
and infinitival complex constructions, where it is the same reanalysis that licenses the
in-situ NP. -/
theorem weak_pronoun_complex : ¬ Derivable (.sc .P) True False .inner :=
  λ h => ((derivable_inner_iff _ _ _).1 h).2.1 trivial

/-- (167): *look the information right up* is derivable and *look right up the information*
is not, (169), the modified particle being unable to incorporate. -/
theorem modified_outer_only :
    Derivable .np False True .outer ∧ ¬ Derivable .np False True .inner :=
  ⟨derivable_outer _ _ _, λ h => ((derivable_inner_iff _ _ _).1 h).2.2 trivial⟩

/-! ### Extraction of the predicate of SC2, §2.3.3.4 -/

/-- (66): the trace of an extracted predicate of SC2 is lexically governed, as the ECP
demands, only by the reanalysed verb-particle complex, since the particle itself is not a
lexical governor; subextraction from the predicate is governed by the predicate's own head
and always possible, (61), (63) and (65). -/
def PredicateExtractable : Strategy → Prop
  | .raising => False
  | .reanalysis => True

/-- (60): in a nominal complex particle construction the predicate cannot be extracted
whatever the surface position of the particle, since no licensed derivation reanalyses. -/
theorem not_predicateExtractable_of_isBarrier {k : Complement} (hk : k.IsBarrier)
    {weak modified : Prop} {s : Strategy} (hs : Licensed k weak modified s) :
    ¬ PredicateExtractable s := by
  cases s
  · exact id
  · exact λ _ => hs.1 hk

/-- (67): in a prepositional complex particle construction, verb-adjacent particle placement
is derivable and renders the predicate of SC2 extractable, (62a) and (64a), and clause-final
placement does not, (62b) and (64b); extraposition of the predicate patterns the same way,
(69). -/
theorem predicateExtractable_iff_inner :
    (∃ s, Licensed (.sc .P) False False s ∧ s.placement = .inner ∧ PredicateExtractable s) ∧
      ∀ s, s.placement = .outer → ¬ PredicateExtractable s :=
  ⟨⟨.reanalysis, by simp [Licensed, Complement.IsBarrier], rfl, trivial⟩,
    λ s hs => by cases s <;> simp_all [Strategy.placement, PredicateExtractable]⟩

end Dendikken1995
