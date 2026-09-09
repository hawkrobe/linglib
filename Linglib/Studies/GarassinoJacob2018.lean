import Linglib.Discourse.QUD.Basic
import Linglib.Semantics.Questions.Exhaustivity
import Linglib.Semantics.Focus.Interpretation
import Linglib.Fragments.Italian.PolarityMarking
import Linglib.Fragments.Spanish.PolarityMarking
import Linglib.Fragments.Romance.French.PolarityMarking
import Linglib.Data.Examples.GarassinoJacob2018

/-!
# Garassino and Jacob (2018): Polarity focus and non-canonical syntax in Italian, French and Spanish

This file formalizes [garassino-jacob-2018]'s account of clitic left dislocation and the *sì che*
~ *sí que* constructions as realizations of polarity focus. Polarity focus is focus whose
background is the whole proposition and whose alternatives are the proposition and its negation,
so a polarity-focus utterance is a congruent answer to a polar question under discussion
(`polarFocus_qaCongruent`). The chapter's corpus passages are read as discourse trees in the
manner of [buring-2003] and [roberts-2012]: a *wh*-question such as *who has been sitting back?*
is pursued through the polar question for each candidate, each answered with a polarity-focus
utterance, and a polar question about a hyperonymous proposition through the polar questions of
its instances. Both strategies are complete: jointly resolving the subquestions resolves the
question (`agentStrategy_isComplete`, `scalarStrategy_isComplete`), the former because the polar
questions of a family are its partition question.

The rows are the chapter's examples with the lexical and syntactic means they use, the kind of
antecedent, the dislocated constituent and, where the chapter says, whether the utterance stands
to its antecedent in situational identity or analogy and whether it answers a subquestion. The
contexts attested for *sì che*, *sí que* and French *si* lie within the environments the
fragments record (`rows_siChe_env`, `rows_siQue_env`, `rows_si_env`), French *si* answering only
a preceding negative turn.

## Implementation notes

* In the Direct Europarl corpus the chapter counts 6 Italian and 4 French polar left dislocations
  against none in Spanish, and 61 Spanish *sí que* against none in Italian, with 36 of the 61
  carrying a left element (26 subjects, 2 objects, 8 adverbials); it draws the complementary
  distribution and Spanish's preference for a transparent assertive particle from these figures
  and offers no quantitative analysis, so the counts stay in prose.
* The chapter endorses [matic-nikolaeva-2018]'s view that dislocation is no structural means of
  polarity focus but makes the reading available in context; the fragments' `polarityReversal`
  classification of the particles is the form-class view that study contests.
* The discourse trees are stated for finitely many worlds, which is what the substrate's strategy
  completeness needs to pass from lattice entailment to alternative entailment.

## References

* [garassino-jacob-2018]
* [dimroth-sudhoff-2018]
* [matic-nikolaeva-2018]
* [buring-2003]
* [roberts-2012]
* [hohle-1992]
* [batllori-hernanz-2013]
* [poletto-zanuttini-2013]
-/

namespace GarassinoJacob2018

open Question Questions Discourse Data.Examples

variable {W F : Type*}

/-! ### Polarity focus as a polar question under discussion -/

/-- The focus value of a polarity-focus utterance: the proposition and its negation. -/
def polarFocus (p : Set W) : Focus.Interpretation.PropFocusValue W := {p, pᶜ}

/-- The polar question of a proposition is the join of the proposition and its negation. -/
theorem query_ofSet_eq_iSup (p : Set W) :
    (ofSet p).query = ⨆ b : Bool, ofSet (bif b then p else pᶜ) := by
  apply Question.ext
  intro σ
  rw [mem_iSup_ofSet, mem_query, mem_ofSet, info_ofSet]
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨true, h⟩
    · exact Or.inr ⟨false, h⟩
  · rintro (rfl | ⟨b, hb⟩)
    · exact Or.inl (Set.empty_subset _)
    · cases b
      · exact Or.inr hb
      · exact Or.inl hb

theorem alt_query_ofSet {p : Set W} (hp : p.Nonempty) (hpc : pᶜ.Nonempty) :
    alt (ofSet p).query = {p, pᶜ} := by
  rw [query_ofSet_eq_iSup, alt_iSup_ofSet (λ b => by cases b <;> assumption)
    (λ i j h => by
      cases i <;> cases j
      · rfl
      · exact absurd (h hpc.some_mem) hpc.some_mem
      · exact absurd hp.some_mem (h hp.some_mem)
      · rfl)]
  ext q
  simp only [Set.mem_range, Bool.exists_bool, Bool.cond_false, Bool.cond_true, Set.mem_insert_iff,
    Set.mem_singleton_iff, eq_comm, or_comm]

/-- A polarity-focus utterance is a congruent answer to the polar question of its proposition. -/
theorem polarFocus_qaCongruent {p : Set W} (hp : p.Nonempty) (hpc : pᶜ.Nonempty) :
    Focus.Interpretation.qaCongruent (polarFocus p) (alt (ofSet p).query) :=
  (alt_query_ofSet hp hpc).symm

/-! ### Discourse strategies of polar subquestions -/

/-- A *wh*-question over candidates pursued through the polar question for each: the tree of the
sitting-back passage. -/
def agentStrategy (agents : List F) (P : F → Set W) : Strategy W :=
  .node (⨆ w, ofSet (strongAnswer (Set.range P) w)) (agents.map λ f => .leaf (ofSet (P f)).query)

/-- The polar subquestions for all candidates jointly resolve the *wh*-question. -/
theorem agentStrategy_isComplete [Finite W] {agents : List F} (hcov : ∀ f, f ∈ agents)
    (P : F → Set W) : (agentStrategy agents P).IsComplete := by
  refine .node (λ _ => ?_) (λ c hc => ?_)
  · have hmem : ∀ q, q ∈ ((agents.map λ f => RoseTree.leaf (ofSet (P f)).query).map RoseTree.value :
        Multiset (Question W)) ↔ ∃ f, (ofSet (P f)).query = q := by
      intro q
      simp only [Multiset.mem_coe, List.mem_map, List.map_map, Function.comp_def, RoseTree.leaf,
        RoseTree.value_node]
      exact ⟨λ ⟨f, _, h⟩ => ⟨f, h⟩, λ ⟨f, h⟩ => ⟨f, hcov f, h⟩⟩
    rw [← iInf_query_ofSet_eq_iSup_ofSet_strongAnswer]
    refine entails_of_le (le_antisymm ?_ ?_).le (Set.toFinite _)
    · exact le_iInf λ f => Multiset.inf_le ((hmem _).mpr ⟨f, rfl⟩)
    · exact Multiset.le_inf.mpr λ q hq => by obtain ⟨f, rfl⟩ := (hmem q).mp hq; exact iInf_le _ f
  · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact .leaf _

/-- A polar question about a disjunction of instances pursued through the polar questions of the
instances: the tree of the treaty passage. -/
def scalarStrategy (p q : Set W) : Strategy W :=
  .node (ofSet (p ∪ q)).query [.leaf (ofSet p).query, .leaf (ofSet q).query]

theorem scalarStrategy_isComplete [Finite W] (p q : Set W) : (scalarStrategy p q).IsComplete := by
  refine .node_pair (entails_of_le (le_def.mpr λ σ hσ => ?_) (Set.toFinite _)) (.leaf _) (.leaf _)
  rw [RoseTree.leaf, RoseTree.leaf, RoseTree.value_node, RoseTree.value_node, inf_eq_conj] at hσ
  obtain ⟨h₁, h₂⟩ := hσ
  have h₁' : σ ∈ (ofSet p).query := h₁
  have h₂' : σ ∈ (ofSet q).query := h₂
  show σ ∈ (ofSet (p ∪ q)).query
  rw [mem_query, mem_ofSet, info_ofSet] at h₁' h₂' ⊢
  rcases h₁' with h₁' | h₁' <;> rcases h₂' with h₂' | h₂'
  · exact Or.inl (h₁'.trans Set.subset_union_left)
  · exact Or.inl (h₁'.trans Set.subset_union_left)
  · exact Or.inl (h₂'.trans Set.subset_union_right)
  · exact Or.inr λ w hw => (Set.compl_union p q).symm ▸ ⟨h₁' hw, h₂' hw⟩

/-! ### The chapter's examples -/

/-- The lexical and syntactic means of polarity focus the chapter surveys. -/
inductive Means
  | emphaticDo | verumAccent | embedding | juxtaposed | ellipticEmbedding | fronting | faireCleft
  | leftDislocation | rightDislocation | siChe | siQue | siOnly | siParticle
  deriving DecidableEq, Repr

/-- What the polarity-focus utterance reacts to. -/
inductive Antecedent
  | explicitNegation | explicitQuestion | inferredNegation | openQuestion | modal | positive
  | absent
  deriving DecidableEq, Repr

/-- The dislocated constituent, if any. -/
inductive Dislocated
  | absent | subject | object | adverbial | both
  deriving DecidableEq, Repr

/-- Whether the utterance's situation is the antecedent's or an analogous one. -/
inductive Relation
  | identity | analogy | unstated
  deriving DecidableEq, Repr

/-- The environment a polarity-focus utterance occupies: correction after a negative antecedent,
contrast otherwise. -/
def Antecedent.env : Antecedent → Polarity.Marking.Env
  | .explicitNegation | .inferredNegation => .correction
  | _ => .contrast

structure Row where
  means : Means
  antecedent : Antecedent
  dislocated : Dislocated
  relation : Relation
  subquestion : Bool
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let means ← ex.parse? "strategy" [("emphaticDo", Means.emphaticDo),
    ("verumAccent", .verumAccent), ("embedding", .embedding), ("juxtaposed", .juxtaposed),
    ("ellipticEmbedding", .ellipticEmbedding), ("fronting", .fronting), ("faireCleft", .faireCleft),
    ("leftDislocation", .leftDislocation), ("rightDislocation", .rightDislocation),
    ("siChe", .siChe), ("siQue", .siQue), ("siOnly", .siOnly), ("siParticle", .siParticle)]
  let antecedent ← ex.parse? "antecedent" [("explicitNegation", Antecedent.explicitNegation),
    ("explicitQuestion", .explicitQuestion), ("inferredNegation", .inferredNegation),
    ("openQuestion", .openQuestion), ("modal", .modal), ("positive", .positive), ("none", .absent)]
  let dislocated ← ex.parse? "dislocated" [("none", Dislocated.absent), ("subject", .subject),
    ("object", .object), ("adverbial", .adverbial), ("both", .both)]
  let relation ← ex.parse? "relation" [("identity", Relation.identity), ("analogy", .analogy),
    ("unstated", .unstated)]
  let subquestion ← ex.parse? "subquestion" [("yes", true), ("no", false)]
  pure ⟨means, antecedent, dislocated, relation, subquestion⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- *Sì che* is attested answering a polar question as well as a denial, both environments the
Italian fragment licenses. -/
theorem rows_siChe_env : ∀ r ∈ rows, r.means = .siChe →
    r.antecedent.env ∈ Italian.PolarityMarking.siChe.environments := by
  decide

/-- *Sí que* is attested after denials, in non-contradictory contexts and as emphatic
reinforcement, all within the Spanish fragment's environments. -/
theorem rows_siQue_env : ∀ r ∈ rows, r.means = .siQue →
    r.antecedent.env ∈ Spanish.PolarityMarking.siQue.environments := by
  decide

/-- French *si* is attested only answering a preceding negative turn, the one environment the
French fragment licenses. -/
theorem rows_si_env : ∀ r ∈ rows, r.means = .siParticle →
    r.antecedent.env ∈ French.PolarityMarking.si.environments := by
  decide

/-- Every utterance the chapter reads as answering a subquestion stands in situational analogy to
its antecedent, the interrelation of its criteria it states; the converse fails. -/
theorem rows_subquestion_analogy :
    (∀ r ∈ rows, r.subquestion = true → r.relation = .analogy) ∧
      ∃ r ∈ rows, r.relation = .analogy ∧ r.subquestion = false := by
  decide

end GarassinoJacob2018
