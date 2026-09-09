import Linglib.Semantics.Alternatives.Symmetric
import Linglib.Semantics.Alternatives.Structural
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Logic.Modal.Defs
import Linglib.Data.Examples.FoxKatzir2011

/-!
# Fox and Katzir (2011): On the Characterization of Alternatives

This file formalizes [fox-katzir-2011]'s argument that the alternatives of scalar implicature
and of association with focus are one set, [katzir-2007]'s structural alternatives extended by
the salient constituents of the context (`formalAlternatives`), and that symmetry among
alternatives is broken only there: contextual restriction never keeps one of two alternatives
that partition the assertion while pruning the other. The implicature and *only* operators
`SM` and `Only` negate the strictly stronger and the non-weaker alternatives; on symmetric
alternatives both are contradictory (`SM_eq_empty_of_isSymmetric`), a universal operator above
the assertion removes the symmetry and both inferences arise (`mem_SM_nec`), innocent exclusion
negates neither symmetric alternative (`exhIE_eq_self_of_isSymmetric`), and a contextual set
closed under negation and conjunction keeps both or neither
(`Alternatives.IsSymmetric.mem_of_mem`). The paper's stronger condition, allowable restriction
through exhaustive relevance, forbids pruning one of two compatible disjuncts as well
(`not_isAllowableRestriction_pair`).

## Implementation notes

Sentences are propositions `Set W`, alternative sets are `Set (Set W)`, and the operators are
intersections of complements, the paper's propositional rendering of *only*. The structural
definition is stated without focus marking, so `formalAlternatives` contains the paper's set;
its one new clause, salient constituents, is what brings a symmetric alternative into the set
(`mem_formalAlternatives_of_salient`). Universal operators are `ModalLogic.box` over an
accessibility relation, covering the modal and the quantificational cases alike.

## References

* [fox-katzir-2011]
* [katzir-2007]
* [kroch-1972]
* [horn-1972]
* [rooth-1985]
* [sauerland-2004]
* [fox-2007]
-/

namespace FoxKatzir2011

open Alternatives Exhaustification ModalLogic Set Data.Examples

variable {W : Type*}

/-! ### Formal alternatives -/

section Formal

open Syntax Alternatives.Structural

variable {C V : Type} (lex : List (Tree C V)) (φ : Tree C V) (salient : List (Tree C V))

/-- The substitution source in a context: the lexicon, the sub-constituents of the sentence,
and the salient constituents of the context. -/
def contextualSource : List (Tree C V) := lex ++ φ.subtrees ++ salient

/-- The formal alternatives in a context: whatever is at most as complex as the sentence over
the contextual substitution source. -/
def formalAlternatives : Set (Tree C V) :=
  {ψ | atMostAsComplex (contextualSource lex φ salient) ψ φ}

/-- Without salient constituents the alternatives are [katzir-2007]'s. -/
theorem formalAlternatives_nil : formalAlternatives lex φ [] = structuralAlternatives lex φ := by
  rw [formalAlternatives, contextualSource, List.append_nil]
  rfl

/-- A salient constituent of the sentence's category is a formal alternative. -/
theorem mem_formalAlternatives_of_salient {ψ : Tree C V} (hψ : ψ ∈ salient)
    (hcat : ψ.cat = φ.cat) : ψ ∈ formalAlternatives lex φ salient :=
  Relation.ReflTransGen.single (StructOp.subst hcat (by simp [contextualSource, hψ]))

/-- The symmetric *some but not all* is not a structural alternative of *some*, but it becomes a
formal alternative once it is salient. -/
theorem someButNotAll_mem_formalAlternatives :
    someButNotAllSentence ∈ formalAlternatives exLexicon someSentence [someButNotAllSentence] :=
  mem_formalAlternatives_of_salient _ _ _ (List.mem_singleton_self _) rfl

end Formal

/-! ### The operators -/

section Operators

variable (A : Set (Set W)) (S : Set W)

/-- The alternatives negated for scalar implicature: the strictly stronger members. -/
def nSI : Set (Set W) := {p ∈ A | p ⊂ S}

/-- The alternatives negated by *only*: the non-weaker members. -/
def nAF : Set (Set W) := {p ∈ A | ¬ S ⊆ p}

/-- The scalar implicature: the negations of the strictly stronger alternatives. -/
def SI : Set W := ⋂ p ∈ nSI A S, pᶜ

/-- The strengthened meaning. -/
def SM : Set W := S ∩ SI A S

/-- The exclusion of *only*: the negations of the non-weaker alternatives. -/
def EXC : Set W := ⋂ p ∈ nAF A S, pᶜ

/-- *Only*: the prejacent with the non-weaker alternatives denied. -/
def Only : Set W := S ∩ EXC A S

variable {A S}

theorem mem_SM {w : W} : w ∈ SM A S ↔ w ∈ S ∧ ∀ p ∈ A, p ⊂ S → w ∉ p := by
  simp only [SM, SI, nSI, mem_inter_iff, mem_iInter₂, mem_ofPred_eq, mem_compl_iff]
  exact and_congr_right λ _ =>
    ⟨λ h p hp hps => h p ⟨hp, hps⟩, λ h p ⟨hp, hps⟩ => h p hp hps⟩

theorem mem_Only {w : W} : w ∈ Only A S ↔ w ∈ S ∧ ∀ p ∈ A, ¬ S ⊆ p → w ∉ p := by
  simp only [Only, EXC, nAF, mem_inter_iff, mem_iInter₂, mem_ofPred_eq, mem_compl_iff]
  exact and_congr_right λ _ =>
    ⟨λ h p hp hps => h p ⟨hp, hps⟩, λ h p ⟨hp, hps⟩ => h p hp hps⟩

theorem nSI_subset_nAF : nSI A S ⊆ nAF A S := λ _ ⟨hp, hps⟩ => ⟨hp, (ssubset_def ▸ hps).2⟩

/-- *Only* is at least as strong as the strengthened meaning. -/
theorem Only_subset_SM : Only A S ⊆ SM A S := λ _ hw =>
  mem_SM.2 ⟨(mem_Only.1 hw).1, λ p hp hps => (mem_Only.1 hw).2 p hp (ssubset_def ▸ hps).2⟩

end Operators

/-! ### Symmetry -/

section Symmetry

variable {A : Set (Set W)} {S S₁ S₂ : Set W}

/-- The symmetry problem: with both symmetric alternatives in the set, the strengthened meaning
is contradictory, since negating either asserts the other. -/
theorem SM_eq_empty_of_isSymmetric (h : IsSymmetric S S₁ S₂) (h₁ : S₁ ∈ A) (h₂ : S₂ ∈ A)
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty) : SM A S = ∅ := by
  ext w
  simp only [mem_SM, mem_empty_iff_false, iff_false, not_and]
  intro hw hall
  have hw' : w ∈ S₁ ∪ S₂ := h.union ▸ hw
  rcases hw' with hw₁ | hw₂
  · exact hall S₁ h₁ (h.ssubset_left hne₂) hw₁
  · exact hall S₂ h₂ (h.symm.ssubset_left hne₁) hw₂

/-- *Only* on symmetric alternatives is contradictory as well. -/
theorem Only_eq_empty_of_isSymmetric (h : IsSymmetric S S₁ S₂) (h₁ : S₁ ∈ A) (h₂ : S₂ ∈ A)
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty) : Only A S = ∅ :=
  subset_empty_iff.1 ((SM_eq_empty_of_isSymmetric h h₁ h₂ hne₁ hne₂) ▸ Only_subset_SM)

/-- Neither symmetric alternative is innocently excludable given the assertion. -/
theorem not_isInnocentlyExcludable_of_isSymmetric (h : IsSymmetric S S₁ S₂)
    (hne₁ : S₁.Nonempty) : ¬ IsInnocentlyExcludable {S, S₁, S₂} S S₁ := by
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (by simp)]
  obtain ⟨a, ha⟩ := hne₁
  refine λ h' => h' ⟨h.subset_left ha, ?_⟩ ha
  rintro ⟨v, hv, hva, hnav⟩
  have hv' : v ∈ S₁ ∪ S₂ := h.union ▸ hv
  rcases hv' with hv₁ | hv₂
  · refine hnav λ c hc hac => ?_
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    obtain h1 | h1 | h1 := hc <;> subst c
    · exact hv
    · exact hv₁
    · exact (disjoint_left.1 h.disjoint ha hac).elim
  · exact disjoint_left.1 h.disjoint ha (hva S₂ (by simp) hv₂)

/-- Innocent exclusion negates neither symmetric alternative: exhaustification is vacuous. -/
theorem exhIE_eq_self_of_isSymmetric (h : IsSymmetric S S₁ S₂) (hne₁ : S₁.Nonempty)
    (hne₂ : S₂.Nonempty) : exhIE {S, S₁, S₂} S = S := by
  ext w
  rw [mem_exhIE_iff _ _ (toFinite _)]
  refine ⟨λ hw => hw.1, λ hw => ⟨hw, λ q hq => ?_⟩⟩
  have hq1 := hq.1
  simp only [mem_insert_iff, mem_singleton_iff] at hq1
  obtain h1 | h1 | h1 := hq1 <;> subst q
  · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨w, hw⟩ subset_rfl hq).elim
  · exact (not_isInnocentlyExcludable_of_isSymmetric h hne₁ hq).elim
  · have := not_isInnocentlyExcludable_of_isSymmetric h.symm hne₂
    rw [pair_comm S₂ S₁] at this
    exact (this hq).elim

/-- With the symmetric alternative absent, as under Horn scales, the other is innocently
excludable and the implicature arises. -/
theorem exhIE_pair_eq_sdiff (h : IsSymmetric S S₁ S₂) (hne₂ : S₂.Nonempty) :
    exhIE {S, S₁} S = S₂ := by
  obtain ⟨b, hb⟩ := hne₂
  have hIE : IsInnocentlyExcludable {S, S₁} S S₁ := by
    refine .of_forall_subset_or_notMem (by simp) (h.subset_right hb)
      (disjoint_left.1 h.disjoint.symm hb) ?_
    rintro c hc
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    obtain h1 | h1 := hc <;> subst c
    · exact Or.inl subset_rfl
    · exact Or.inr (disjoint_left.1 h.disjoint.symm hb)
  ext w
  rw [mem_exhIE_iff _ _ (toFinite _), ← h.sdiff_eq, mem_sdiff]
  refine ⟨λ ⟨hw, h'⟩ => ⟨hw, h' S₁ hIE⟩, λ ⟨hw, hw₁⟩ => ⟨hw, λ q hq => ?_⟩⟩
  have hq1 := hq.1
  simp only [mem_insert_iff, mem_singleton_iff] at hq1
  obtain h1 | h1 := hq1 <;> subst q
  · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨w, hw⟩ subset_rfl hq).elim
  · exact hw₁

end Symmetry

/-! ### Universal operators -/

section Universal

variable {R : W → W → Prop} {S S₁ S₂ : Set W}

/-- Necessity as a proposition: the worlds all of whose accessible worlds satisfy `p`. -/
def nec (R : W → W → Prop) (p : Set W) : Set W := {x | □[R] (· ∈ p) x}

/-- Under a universal operator the alternatives are no longer symmetric whenever some world's
accessible worlds fall on both sides. -/
theorem not_isSymmetric_nec {x : W} (hx : x ∈ nec R S) (hx₁ : x ∉ nec R S₁) (hx₂ : x ∉ nec R S₂) :
    ¬ IsSymmetric (nec R S) (nec R S₁) (nec R S₂) := λ h => by
  have : x ∈ nec R S₁ ∪ nec R S₂ := h.union ▸ hx
  exact this.elim hx₁ hx₂

/-- Both implicatures arise under the universal operator: such a world lies in the strengthened
meaning. -/
theorem mem_SM_nec {x : W} (hx : x ∈ nec R S) (hx₁ : x ∉ nec R S₁) (hx₂ : x ∉ nec R S₂) :
    x ∈ SM {nec R S, nec R S₁, nec R S₂} (nec R S) := by
  refine mem_SM.2 ⟨hx, λ p hp hps => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  obtain h1 | h1 | h1 := hp <;> subst p
  · exact (ssubset_irrefl _ hps).elim
  · exact hx₁
  · exact hx₂

/-- Both exclusions of *only* arise under the universal operator. -/
theorem mem_Only_nec {x : W} (hx : x ∈ nec R S) (hx₁ : x ∉ nec R S₁) (hx₂ : x ∉ nec R S₂) :
    x ∈ Only {nec R S, nec R S₁, nec R S₂} (nec R S) := by
  refine mem_Only.2 ⟨hx, λ p hp hps => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  obtain h1 | h1 | h1 := hp <;> subst p
  · exact (hps subset_rfl).elim
  · exact hx₁
  · exact hx₂

end Universal

/-! ### Contextual restriction -/

section Restriction

variable {S S₁ S₂ : Set W} {F : Set (Set W)}

/-- Context cannot break symmetry: with the context set the relevant propositions, closed under
negation and conjunction, the actual alternatives keep both symmetric alternatives or
neither. -/
theorem mem_inter_of_isSymmetric (h : IsSymmetric S S₁ S₂) (R : BooleanSubalgebra (Set W))
    (hS : S ∈ R) (hF : S₂ ∈ F) (h₁ : S₁ ∈ (R : Set (Set W)) ∩ F) :
    S₂ ∈ (R : Set (Set W)) ∩ F :=
  ⟨h.mem_of_mem hS h₁.1, hF⟩

/-- Exhaustively relevant given a restriction: its *only*-meaning lies in the Boolean closure of
the restriction. -/
def ExhaustivelyRelevant (A : Set (Set W)) (p : Set W) : Prop :=
  Only A p ∈ BooleanSubalgebra.closure A

/-- An allowable restriction of the formal alternatives: it keeps the assertion, and prunes
nothing exhaustively relevant. -/
def IsAllowableRestriction (F A : Set (Set W)) (S : Set W) : Prop :=
  S ∈ A ∧ ∀ p ∈ F \ A, ¬ ExhaustivelyRelevant A p

/-- Neither disjunct of a disjunction can be pruned in favour of the other, symmetric or not:
its *only*-meaning is the assertion without the kept disjunct. -/
theorem not_isAllowableRestriction_pair (hS : S = S₁ ∪ S₂) (h₂₁ : ¬ S₂ ⊆ S₁) (hF : S₂ ∈ F)
    (h₂ : S₂ ∉ ({S, S₁} : Set (Set W))) : ¬ IsAllowableRestriction F {S, S₁} S := by
  rintro ⟨-, hall⟩
  refine hall S₂ ⟨hF, h₂⟩ ?_
  have hOnly : Only {S, S₁} S₂ = S \ S₁ := by
    subst hS
    ext w
    rw [mem_Only, union_sdiff_left, mem_sdiff]
    simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨λ ⟨hw, _, h⟩ => ⟨hw, h h₂₁⟩,
      λ ⟨hw, h⟩ => ⟨hw, λ hn => (hn subset_union_right).elim, λ _ => h⟩⟩
  rw [ExhaustivelyRelevant, hOnly]
  exact BooleanSubalgebra.sdiff_mem (BooleanSubalgebra.subset_closure (by simp))
    (BooleanSubalgebra.subset_closure (by simp))

end Restriction

/-! ### The data -/

/-- A sentence of the data: whether its formal alternatives contain a symmetric pair, whether a
universal operator intervenes, whether the alternatives at issue are compatible, and whether
the inference arises. -/
structure Row where
  symmetric : Bool
  universal : Bool
  compatible : Bool
  inference : Bool
  deriving DecidableEq

def yesNoTable : List (String × Bool) := [("yes", true), ("no", false)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let s ← ex.parse? "symmetric" yesNoTable
  let u ← ex.parse? "universal" yesNoTable
  let c ← ex.parse? "compatible" yesNoTable
  let i ← ex.parse? "inference" yesNoTable
  pure ⟨s, u, c, i⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The inference arises exactly when a universal operator removes the symmetry, or when the
formal alternatives contain neither a symmetric pair nor compatible disjuncts. -/
theorem rows_predicted : ∀ r ∈ rows,
    (r.inference = true ↔ r.universal = true ∨ (r.symmetric = false ∧ r.compatible = false)) := by
  decide

end FoxKatzir2011
