import Linglib.Semantics.Alternatives.Basic
import Linglib.Semantics.Alternatives.Structural
import Linglib.Semantics.Questions.Exhaustivity
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Fragments.Turkish.QuestionParticles
import Linglib.Data.Examples.TurkHirsch2026

/-!
# Türk and Hirsch (2026): Constraining Alternatives in Turkish Polar Questions

This file formalizes [turk-hirsch-2026], an argument from Turkish polar questions that focus
alternatives are formed in the syntax under a category constraint. Turkish polar questions carry
the focus clitic *=mI*, which by default attaches to a focused covert polarity head Σ, (4), and
[atlamaz-2023] derives the Hamblin set of the question from focus alternatives: Σ has the identity
as ordinary value and the identity and negation as focus value, the alternatives propagate
pointwise, and a question head C_Q sets the ordinary value of the clause to the focus value of its
prejacent, `sigmaF`, `tp`, `cq`. The two alternatives of Σ are assumed rather than derived. Under
[rooth-1985]'s type-theoretic alternatives the focus value of Σ is every propositional operator,
so the Hamblin set is every proposition, `hamblinType_eq_univ`, and [dayal-1996]'s answerhood
operator, which selects the strongest true member, returns total information about the world,
`isStrongestTrueAnswer_hamblinType`; on the sample (31), which adds the deontic modal
propositions, it returns the conjunction that Ali had to sleep and did, (35b), rather than the
attested complete answer (35a), `isStrongestTrueAnswer_sample`. Contextual restriction cannot
repair this, since any Hamblin set at all is the intersection of the type-theoretic focus value
with some context, `exists_context_inter_eq`, whereas the modalized question (38) is unavailable
even in the supporting context (39). Instead alternatives are syntactic objects formed under the
Category Match Constraint (42), [fox-katzir-2011], [katzir-2007]: replacements of the focus share
its category, `categoryMatch`. With Σ and NEG the only morphemes of category Pol, the Hamblin set
is the polar one, `hamblinCat_eq`, `hamblinCat_eq_alt_polar`, Dayal's operator returns the
positive or the negative answer, `isStrongestTrueAnswer_hamblinCat`, and the modal answer (41)
is not a member, `mem_hamblinCat_iff`. No structural-complexity constraint is involved: category
match is a single substitution step of [katzir-2007]'s operations, `structOp_of_mem_categoryMatch`.

## Implementation notes

Propositions are sets of worlds, the deontic modal is `Modality.Kratzer.necessity` over a modal
base and an ordering source, and the lexicon is a list of terminals of `Syntax.Tree` so that
category match is the substitution step of `Alternatives.Structural.StructOp`; the denotation of
a tree is its terminal's operator and the identity elsewhere. Two-dimensional values are
`WithAlternatives`, whose `<*>` is pointwise functional application. The embedding data, (14) and
(18), in which *=mI* below the complementizer *diye* yields a declarative matrix clause and
*=mI* above it a matrix question, so that *=mI* tracks the highest focus mark, are recorded as
rows and not modelled. The examples are the rows of `Data.Examples.TurkHirsch2026`.

## References

* [turk-hirsch-2026]
* [atlamaz-2023]
* [fox-katzir-2011]
* [katzir-2007]
* [rooth-1985]
* [rooth-1992]
* [dayal-1996]
* [hamblin-1973b]
* [kamali-krifka-2020]
* [hirsch-schwarz-2025]
-/

namespace TurkHirsch2026

open Alternatives Alternatives.Structural Modality.Kratzer Question Syntax

/-! ### The polar morphemes and the deontic modal -/

/-- Syntactic categories: the polarity category of Σ and NEG, and that of the deontic modal. -/
inductive Cat where
  | pol
  | modal
  deriving DecidableEq, Repr

/-- The propositional operators of the lexicon. -/
inductive Word where
  | sigma
  | neg
  | deontic
  deriving DecidableEq, Repr

variable {W : Type*} (f : ModalBase W) (g : OrderingSource W)

/-- The operator a word denotes: Σ the identity, NEG complementation, and the deontic modal
necessity over the modal base and ordering source. -/
def Word.den : Word → Set W → Set W
  | .sigma => id
  | .neg => compl
  | .deontic => λ p => {w | necessity f g (· ∈ p) w}

/-- The operator a tree denotes: its terminal's operator, and the identity on a node. -/
def Tree.den : Tree Cat Word → Set W → Set W
  | .terminal _ w => w.den f g
  | _ => id

/-- (44): the lexicon of propositional operators, Σ and NEG of category Pol and the deontic modal
of its own category. -/
def lexicon : List (Tree Cat Word) :=
  [.terminal .pol .sigma, .terminal .pol .neg, .terminal .modal .deontic]

/-- The focused polarity head Σ_F. -/
def sigma : Tree Cat Word := .terminal .pol .sigma

/-! ### Composing the question -/

/-- Σ_F with a given focus value: the identity as ordinary value, (8a). -/
def sigmaF (A : Set (Set W → Set W)) : WithAlternatives (Set W → Set W) :=
  { ordinary := id, alternatives := A }

/-- The TP: Σ_F applied pointwise to the unfocused prejacent `p`, (9). -/
def tp (A : Set (Set W → Set W)) (p : Set W) : WithAlternatives (Set W) := sigmaF A <*> pure p

/-- (10): C_Q sets the ordinary value to the focus value of its prejacent, the Hamblin set. -/
def cq (m : WithAlternatives (Set W)) : WithAlternatives (Set (Set W)) :=
  { ordinary := m.alternatives, alternatives := {m.alternatives} }

theorem tp_alternatives (A : Set (Set W → Set W)) (p : Set W) :
    (tp A p).alternatives = (· p) '' A := by
  ext q
  simp [tp, sigmaF]

/-! ### Type-theoretic alternatives over-generate -/

/-- The Hamblin set under [rooth-1985]'s type-theoretic focus value, every operator of Σ's type,
(26). -/
def hamblinType (p : Set W) : Set (Set W) := (cq (tp Set.univ p)).ordinary

/-- (28): the type-theoretic Hamblin set is every proposition. -/
theorem hamblinType_eq_univ (p : Set W) : hamblinType p = Set.univ := by
  rw [hamblinType, cq, tp_alternatives]
  exact Set.eq_univ_of_forall λ q => ⟨λ _ => q, Set.mem_univ _, rfl⟩

/-- Under type-theoretic alternatives the complete answer at `w` is total information about
`w`: the responder must supply every true proposition. -/
theorem isStrongestTrueAnswer_hamblinType (p : Set W) (w : W) :
    IsStrongestTrueAnswer (hamblinType p) w {w} := by
  rw [hamblinType_eq_univ]
  exact ⟨⟨Set.mem_univ _, rfl⟩, λ _ hq => Set.singleton_subset_iff.2 hq.2⟩

/-- (31): the sample of the Hamblin set with the deontic propositions. -/
def sample (p : Set W) : Set (Set W) :=
  {p, pᶜ, Word.deontic.den f g p, (Word.deontic.den f g p)ᶜ, Word.deontic.den f g p ∩ p}

theorem sample_subset_hamblinType (p : Set W) : sample f g p ⊆ hamblinType p := by
  rw [hamblinType_eq_univ]
  exact Set.subset_univ _

/-- (34): at a world where Ali had to sleep and slept, the strongest true member of the sample
is the conjunction that he had to sleep and did, the over-informative answer (35b). -/
theorem isStrongestTrueAnswer_sample {p : Set W} {w : W} (hw : w ∈ p)
    (hbox : w ∈ Word.deontic.den f g p) :
    IsStrongestTrueAnswer (sample f g p) w (Word.deontic.den f g p ∩ p) := by
  refine ⟨⟨by simp [sample], hbox, hw⟩, ?_⟩
  rintro q ⟨hq, hwq⟩
  simp only [sample, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact Set.inter_subset_right
  · exact absurd hw hwq
  · exact Set.inter_subset_left
  · exact absurd hbox hwq
  · exact le_rfl

/-- (36): any Hamblin set whatever is the type-theoretic focus value restricted by some
context, so restriction by context alone cannot exclude the modalized question (38). -/
theorem exists_context_inter_eq (p : Set W) (H : Set (Set W)) :
    ∃ c : Set (Set W), hamblinType p ∩ c = H :=
  ⟨H, by rw [hamblinType_eq_univ, Set.univ_inter]⟩

/-! ### Category match -/

/-- (42), the Category Match Constraint: the alternatives of a focused constituent are its
same-category replacements from the lexicon. -/
def categoryMatch {C V : Type} (lex : List (Tree C V)) (φ : Tree C V) : Set (Tree C V) :=
  {ψ | ψ ∈ lex ∧ ψ.cat = φ.cat}

/-- A category-match replacement is one substitution step of [katzir-2007]'s structural
operations; no complexity bound is involved. -/
theorem structOp_of_mem_categoryMatch {C V : Type} {lex : List (Tree C V)} {φ ψ : Tree C V}
    (h : ψ ∈ categoryMatch lex φ) : StructOp lex φ ψ :=
  .subst h.2 h.1

/-- (45): the category-match alternatives of Σ_F are Σ and NEG. -/
theorem categoryMatch_sigma :
    categoryMatch lexicon sigma = {.terminal .pol .sigma, .terminal .pol .neg} := by
  ext ψ
  simp only [categoryMatch, lexicon, sigma, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
    or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl | rfl, hc⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hc (by decide)
  · rintro (rfl | rfl) <;> exact ⟨by simp, rfl⟩

/-- The Hamblin set under category match. -/
def hamblinCat (p : Set W) : Set (Set W) :=
  (cq (tp ((Tree.den f g) '' categoryMatch lexicon sigma) p)).ordinary

/-- Under category match the Hamblin set is the polar one, (23). -/
theorem hamblinCat_eq (p : Set W) : hamblinCat f g p = {p, pᶜ} := by
  rw [hamblinCat, cq, tp_alternatives, categoryMatch_sigma, Set.image_image, Set.image_pair]
  rfl

/-- The category-match Hamblin set is the alternative set of the polar interrogative. -/
theorem hamblinCat_eq_alt_polar {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    hamblinCat f g p = alt (polar p) := by
  rw [hamblinCat_eq, alt_polar_of_nontrivial hne hnu]

/-- (41): a proposition is a member of the category-match Hamblin set only as the positive or
the negative answer; the modal answer is excluded as soon as it differs from both. -/
theorem mem_hamblinCat_iff (p q : Set W) : q ∈ hamblinCat f g p ↔ q = p ∨ q = pᶜ := by
  rw [hamblinCat_eq]
  rfl

/-- (35a): under category match the complete answer is the positive answer when it is true. -/
theorem isStrongestTrueAnswer_hamblinCat {p : Set W} {w : W} (hw : w ∈ p) :
    IsStrongestTrueAnswer (hamblinCat f g p) w p := by
  rw [hamblinCat_eq]
  refine ⟨⟨Set.mem_insert _ _, hw⟩, ?_⟩
  rintro q ⟨hq, hwq⟩
  rcases hq with rfl | rfl
  · exact le_rfl
  · exact absurd hw hwq

/-- And the negative answer when the positive one is false. -/
theorem isStrongestTrueAnswer_hamblinCat_compl {p : Set W} {w : W} (hw : w ∉ p) :
    IsStrongestTrueAnswer (hamblinCat f g p) w pᶜ := by
  rw [hamblinCat_eq]
  refine ⟨⟨Set.mem_insert_of_mem _ rfl, hw⟩, ?_⟩
  rintro q ⟨hq, hwq⟩
  rcases hq with rfl | rfl
  · exact absurd hwq hw
  · exact le_rfl

/-- *=mI* is vacuous: the fragment's entry is the identity, the ordinary value of Σ. -/
theorem mi_denotation_eq {V : Type} (p : V → Prop) :
    Turkish.QuestionParticles.mi.denotation p = p := rfl

end TurkHirsch2026
