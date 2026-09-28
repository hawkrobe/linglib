module

public import Linglib.Semantics.Questions.Hamblin
public import Mathlib.Algebra.Group.Action.Prod

/-!
# Highlighting

A sentence does more than express an inquisitive proposition: it makes some possibilities
salient, as antecedents for anaphora, and marks each of them as positive or negative
([roelofsen-vangool-2010], [roelofsen-farkas-2015]). *Is the number of planets even?* and *Is it
odd?* express the same issue, but *yes* conveys different answers after them, and *Is it not
even?* differs from *Is it odd?* in what *no* conveys.

This file formalizes the two-dimensional semantics of [roelofsen-farkas-2015]. Its language
`Highlighting.Formula` is built from atoms by negation, inquisitive disjunction and the two
projection operators `!` and `?`, the non-inquisitive and the non-informative projection. A
formula has two values, each computed from the values of its parts: the proposition it expresses
in InqB (`Highlighting.Formula.proposition`, (26)), a `Question`, and the possibilities it
highlights, each with its polarity (`Highlighting.Formula.highlights`, (60)), an element of
`Polarity × Set W`. An atom
highlights its truth set positively; a negation highlights the complement of everything its
argument highlights, negatively (`Highlighting.neg`); a disjunction highlights what either
disjunct does; and a projection leaves a single negative possibility in place and otherwise
merges the highlighted possibilities into one positive possibility (`Highlighting.project`).

The highlights of a formula are not a function of its proposition
(`Highlighting.Formula.not_exists_highlights_eq_comp_proposition`): `?p` and `?¬p` express the
same issue but highlight `p` positively and its complement negatively. The projection operators
are therefore primitive: `!p` and `¬¬p` express the same proposition, but `!p` highlights `p`
positively and `¬¬p` negatively (`Highlighting.Formula.highlights_bang_ne_highlights_neg_neg`).

The polarity group acts on a possibility and its polarity together: the negative polarity
complements the possibility and reverses its polarity. The basic formulas on an atom, `p` and
`¬p` (`Highlighting.Formula.ofPolarity`), highlight the images of `(positive, p)` under the two
polarities, so *Is it odd?* and *Is it not even?* highlight the same worlds with opposite
polarities.

## Main definitions

* `Highlighting.neg`, `Highlighting.project`: the clauses of (60) for negation and projection.
* `Highlighting.Formula`: the language, with `proposition` and `highlights`, its two semantic
  values.

## Implementation notes

The language is that of InqB without conjunction and implication, which [roelofsen-farkas-2015]
leave aside, and with the projections primitive, as the highlighting dimension requires. In the
presentation of [ciardelli-groenendijk-roelofsen-2018], formalized as the modal-free fragment of
`ModalLogic.Inquisitive.Formula`, negation and the projections are defined from `⊥`, `∧` and `→`,
so `!p` is `¬¬p` there.

## References

* [roelofsen-farkas-2015]
* [roelofsen-vangool-2010]
* [ciardelli-groenendijk-roelofsen-2018]
-/

@[expose] public section

variable {W : Type*}

namespace Highlighting

/-- The negation of a formula highlights the complement of the union of the possibilities the
formula highlights, with negative polarity. -/
def neg (H : Set (Polarity × Set W)) : Set (Polarity × Set W) :=
  {(.negative, (⋃₀ (Prod.snd '' H))ᶜ)}

open Classical in
/-- The projections `!` and `?` of a formula leave a single negative possibility in place and
merge any other highlights into one positive possibility, their union. -/
noncomputable def project (H : Set (Polarity × Set W)) : Set (Polarity × Set W) :=
  if ∃ α, H = {(.negative, α)} then H else {(.positive, ⋃₀ (Prod.snd '' H))}

/-- The negation of a formula highlighting a single possibility highlights its complement. -/
@[simp] theorem neg_singleton (s : Polarity) (α : Set W) :
    neg {(s, α)} = {(.negative, αᶜ)} := by
  simp [neg]

/-- Projection keeps a single negative possibility. -/
@[simp] theorem project_singleton_negative (α : Set W) :
    project {(.negative, α)} = {(.negative, α)} :=
  ite_eq_left ⟨α, rfl⟩

/-- Projection keeps a single positive possibility. -/
@[simp] theorem project_singleton_positive (α : Set W) :
    project {(.positive, α)} = {(.positive, α)} := by
  have h : ¬ ∃ β, ({(.positive, α)} : Set (Polarity × Set W)) = {(.negative, β)} := by
    rintro ⟨β, h⟩
    simpa using Set.singleton_eq_singleton_iff.mp h
  rw [project, ite_eq_right h]
  simp

/-- Projection keeps a single possibility, whatever its polarity. -/
@[simp] theorem project_singleton (x : Polarity × Set W) : project {x} = {x} := by
  obtain ⟨_ | _, α⟩ := x
  · exact project_singleton_positive α
  · exact project_singleton_negative α

/-- The language of [roelofsen-farkas-2015]: atoms, negation, inquisitive disjunction, and the
non-inquisitive and non-informative projections `!` and `?`. -/
inductive Formula (A : Type*) where
  | atom (a : A)
  | neg (φ : Formula A)
  | inqDisj (φ ψ : Formula A)
  | bang (φ : Formula A)
  | query (φ : Formula A)
  deriving DecidableEq, Repr

namespace Formula

variable {A : Type*} (v : A → Set W)

/-- (26): the proposition a formula expresses under the valuation `v` of its atoms. -/
def proposition : Formula A → Question W
  | atom a => Question.ofSet (v a)
  | neg φ => (proposition φ)ᶜ
  | inqDisj φ ψ => proposition φ ⊔ proposition ψ
  | bang φ => (proposition φ).bang
  | query φ => (proposition φ).query

/-- (60): the possibilities a formula highlights, each with its polarity. -/
noncomputable def highlights : Formula A → Set (Polarity × Set W)
  | atom a => {(.positive, v a)}
  | neg φ => Highlighting.neg (highlights φ)
  | inqDisj φ ψ => highlights φ ∪ highlights ψ
  | bang φ => project (highlights φ)
  | query φ => project (highlights φ)

attribute [simp] proposition highlights

/-- The basic formula of polarity `s` on the atom `a`: `a` or `¬a`. -/
def ofPolarity : Polarity → A → Formula A
  | .positive, a => atom a
  | .negative, a => neg (atom a)

/-- A basic formula of polarity `s` on `a` expresses the proposition `s • v a`. -/
@[simp] theorem proposition_ofPolarity (s : Polarity) (a : A) :
    (ofPolarity s a).proposition v = Question.ofSet (s • v a) := by
  cases s
  · rfl
  · simp [ofPolarity, Question.compl_eq, Question.info_ofSet]

/-- A basic formula of polarity `s` on `a` highlights the image of `(positive, v a)` under `s`:
the negative polarity complements the possibility and marks it negative. -/
@[simp] theorem highlights_ofPolarity (s : Polarity) (a : A) :
    (ofPolarity s a).highlights v = {s • (.positive, v a)} := by
  cases s <;> simp [ofPolarity, Prod.smul_mk]

/-- The polar interrogatives on `a` and on `¬a` express the same issue. -/
theorem proposition_query_ofPolarity (s : Polarity) (a : A) :
    (query (ofPolarity s a)).proposition v = Question.polar (v a) := by
  rw [proposition, proposition_ofPolarity, Question.query_ofSet, Question.polar_smul]

/-- There is more to the meaning of a formula than its proposition: `?a` and `?¬a` express the
same issue but highlight different possibilities, so no function of the proposition gives the
highlights. -/
theorem not_exists_highlights_eq_comp_proposition [Nonempty A] :
    ¬ ∃ f : Question W → Set (Polarity × Set W),
      ∀ φ : Formula A, φ.highlights v = f (φ.proposition v) := by
  rintro ⟨f, hf⟩
  obtain ⟨a⟩ := ‹Nonempty A›
  have h := (hf (query (ofPolarity .positive a))).trans
    ((congrArg f ((proposition_query_ofPolarity v .positive a).trans
      (proposition_query_ofPolarity v .negative a).symm)).trans
        (hf (query (ofPolarity .negative a))).symm)
  simp [ofPolarity, Set.singleton_eq_singleton_iff] at h

/-- The projection `!` is primitive: `!a` and `¬¬a` express the same proposition, but `!a`
highlights `a` positively and `¬¬a` negatively. -/
theorem highlights_bang_ne_highlights_neg_neg (a : A) :
    (bang (atom a)).proposition v = (neg (neg (atom a))).proposition v ∧
      (bang (atom a)).highlights v ≠ (neg (neg (atom a))).highlights v := by
  refine ⟨?_, ?_⟩
  · simp [Question.bang, Question.compl_eq, Question.info_ofSet]
  · simp [Set.singleton_eq_singleton_iff]

end Formula

end Highlighting
