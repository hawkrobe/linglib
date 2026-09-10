import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Questions.Bias
import Linglib.Data.Examples.GartnerGyuris2017

/-!
# Gärtner and Gyuris (2017): On Delimiting the Space of Bias Profiles for Polar Interrogatives

This file formalizes [gartner-gyuris-2017]'s space of bias profiles. Following [sudo-2013], a polar
interrogative clause type is biased evidentially (by compelling contextual evidence for p, against
p, or neither) and epistemically (by the speaker's expectation that p, that not p, or neither), and
separately for each of the three polar questions it can express, the positive question and the
negative questions with inside and outside negation ([ladd-1981]). A bias profile chooses a nonempty
set of the three values for each of the six cells, so there are 7⁶ = 117649 profiles
(`card_profile`). The paper's delimiting principles are predicates on profiles, and the sizes of the
spaces they leave are theorems: the principles that constrain cells separately count as products
over cells (`card_cellwise`), those relating a positive question to its negative counterparts count
as sums over the positive question's value (`card_perDim`, `card_byForm`), giving 46656 for
Convexity, 2744 for Narrow Epistemic Choice, 512 for Static Complementarity with Convexity, 729 and
4096 for the two versions of Polarity Match, 63504 for PPQ ≠ NPQ, and 33856 and 56536 for
distributive and collective Quantitative Markedness. Avoid Disagreement entails Convexity and
excludes Narrow Epistemic Choice (`not_avoidDisagreement_of_narrowEpistemic`), the paper's reason to
confine Polarity Match to the evidential dimension. Appendix A's five total profiles from
[sudo-2013] and [gyuris-2017] are checked against every principle (`sample_staticComplementarity`),
and the infelicity judgments of examples (1), (2), (8), and (9) follow from the profiles
(`rows_felicity`).

## Implementation notes

The three question forms are the substrate's `PQForm`, whose `PosQ`, `LoNQ`, and `HiNQ` are the
paper's PPQ, IN-NPQ, and ON-NPQ; the six cells and the seven choices are enumerated types, so that
every decision the kernel makes ranges over a literal list. The Hungarian *e*-interrogative cannot
express an inside-negation question, so it is a partial profile kept apart from the five total
ones; the paper's Czech and Romero comparisons belong to the later papers' studies.

## References

* [gartner-gyuris-2017]
* [sudo-2013]
* [gyuris-2017]
* [ladd-1981]
* [buring-gunlogson-2000]
-/

namespace GartnerGyuris2017

open Question Features Data.Examples

/-- A bias value: evidence or expectation for p (+), against p (−), or neither (%). -/
inductive Bias where
  | pos
  | neg
  | neut
  deriving DecidableEq, Fintype

/-- A bias choice: one of the seven nonempty sets of bias values. -/
inductive Choice where
  | pos
  | neg
  | neut
  | posNeut
  | posNeg
  | negNeut
  | all
  deriving DecidableEq, Fintype

/-- The values a choice admits. -/
def Choice.toFinset : Choice → Finset Bias
  | .pos => {.pos}
  | .neg => {.neg}
  | .neut => {.neut}
  | .posNeut => {.pos, .neut}
  | .posNeg => {.pos, .neg}
  | .negNeut => {.neg, .neut}
  | .all => Finset.univ

theorem card_choice : Fintype.card Choice = 7 := by decide

/-- The dimension a bias is drawn from. -/
inductive Dimension where
  | evidential
  | epistemic
  deriving DecidableEq, Fintype

/-- The six cells of a profile: a polar question form in a bias dimension. -/
inductive Cell where
  | ppqEv
  | ppqEp
  | inEv
  | inEp
  | onEv
  | onEp
  deriving DecidableEq, Fintype

/-- The question form of a cell. -/
def Cell.form : Cell → PQForm
  | .ppqEv | .ppqEp => .PosQ
  | .inEv | .inEp => .LoNQ
  | .onEv | .onEp => .HiNQ

/-- The dimension of a cell. -/
def Cell.dim : Cell → Dimension
  | .ppqEv | .inEv | .onEv => .evidential
  | .ppqEp | .inEp | .onEp => .epistemic

/-- The cell of a form in a dimension. -/
def Cell.of : PQForm → Dimension → Cell
  | .PosQ, .evidential => .ppqEv
  | .PosQ, .epistemic => .ppqEp
  | .LoNQ, .evidential => .inEv
  | .LoNQ, .epistemic => .inEp
  | .HiNQ, .evidential => .onEv
  | .HiNQ, .epistemic => .onEp

/-- A bias profile: a choice for each cell. -/
abbrev Profile := Cell → Choice

theorem card_profile : Fintype.card Profile = 117649 := by
  simp only [Fintype.card_fun, card_choice]; decide

/-! ### Counting principles -/

/-- A principle that constrains each cell on its own. -/
abbrev Cellwise (A : Cell → Choice → Prop) (p : Profile) : Prop := ∀ c, A c (p c)

/-- A cellwise principle leaves the product over cells of the choices it allows there. -/
theorem card_cellwise (A : Cell → Choice → Prop) [∀ c, DecidablePred (A c)] :
    Fintype.card {p : Profile // Cellwise A p} = ∏ c, Fintype.card {x // A c x} :=
  (Fintype.card_congr (Equiv.subtypePiEquivPi (p := A))).trans Fintype.card_pi

/-- A profile by dimension. -/
def byDim (p : Profile) (d : Dimension) : PQForm → Choice := λ q => p (.of q d)

/-- A form's evidential and epistemic choices. -/
def pair (p : Profile) (q : PQForm) : Choice × Choice :=
  (p (.of q .evidential), p (.of q .epistemic))

/-- A principle relating the positive question's value to each negative question's value factors
through the positive question's value. -/
def formEquiv {X : Type*} (R : X → X → Prop) :
    {g : PQForm → X // R (g .PosQ) (g .LoNQ) ∧ R (g .PosQ) (g .HiNQ)} ≃
      Σ x : X, {y // R x y} × {y // R x y} where
  toFun g := ⟨g.1 .PosQ, ⟨g.1 .LoNQ, g.2.1⟩, ⟨g.1 .HiNQ, g.2.2⟩⟩
  invFun s :=
    ⟨λ q => match q with | .PosQ => s.1 | .LoNQ => s.2.1.1 | .HiNQ => s.2.2.1, s.2.1.2, s.2.2.2⟩
  left_inv g := Subtype.ext (funext λ q => by cases q <;> rfl)
  right_inv s := by rcases s with ⟨x, ⟨y, hy⟩, ⟨z, hz⟩⟩; rfl

theorem card_form {X : Type*} [Fintype X] [DecidableEq X] (R : X → X → Prop) [DecidableRel R] :
    Fintype.card {g : PQForm → X // R (g .PosQ) (g .LoNQ) ∧ R (g .PosQ) (g .HiNQ)} =
      ∑ x : X, Fintype.card {y // R x y} * Fintype.card {y // R x y} :=
  (Fintype.card_congr (formEquiv R)).trans (Fintype.card_sigma.trans (by simp [Fintype.card_prod]))

/-- Profiles as functions from dimensions to form triples. -/
def dimEquiv : Profile ≃ (Dimension → PQForm → Choice) where
  toFun p d q := p (.of q d)
  invFun f c := f c.dim c.form
  left_inv p := funext λ c => by cases c <;> rfl
  right_inv f := funext λ d => funext λ q => by cases d <;> cases q <;> rfl

/-- A principle imposed within each dimension counts as the square of the per-dimension count. -/
theorem card_perDim (Q : (PQForm → Choice) → Prop) [DecidablePred Q] :
    Fintype.card {p : Profile // ∀ d, Q (byDim p d)} = Fintype.card {g // Q g} ^ 2 :=
  (Fintype.card_congr ((Equiv.subtypeEquiv dimEquiv λ _ => Iff.rfl).trans
    (Equiv.subtypePiEquivPi (p := λ _ => Q)))).trans
    (Fintype.card_pi.trans (by simp only [Finset.prod_const, Finset.card_univ]; rfl))

/-- Profiles as functions from forms to pairs of choices. -/
def formsEquiv : Profile ≃ (PQForm → Choice × Choice) where
  toFun p q := pair p q
  invFun f c := match c.dim with | .evidential => (f c.form).1 | .epistemic => (f c.form).2
  left_inv p := funext λ c => by cases c <;> rfl
  right_inv f := funext λ q => by cases q <;> rfl

/-- A principle relating each negative question's pair of choices to the positive question's. -/
theorem card_byForm (R : Choice × Choice → Choice × Choice → Prop) [DecidableRel R] :
    Fintype.card {p : Profile //
        R (pair p .PosQ) (pair p .LoNQ) ∧ R (pair p .PosQ) (pair p .HiNQ)} =
      ∑ x : Choice × Choice, Fintype.card {y // R x y} * Fintype.card {y // R x y} :=
  (Fintype.card_congr (Equiv.subtypeEquiv formsEquiv λ _ => Iff.rfl)).trans (card_form R)

/-! ### The delimiting principles (section 2) -/

/-- Section 2.1, No Uniformity: not every cell makes the same choice. -/
abbrev NoUniformity (p : Profile) : Prop := ¬ ∃ x, ∀ c, p c = x

/-- The uniform profiles are the choices. -/
def uniformEquiv : Choice ≃ {p : Profile // ∃ x, ∀ c, p c = x} where
  toFun x := ⟨λ _ => x, x, λ _ => rfl⟩
  invFun p := p.1 .ppqEv
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨p, x, hx⟩ := p
    exact Subtype.ext (funext λ c => by simp only [hx c, hx .ppqEv])

theorem card_noUniformity : Fintype.card {p : Profile // NoUniformity p} = 117642 := by
  have h : Fintype.card {p : Profile // ∃ x, ∀ c, p c = x} +
      Fintype.card {p : Profile // NoUniformity p} = Fintype.card Profile := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl _)
  rw [card_profile, ← Fintype.card_congr uniformEquiv, card_choice] at h
  omega

/-- Section 2.2, PPQ ≠ NPQ: in each dimension, negation changes the bias. -/
abbrev PPQNeqNPQ (p : Profile) : Prop :=
  ∀ d, byDim p d .PosQ ≠ byDim p d .LoNQ ∧ byDim p d .PosQ ≠ byDim p d .HiNQ

theorem card_ppqNeqNpq : Fintype.card {p : Profile // PPQNeqNPQ p} = 63504 :=
  (card_perDim (λ g => g .PosQ ≠ g .LoNQ ∧ g .PosQ ≠ g .HiNQ)).trans
    (by rw [card_form (· ≠ ·)]; decide)

/-- Section 2.3.1, distributive Quantitative Markedness (11a): in each dimension the positive
question has at least as many options as each negative question. -/
abbrev MarkednessDistributive (p : Profile) : Prop :=
  ∀ d, (byDim p d .LoNQ).toFinset.card ≤ (byDim p d .PosQ).toFinset.card ∧
    (byDim p d .HiNQ).toFinset.card ≤ (byDim p d .PosQ).toFinset.card

theorem card_markednessDistributive :
    Fintype.card {p : Profile // MarkednessDistributive p} = 33856 :=
  (card_perDim (λ g => (g .LoNQ).toFinset.card ≤ (g .PosQ).toFinset.card ∧
    (g .HiNQ).toFinset.card ≤ (g .PosQ).toFinset.card)).trans
    (by rw [card_form (λ x y : Choice => y.toFinset.card ≤ x.toFinset.card)]; decide)

/-- The number of bias options a form has across both dimensions. -/
def size (h : Choice × Choice) : ℕ := h.1.toFinset.card + h.2.toFinset.card

/-- Section 2.3.1, collective Quantitative Markedness (11b): across both dimensions the positive
question has at least as many options as each negative question. -/
abbrev MarkednessCollective (p : Profile) : Prop :=
  size (pair p .LoNQ) ≤ size (pair p .PosQ) ∧ size (pair p .HiNQ) ≤ size (pair p .PosQ)

theorem card_markednessCollective :
    Fintype.card {p : Profile // MarkednessCollective p} = 56536 :=
  (card_byForm (λ x y => size y ≤ size x)).trans (by decide)

/-- Section 2.3.2, generalized Qualitative Markedness: the neutral value belongs to the positive
question's cells and to no negative question's cell. -/
abbrev QualitativeMarkedness : Profile → Prop :=
  Cellwise λ c x => (c.form = .PosQ → .neut ∈ x.toFinset) ∧ (c.form ≠ .PosQ → .neut ∉ x.toFinset)

theorem card_qualitativeMarkedness :
    Fintype.card {p : Profile // QualitativeMarkedness p} = 1296 :=
  (card_cellwise _).trans (by decide)

/-- Section 2.4, Avoid Disagreement: no negative value for a positive question, no positive value
for a negative one. -/
abbrev AvoidDisagreement : Profile → Prop :=
  Cellwise λ c x => (c.form = .PosQ → .neg ∉ x.toFinset) ∧ (c.form ≠ .PosQ → .pos ∉ x.toFinset)

theorem card_avoidDisagreement : Fintype.card {p : Profile // AvoidDisagreement p} = 729 :=
  (card_cellwise _).trans (by decide)

/-- Section 2.4, Don't Rule Out Agreement: every positive-question cell admits the positive value
and every negative-question cell the negative one. -/
abbrev DontRuleOutAgreement : Profile → Prop :=
  Cellwise λ c x => (c.form = .PosQ → .pos ∈ x.toFinset) ∧ (c.form ≠ .PosQ → .neg ∈ x.toFinset)

theorem card_dontRuleOutAgreement :
    Fintype.card {p : Profile // DontRuleOutAgreement p} = 4096 :=
  (card_cellwise _).trans (by decide)

/-- Section 2.5: a choice is convex when it does not skip the neutral value between the positive
and the negative one, that is, when it is not {+, −}. -/
abbrev Convex (x : Choice) : Prop := x ≠ .posNeg

/-- Section 2.5, Convexity: every cell is convex. -/
abbrev Convexity : Profile → Prop := Cellwise λ _ => Convex

theorem card_convexity : Fintype.card {p : Profile // Convexity p} = 46656 :=
  (card_cellwise _).trans (by decide)

/-- Section 2.6: the epistemic options the sample exhibits, {+} and {+, −, %}. -/
abbrev NarrowChoice (x : Choice) : Prop := x = .pos ∨ x = .all

/-- Section 2.6, Narrow Epistemic Choice: every epistemic cell is {+} or {+, −, %}. -/
abbrev NarrowEpistemic : Profile → Prop :=
  Cellwise λ c x => c.dim = .epistemic → NarrowChoice x

theorem card_narrowEpistemic : Fintype.card {p : Profile // NarrowEpistemic p} = 2744 :=
  (card_cellwise _).trans (by decide)

/-- Section 2.7, Static Complementarity: epistemic cells take the narrow options and evidential
cells the remaining ones. -/
abbrev StaticComplementarity : Profile → Prop :=
  Cellwise λ c x => (c.dim = .epistemic → NarrowChoice x) ∧ (c.dim ≠ .epistemic → ¬ NarrowChoice x)

theorem card_staticComplementarity_convexity :
    Fintype.card {p : Profile // StaticComplementarity p ∧ Convexity p} = 512 := by
  have h : ∀ p : Profile, StaticComplementarity p ∧ Convexity p ↔ Cellwise (λ c x =>
      ((c.dim = .epistemic → NarrowChoice x) ∧ (c.dim ≠ .epistemic → ¬ NarrowChoice x)) ∧
        Convex x) p :=
    λ p => (forall_and (α := Cell)).symm
  rw [Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) h), card_cellwise]
  decide

/-! ### Relations among the principles (section 3.1.2) -/

/-- Avoid Disagreement entails Convexity: a cell without one of the poles cannot be {+, −}. -/
theorem Convexity_of_avoidDisagreement {p : Profile} (h : AvoidDisagreement p) : Convexity p := by
  intro c hc
  obtain ⟨h₁, h₂⟩ := h c
  rw [hc] at h₁ h₂
  by_cases hq : c.form = .PosQ
  · exact h₁ hq (by decide)
  · exact h₂ hq (by decide)

/-- Narrow Epistemic Choice gives every negative question the positive epistemic value, which
Avoid Disagreement forbids; Polarity Match can only be meant evidentially. -/
theorem not_avoidDisagreement_of_narrowEpistemic {p : Profile} (h : NarrowEpistemic p) :
    ¬ AvoidDisagreement p := by
  intro had
  have h₁ := h .inEp rfl
  have h₂ := (had .inEp).2 (by decide)
  rcases h₁ with h₁ | h₁ <;> rw [h₁] at h₂ <;> exact h₂ (by decide)

/-! ### Appendix A: the sample -/

/-- A profile from its six cells, in the order positive, inside-negation, outside-negation question,
each evidential then epistemic. -/
def mk (ppqEv ppqEp inEv inEp onEv onEp : Choice) : Profile
  | .ppqEv => ppqEv
  | .ppqEp => ppqEp
  | .inEv => inEv
  | .inEp => inEp
  | .onEv => onEv
  | .onEp => onEp

/-- [1] English V1-interrogative ([sudo-2013]). -/
def englishV1 : Profile := mk .posNeut .all .neg .pos .negNeut .pos
/-- [2] Japanese ∅-interrogative ([sudo-2013]). -/
def japaneseNull : Profile := mk .neut .all .neg .all .posNeut .pos
/-- [3] Japanese *no*-interrogative ([sudo-2013]). -/
def japaneseNo : Profile := mk .pos .all .neg .pos .all .pos
/-- [4] Japanese *desho*-interrogative ([sudo-2013]). -/
def japaneseDesho : Profile := mk .all .pos .all .neg .negNeut .neg
/-- [5] Hungarian fall-rise interrogative ([gyuris-2017]). -/
def hungarianFallRise : Profile := mk .posNeut .all .neg .pos .negNeut .pos

/-- [6] Hungarian *e*-interrogative ([gyuris-2017]): it cannot express an inside-negation
question, so its profile is partial. -/
def hungarianE : Cell → Option Choice
  | .ppqEv => some .neut
  | .ppqEp => some .all
  | .inEv | .inEp => none
  | .onEv => some .neut
  | .onEp => some .pos

/-- The five total profiles of the sample. -/
def sample : List Profile :=
  [englishV1, japaneseNull, japaneseNo, japaneseDesho, hungarianFallRise]

/-- The Hungarian fall-rise interrogative shares the English profile. -/
theorem hungarianFallRise_eq_englishV1 : hungarianFallRise = englishV1 := rfl

private theorem mem_sample {p : Profile} (h : p ∈ sample) :
    p = englishV1 ∨ p = japaneseNull ∨ p = japaneseNo ∨ p = japaneseDesho ∨
      p = hungarianFallRise := by
  simpa [sample] using h

/-- No Uniformity and collective Quantitative Markedness hold throughout the sample. -/
theorem sample_noUniformity_markednessCollective :
    ∀ p ∈ sample, NoUniformity p ∧ MarkednessCollective p := by
  intro p hp; rcases mem_sample hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Distributive Quantitative Markedness fails for the Japanese ∅- and *no*-interrogatives, whose
outside-negation questions have more evidential options than their positive questions. -/
theorem sample_markednessDistributive :
    ∀ p ∈ sample, MarkednessDistributive p ↔ p ≠ japaneseNull ∧ p ≠ japaneseNo := by
  intro p hp; rcases mem_sample hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- PPQ ≠ NPQ fails within the sample for the Japanese ∅- and *desho*-interrogatives, whose
inside-negation question shares a choice with the positive question, and the paper's own
counterexample is the Hungarian *e*-interrogative, whose positive and outside-negation questions
share the evidential anti-bias {%}. -/
theorem sample_ppqNeqNpq :
    (∀ p ∈ sample, PPQNeqNPQ p ↔ p ≠ japaneseNull ∧ p ≠ japaneseDesho) ∧
      hungarianE .ppqEv = hungarianE .onEv :=
  ⟨λ p hp => by rcases mem_sample hp with rfl | rfl | rfl | rfl | rfl <;> decide, rfl⟩

/-- Avoid Disagreement fails throughout the sample, while Don't Rule Out Agreement holds only for
the *desho*-interrogative. -/
theorem sample_polarityMatch :
    ∀ p ∈ sample, ¬ AvoidDisagreement p ∧ (DontRuleOutAgreement p ↔ p = japaneseDesho) := by
  intro p hp; rcases mem_sample hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Convexity holds throughout the sample; Narrow Epistemic Choice fails only for the
*desho*-interrogative, whose negative questions carry {−}. -/
theorem sample_convexity_narrowEpistemic :
    ∀ p ∈ sample, Convexity p ∧ (NarrowEpistemic p ↔ p ≠ japaneseDesho) := by
  intro p hp; rcases mem_sample hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Static Complementarity fails exactly for the Japanese *no*- and *desho*-interrogatives, the six
violations of (26). -/
theorem sample_staticComplementarity :
    ∀ p ∈ sample, StaticComplementarity p ↔ p ≠ japaneseNo ∧ p ≠ japaneseDesho := by
  intro p hp; rcases mem_sample hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### Examples (1), (2), (8), (9): infelicity from the profiles -/

/-- The clause types whose examples the paper judges. -/
inductive Construction where
  | englishV1
  | hungarianE
  deriving DecidableEq

/-- A clause type's choice for a cell. -/
def Construction.cell : Construction → Cell → Option Choice
  | .englishV1, c => some (GartnerGyuris2017.englishV1 c)
  | .hungarianE, c => GartnerGyuris2017.hungarianE c

/-- An example: the clause type, the question it expresses, and the bias value the scenario fixes
in one dimension, with the judgment. -/
structure Row where
  construction : Construction
  form : PQForm
  dimension : Dimension
  value : Bias
  judgment : Judgment
  deriving DecidableEq

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let construction ← ex.parse? "construction"
    [("English V1", .englishV1), ("Hungarian e", .hungarianE)]
  let form ← ex.parse? "form" [("PPQ", .PosQ), ("IN-NPQ", .LoNQ), ("ON-NPQ", .HiNQ)]
  let dimension ← ex.parse? "dimension" [("evidential", .evidential), ("epistemic", .epistemic)]
  let value ← ex.parse? "value" [("+", .pos), ("-", .neg), ("%", .neut)]
  pure ⟨construction, form, dimension, value, ex.judgment⟩

/-- The judged examples (1), (2a), (2b), (8), (9a), (9b). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

example : rows.length = Examples.all.length := by decide

/-- An example is felicitous exactly when the scenario's bias value is among the clause type's
options for that cell: the judgments follow from the profiles. -/
theorem rows_felicity :
    ∀ r ∈ rows, r.judgment = .acceptable ↔
      ∃ x ∈ r.construction.cell (.of r.form r.dimension), r.value ∈ x.toFinset := by
  decide

end GartnerGyuris2017
