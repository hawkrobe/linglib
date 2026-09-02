import Linglib.Pragmatics.Expressives.Basic
import Linglib.Logic.Modal.Defs
import Linglib.Semantics.Conditionals.SelectionFunction
import Mathlib.Logic.Function.Basic

/-!
# Kirk-Giannini 2024: Covert mixed quotation

Mixed quotation arises compositionally from pure quotation and a phonologically null operator
𝔐 with two meanings, both saturated by its pure-quoted sister `q`: the at-issue ⦇q⦈(w_c)(s_x),
the extension of `q` as uttered by the anaphorically retrieved speaker `s_x` at the world of
the context ([shan-2010]'s quotative interpretation function ⦇∗⦈), and the peripheral
R(s_x, u_x, q), that `s_x` produced the utterance `u_x` of `q` ([potts-2005]'s second
dimension, as [potts-2007a] uses it for quotation). Three further covert items combine with
it: ↓ shunts the peripheral proposition into the at-issue dimension, † diagonalizes ⦇∗⦈ so
that `q` means at a world `w` what `s_x` would mean by it there, and 𝔄 is the appropriateness
modal ⧫ applied to 𝔐's peripheral proposition. Covert 𝔐 then accounts for non-projecting CI
items (26″), c-monsters (29, [kocurek-jerzak-rudolph-2020]'s Pluto data), metalinguistic
negation (3, [horn-1989]), metalinguistic negotiation (6, [plunkett-sundell-2013]'s Secretariat
dispute) and 'in a sense' (7′).

`Model` interprets ⦇∗⦈, R and the accessibility relation of ⧫ in the appendix's intended model,
with the output type of ⦇∗⦈ fixed to propositions; `mq`, `shunt`, `approp` and `Model.dagger`
are the four covert items on `TwoDimProp`, † being `Function.extend`, so that
`Model.exists_dagger_iff` identifies the paper's footnote-22 assumption with
`Function.FactorsThrough`; `appropAssertion` and `metaNeg` are the forms ↓[… 𝔄𝔐q …] and its
negation, whose at-issue content `metaNeg_atIssue_iff` gives as ¬p ∨ ¬⧫R. Parsetrees and the
tree admissibility conditions are not represented, each rule appearing as the operator it
licenses.

## References

* [C. D. Kirk-Giannini, *Covert Mixed Quotation* (2024)][kirk-giannini-2024]
* [C. Shan, *The character of quotation* (2010)][shan-2010]
* [C. Potts, *The Logic of Conventional Implicatures* (2005)][potts-2005]
* [C. Potts, *The dimensions of quotation* (2007)][potts-2007a]
* [E. McCready, *Varieties of conventional implicature* (2010)][mccready-2010]
* [A. W. Kocurek, E. Jerzak and R. E. Rudolph, *Against conventional wisdom*
  (2020)][kocurek-jerzak-rudolph-2020]
* [L. R. Horn, *A Natural History of Negation* (1989)][horn-1989]
* [D. Plunkett and T. Sundell, *Disagreement and the semantics of normative and evaluative
  terms* (2013)][plunkett-sundell-2013]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
-/

namespace KirkGiannini2024

open Pragmatics.Expressives (TwoDimProp)
open Function (FactorsThrough)
open scoped ModalLogic

/-- The constants of ℒ_MQ interpreted in the intended model. -/
structure Model (W Expr Speaker Utt : Type*) where
  /-- ⦇∗⦈: `quot q w₁ s` is the intension contributed by an utterance of `q` by `s` at `w₁`. -/
  quot : Expr → W → Speaker → W → Prop
  /-- R: `utter s u q w` iff `s` produces the utterance `u` of `q` at `w`. -/
  utter : Speaker → Utt → Expr → W → Prop
  /-- Accessibility of ⧫, `□[M.appropriate]`: `appropriate w v` iff `v` is among the worlds
  characterizing what is or would be appropriate at `w`. -/
  appropriate : W → W → Prop

variable {W Expr Speaker Utt : Type*} (M : Model W Expr Speaker Utt) (wc : W) (sx : Speaker)
  (ux : Utt)

namespace Model

/-! ### Diagonalization -/

/-- 𝔐's at-issue meaning `λq.⦇q⦈(w_c)(s)` as a function of the speaker `s`. -/
def mqAtIssue (s : Speaker) : Expr → W → Prop := λ q => M.quot q wc s

/-- ⦇∗⦈∗: `M.diag s q w` is the extension at `w` of `q` as uttered by `s` at `w`. -/
def diag (s : Speaker) : Expr → W → Prop := λ q w => M.quot q w s w

/-- At the world of the context diagonalization is invisible, so (Conventional Wisdom) holds
for unembedded material. -/
theorem mqAtIssue_wc (s : Speaker) (q : Expr) : M.mqAtIssue wc s q wc = M.diag s q wc := rfl

/-- † ⇝ `λf | ∃s. f = λq.⦇q⦈(w_c)(s). f∗`: ⦇∗⦈∗ extended along 𝔐's at-issue meaning. The
paper leaves † undefined off that domain; `Function.extend` returns `⊥` there. -/
noncomputable def dagger : (Expr → W → Prop) → Expr → W → Prop :=
  Function.extend (M.mqAtIssue wc) M.diag ⊥

/-- The paper's footnote-22 assumption: no two speakers agree on the intensions of all
expressions at `w_c` while differing on some at another world. Under it † returns ⦇∗⦈∗ of
the speaker whose meaning it was given. -/
theorem dagger_mqAtIssue (h : FactorsThrough M.diag (M.mqAtIssue wc)) (s : Speaker) :
    M.dagger wc (M.mqAtIssue wc s) = M.diag s :=
  h.extend_apply _ s

/-- The assumption is also necessary: some function sends each `λq.⦇q⦈(w_c)(s)` to ⦇∗⦈∗(s)
iff ⦇∗⦈∗ factors through 𝔐's at-issue meaning. -/
theorem exists_dagger_iff :
    (∃ d : (Expr → W → Prop) → Expr → W → Prop, ∀ s, d (M.mqAtIssue wc s) = M.diag s) ↔
      FactorsThrough M.diag (M.mqAtIssue wc) := by
  rw [Function.factorsThrough_iff]
  exact exists_congr λ d => ⟨λ h => (funext h).symm, λ h s => (congrFun h s).symm⟩

end Model

/-! ### The covert lexicon on two-dimensional meanings -/

/-- 𝔐 ⇝ `λq.⦇q⦈(w_c)(s_x) • λq.R(s_x, u_x, q)`, both saturated by the pure-quoted sister `q`
(a-to-p Shunting). -/
def mq (q : Expr) : TwoDimProp W := ⟨M.quot q wc sx, M.utter sx ux q⟩

/-- ↓ ⇝ `λp.p̌` with p-to-a Shunting ([mccready-2010]): the peripheral proposition is conjoined
with the at-issue one, and the single peripheral dimension is then empty. -/
def shunt (p : TwoDimProp W) : TwoDimProp W := ⟨p.atIssue ⊓ p.ci, ⊤⟩

/-- 𝔄 ⇝ ⧫ with Peripheral Intensional Function Application: the peripheral proposition is
replaced by ⧫ of its intension, the at-issue meaning passing up unchanged. -/
def approp (p : TwoDimProp W) : TwoDimProp W := ⟨p.atIssue, □[M.appropriate] p.ci⟩

/-- †𝔐: † applied to 𝔐's at-issue meaning, the peripheral meaning passing up unchanged. -/
noncomputable def daggerMQ (q : Expr) : TwoDimProp W :=
  ⟨M.dagger wc (M.mqAtIssue wc sx) q, M.utter sx ux q⟩

@[simp] theorem mq_atIssue (q : Expr) (w : W) :
    (mq M wc sx ux q).atIssue w ↔ M.quot q wc sx w := Iff.rfl

@[simp] theorem mq_ci (q : Expr) (w : W) : (mq M wc sx ux q).ci w ↔ M.utter sx ux q w := Iff.rfl

@[simp] theorem shunt_atIssue (p : TwoDimProp W) (w : W) :
    (shunt p).atIssue w ↔ p.atIssue w ∧ p.ci w := Iff.rfl

@[simp] theorem shunt_ci (p : TwoDimProp W) (w : W) : (shunt p).ci w := trivial

@[simp] theorem approp_atIssue (p : TwoDimProp W) (w : W) :
    (approp M p).atIssue w ↔ p.atIssue w := Iff.rfl

@[simp] theorem approp_ci (p : TwoDimProp W) (w : W) :
    (approp M p).ci w ↔ □[M.appropriate] p.ci w := Iff.rfl

theorem daggerMQ_atIssue (h : FactorsThrough M.diag (M.mqAtIssue wc)) (q : Expr) :
    (daggerMQ M wc sx ux q).atIssue = M.diag sx q :=
  congrFun (M.dagger_mqAtIssue wc h sx) q

/-- (10′) and (12): ↓ at the clause boundary makes 'Peter orders ‘[eI]pricots’' say that Peter
orders apricots and utters ‘[eI]pricots’ in so doing, available to a higher quantifier or
conditional. -/
theorem shunt_mq_atIssue (q : Expr) (w : W) :
    (shunt (mq M wc sx ux q)).atIssue w ↔ M.quot q wc sx w ∧ M.utter sx ux q w := Iff.rfl

/-! ### Conventional implicature items (§3) -/

/-- (26) and (26″): a speech report `F` of a CI item `q` whose meaning is `lex q`, whose
peripheral content projects unquoted (`TwoDimProp.mapAtIssue_ci`) but, 𝔪-quoted, is replaced by
the attribution R(s_x, u_x, q) while the at-issue content is unchanged, given that ⦇∗⦈ returns
only at-issue content. -/
theorem report_mq (lex : Expr → TwoDimProp W) (F : (W → Prop) → W → Prop) (q : Expr)
    (h : M.quot q wc sx = (lex q).atIssue) :
    (TwoDimProp.mapAtIssue F (mq M wc sx ux q)).atIssue =
        (TwoDimProp.mapAtIssue F (lex q)).atIssue ∧
      (TwoDimProp.mapAtIssue F (mq M wc sx ux q)).ci = M.utter sx ux q :=
  ⟨congrArg F h, rfl⟩

/-! ### C-monsters (§4) -/

/-- (29) 'If Pluto were a planet, …' with †𝔐 around 'planet': the antecedent contributes the
diagonal ⦇'planet'⦈∗(s_x), so a [stalnaker-1968] selection function takes the conditional to
the nearest world whose conventions for 'planet', as `s_x` would use it there, include
Pluto. -/
theorem selectionConditional_daggerMQ (h : FactorsThrough M.diag (M.mqAtIssue wc))
    (s : Conditionals.SelectionFunction W) (q : Expr) (C : W → Prop) (w : W) :
    Conditionals.selectionConditional s (daggerMQ M wc sx ux q).atIssue C w ↔
      C (s.sel w {v | M.quot q v sx v}) := by
  rw [daggerMQ_atIssue M wc sx ux h]; rfl

/-! ### Metalinguistic negation and negotiation (§5–6) -/

/-- ↓[… 𝔄𝔐q …]: the quoted clause conjoined with the appropriateness of `q`'s verbatim use.
A's assertion in (6), the antecedent of (35″), the prejacent of (36). -/
def appropAssertion (q : Expr) : TwoDimProp W := shunt (approp M (mq M wc sx ux q))

/-- not ↓[… 𝔄𝔐q …]: metalinguistic negation, (3), and B's denial in (6). -/
def metaNeg (q : Expr) : TwoDimProp W := TwoDimProp.neg (appropAssertion M wc sx ux q)

theorem appropAssertion_atIssue (q : Expr) (w : W) :
    (appropAssertion M wc sx ux q).atIssue w ↔
      M.quot q wc sx w ∧ □[M.appropriate] (M.utter sx ux q) w := Iff.rfl

theorem metaNeg_atIssue (q : Expr) (w : W) :
    (metaNeg M wc sx ux q).atIssue w ↔
      ¬ (M.quot q wc sx w ∧ □[M.appropriate] (M.utter sx ux q) w) := Iff.rfl

/-- (3) is true iff the quoted clause fails or its verbatim use is inappropriate. -/
theorem metaNeg_atIssue_iff (q : Expr) (w : W) :
    (metaNeg M wc sx ux q).atIssue w ↔
      ¬ M.quot q wc sx w ∨ ¬ □[M.appropriate] (M.utter sx ux q) w := not_and_or

/-- B's utterance in (6) expresses the negation of A's, the retrieved speaker and utterance
being the same: the disputants' contents are incompatible. -/
theorem metaNeg_atIssue_iff_not (q : Expr) (w : W) :
    (metaNeg M wc sx ux q).atIssue w ↔ ¬ (appropAssertion M wc sx ux q).atIssue w := Iff.rfl

/-- The correction in (3): its second clause `q'` ('mongooses') expresses in the mouth of
`s_x` what `q` ('mongeese') does, so together with it the first clause entails that using `q`
is not appropriate. -/
theorem metaNeg_correction {q q' : Expr} {w : W} (h : M.quot q wc sx = M.quot q' wc sx)
    (h₁ : (metaNeg M wc sx ux q).atIssue w) (h₂ : (mq M wc sx ux q').atIssue w) :
    ¬ □[M.appropriate] (M.utter sx ux q) w :=
  λ hb => h₁ ⟨by simpa [h] using h₂, hb⟩

/-- Whenever verbatim use of `q` is inappropriate, (3)'s form is true whatever the quoted
clause's truth value: (37) 'She's not happy' can be said of someone ecstatic, whereas (38)
'She's unhappy', whose negation is incorporated below the covert material, cannot. -/
theorem metaNeg_of_not_box {q : Expr} {w : W} (hb : ¬ □[M.appropriate] (M.utter sx ux q) w) :
    (metaNeg M wc sx ux q).atIssue w :=
  λ h => hb h.2

/-- (41) 'She's not not happy' with 'not happy' 𝔪-quoted says that she is happy or that
'not happy' is inappropriate, so (42) 'She's happy' does not follow: double negation is not
eliminated. -/
theorem metaNeg_compl {q q₀ : Expr} {w : W} (h : M.quot q wc sx = (M.quot q₀ wc sx)ᶜ) :
    (metaNeg M wc sx ux q).atIssue w ↔
      M.quot q₀ wc sx w ∨ ¬ □[M.appropriate] (M.utter sx ux q) w := by
  simp [metaNeg_atIssue_iff, h]

/-- (6) with its uncontroversial at-issue content granted: A asserts that characterizing
Secretariat with 'athlete' is appropriate. -/
theorem appropAssertion_atIssue_iff_box {q : Expr} {w : W} (hp : M.quot q wc sx w) :
    (appropAssertion M wc sx ux q).atIssue w ↔ □[M.appropriate] (M.utter sx ux q) w := by
  simp [appropAssertion_atIssue, hp]

/-- (6) with its uncontroversial at-issue content granted: B denies that characterizing
Secretariat with 'athlete' is appropriate. -/
theorem metaNeg_atIssue_iff_not_box {q : Expr} {w : W} (hp : M.quot q wc sx w) :
    (metaNeg M wc sx ux q).atIssue w ↔ ¬ □[M.appropriate] (M.utter sx ux q) w := by
  simp [metaNeg_atIssue, hp]

/-! ### 'In a sense' (§7) -/

/-- 'In The Sense That', (43): `⌜𝔪S𝔪 in the sense that S′⌝` with `μ` the intension of `S′` is
`∃s_x[⦇S⦈(w_c)(s_x) ∧ [^⦇S⦈(w_c)(s_x)] = μ]`, which as a predicate of `μ` is the relative
clause of (7′). -/
def inTheSenseThat (q : Expr) (μ : W → Prop) (w : W) : Prop :=
  ∃ s, M.quot q wc s w ∧ M.quot q wc s = μ

/-- (7′) 'There is a sense which viruses are alive in': `∃μ∃s_x[…]`. -/
def inASense (q : Expr) (w : W) : Prop := ∃ μ, inTheSenseThat M wc q μ w

theorem inTheSenseThat_iff (q : Expr) (μ : W → Prop) (w : W) :
    inTheSenseThat M wc q μ w ↔ μ w ∧ ∃ s, M.quot q wc s = μ :=
  ⟨λ ⟨s, hs, hμ⟩ => ⟨hμ ▸ hs, s, hμ⟩, λ ⟨hμ, s, hs⟩ => ⟨s, hs ▸ hμ, hs⟩⟩

/-- (7′) is true iff some speaker's use of the sentence at `w_c` expresses a truth at `w`; the
paper restricts the speakers quantified over to not-too-outlandish ones. -/
theorem inASense_iff (q : Expr) (w : W) : inASense M wc q w ↔ ∃ s, M.quot q wc s w :=
  ⟨λ ⟨_, s, hs, _⟩ => ⟨s, hs⟩, λ ⟨s, hs⟩ => ⟨_, s, hs, rfl⟩⟩

end KirkGiannini2024
