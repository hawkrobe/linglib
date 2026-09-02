import Linglib.Pragmatics.Expressives.Basic
import Linglib.Logic.Modal.Defs
import Linglib.Semantics.Conditionals.SelectionFunction
import Mathlib.Logic.Function.Basic

/-!
# Kirk-Giannini 2024: Covert mixed quotation

Mixed quotation arises compositionally from pure quotation and a phonologically null operator
𝔐 with two meanings, saturated by its pure-quoted sister `q`: the at-issue `λq.⦇q⦈(w_c)(s_x)`,
the extension of `q` as uttered by the anaphorically retrieved speaker `s_x` at the world of
the context ([shan-2010]'s quotative interpretation function ⦇∗⦈), and the peripheral
`λq.R(s_x, u_x, q)`, that `s_x` produced the utterance `u_x` of `q` ([potts-2005]'s second
dimension, as [potts-2007a] uses it for quotation). Covert mixed quotation is covert pure
quotation composed with 𝔐. Three further covert items combine with it: ↓ shunts the
peripheral proposition into the at-issue dimension, † diagonalizes ⦇∗⦈ so that `q` means at a
world `w` what `s_x` would mean by it at `w`, and 𝔄 is the appropriateness modal ⧫ applied to
𝔐's peripheral proposition. The five applications are stated on the paper's own logical
forms: (26″) non-projecting CI items, (29) c-monsters ([kocurek-jerzak-rudolph-2020]'s Pluto
data), (3) metalinguistic negation ([horn-1989]), (6) metalinguistic negotiation
([plunkett-sundell-2013]'s Secretariat dispute), and (7′) 'in a sense'.

The model is the appendix's intended model with the output type χ of ⦇∗⦈ fixed to
propositions, so a quoted item stands for the clause it contributes; parsetrees and the tree
admissibility conditions are not represented, each rule appearing as the operator it licenses.

## Main definitions

* `Model` — the constants ⦇∗⦈, R and the accessibility relation of ⧫.
* `mq`, `shunt`, `approp`, `Model.dagger` — the covert items 𝔐, ↓, 𝔄, †.
* `appropAssertion`, `metaNeg` — the forms ↓[… 𝔄𝔐q …] and not ↓[… 𝔄𝔐q …] of (6) and (3).
* `inTheSenseThat`, `inASense` — quantification into 𝔐 for (43) and (7′).

## Main results

* `Model.dagger_mqAtIssue`, `Model.exists_dagger_iff` — † is well defined on 𝔐's at-issue
  meanings exactly under the paper's footnote-22 assumption, `Function.FactorsThrough`.
* `metaNeg_correction`, `metaNeg_of_not_box`, `metaNeg_compl` — (3) entails that 'mongeese'
  is inappropriate; the contrasts (37)/(38) and (41)/(42).
* `metaNeg_atIssue_iff_not`, `negotiation` — B's denial in (6) negates A's assertion.
* `inASense_iff` — (7′) holds iff some speaker's use of the sentence expresses a truth.

## Comparisons the paper draws

* [maier-2014a]'s single type-polymorphic mixed-quotation operator is replaced by pure
  quotation plus 𝔐; that the quoted material is first pure-quoted is what eliminates its
  peripheral content (`report_mq`).
* [harris-potts-2009]'s free orientation variable on CI items leaves the default of speaker
  orientation unexplained and forces non-propositional CI content into a propositional mould.
* [kocurek-jerzak-rudolph-2020]'s world/convention pairs are not needed: † yields their Pluto
  readings while (Conventional Wisdom) holds for unembedded material (`Model.mqAtIssue_wc`).
* [horn-1989] and [potts-2007a] make negation ambiguous; here it is univocal, the
  metalinguistic reading coming from covert 𝔄𝔐 material in its scope. The restrictions of
  [horn-1985] and [burton-roberts-1989] follow: (38) incorporated negation cannot scope over
  that material, (40) an NPI breaks the verbatim requirement R imposes on the retrieved
  utterance, (42) double negation does not eliminate.
* [plunkett-sundell-2013] hold that the disputants in (6) express consistent contents; on the
  present analysis B's content is the negation of A's.

## References

* [C. D. Kirk-Giannini, *Covert Mixed Quotation* (2024)][kirk-giannini-2024]
* [C. Shan, *The character of quotation* (2010)][shan-2010]
* [C. Potts, *The Logic of Conventional Implicatures* (2005)][potts-2005]
* [C. Potts, *The dimensions of quotation* (2007)][potts-2007a]
* [E. McCready, *Varieties of conventional implicature* (2010)][mccready-2010]
* [E. Maier, *Mixed quotation: The grammar of apparently transparent opacity* (2014)][maier-2014a]
* [J. A. Harris and C. Potts, *Perspective-shifting with appositives and expressives*
  (2009)][harris-potts-2009]
* [A. W. Kocurek, E. Jerzak and R. E. Rudolph, *Against conventional wisdom*
  (2020)][kocurek-jerzak-rudolph-2020]
* [L. R. Horn, *Metalinguistic negation and pragmatic ambiguity* (1985)][horn-1985]
* [L. R. Horn, *A Natural History of Negation* (1989)][horn-1989]
* [N. Burton-Roberts, *On Horn's dilemma: Presupposition and negation*
  (1989)][burton-roberts-1989]
* [D. Plunkett and T. Sundell, *Disagreement and the semantics of normative and evaluative
  terms* (2013)][plunkett-sundell-2013]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
-/

namespace KirkGiannini2024

open Pragmatics.Expressives (TwoDimProp)
open Function (FactorsThrough)

/-- The constants of ℒ_MQ interpreted in the intended model. -/
structure Model (W Expr Speaker Utt : Type*) where
  /-- ⦇∗⦈: `quot q w₁ s` is the intension contributed by an utterance of `q` by `s` at `w₁`. -/
  quot : Expr → W → Speaker → W → Prop
  /-- R: `utter s u q w` iff `s` produces the utterance `u` of `q` at `w`. -/
  utter : Speaker → Utt → Expr → W → Prop
  /-- Accessibility of ⧫: `appropriate w v` iff `v` is among the worlds characterizing what is
  or would be appropriate at `w`. -/
  appropriate : W → W → Prop

variable {W Expr Speaker Utt : Type*} (M : Model W Expr Speaker Utt) (wc : W) (sx : Speaker)
  (ux : Utt)

namespace Model

/-- ⧫: `M.box p w` iff `p` holds at every world appropriate at `w`. -/
abbrev box : (W → Prop) → W → Prop := ModalLogic.box M.appropriate

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
def approp (p : TwoDimProp W) : TwoDimProp W := ⟨p.atIssue, M.box p.ci⟩

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

@[simp] theorem approp_ci (p : TwoDimProp W) (w : W) : (approp M p).ci w ↔ M.box p.ci w :=
  Iff.rfl

theorem daggerMQ_atIssue (h : FactorsThrough M.diag (M.mqAtIssue wc)) (q : Expr) :
    (daggerMQ M wc sx ux q).atIssue = M.diag sx q :=
  congrFun (M.dagger_mqAtIssue wc h sx) q

/-- (10′) and (12): ↓ at the clause boundary makes 'Peter orders ‘[eI]pricots’' say that Peter
orders apricots and utters ‘[eI]pricots’ in so doing, available to a higher quantifier or
conditional. -/
theorem shunt_mq_atIssue (q : Expr) (w : W) :
    (shunt (mq M wc sx ux q)).atIssue w ↔ M.quot q wc sx w ∧ M.utter sx ux q w := Iff.rfl

/-! ### Conventional implicature items (paper §3) -/

/-- (26) and (26″): a speech report `F` of a CI item `q` whose meaning is `lex q`. Unquoted, the
report's peripheral content is the item's own CI ([potts-2005]'s projection,
`TwoDimProp.mapAtIssue_ci`). 𝔪-quoted, pure quotation has eliminated that content, so the
report has the same at-issue content, given that ⦇∗⦈ returns only at-issue content, but its
peripheral content is the attribution R(s_x, u_x, q): Jones, not the speaker, is understood to
have the attitude. -/
theorem report_mq (lex : Expr → TwoDimProp W) (F : (W → Prop) → W → Prop) (q : Expr)
    (h : M.quot q wc sx = (lex q).atIssue) :
    (TwoDimProp.mapAtIssue F (mq M wc sx ux q)).atIssue =
        (TwoDimProp.mapAtIssue F (lex q)).atIssue ∧
      (TwoDimProp.mapAtIssue F (mq M wc sx ux q)).ci = M.utter sx ux q :=
  ⟨congrArg F h, rfl⟩

/-! ### C-monsters (paper §4) -/

/-- (29) 'If Pluto were a planet, …' with †𝔐 around 'planet': the antecedent contributes the
diagonal ⦇'planet'⦈∗(s_x), so a [stalnaker-1968] selection function takes the conditional to
the nearest world whose conventions for 'planet', as `s_x` would use it there, include
Pluto. -/
theorem selectionConditional_daggerMQ (h : FactorsThrough M.diag (M.mqAtIssue wc))
    (s : Conditionals.SelectionFunction W) (q : Expr) (C : W → Prop) (w : W) :
    Conditionals.selectionConditional s (daggerMQ M wc sx ux q).atIssue C w ↔
      C (s.sel w {v | M.quot q v sx v}) := by
  rw [daggerMQ_atIssue M wc sx ux h]; rfl

/-! ### Metalinguistic negation and negotiation (paper §5, §6) -/

/-- ↓[… 𝔄𝔐q …]: the quoted clause conjoined with the appropriateness of `q`'s verbatim use.
A's assertion in (6), the antecedent of (35″), the prejacent of (36). -/
def appropAssertion (q : Expr) : TwoDimProp W := shunt (approp M (mq M wc sx ux q))

/-- not ↓[… 𝔄𝔐q …]: metalinguistic negation, (3), and B's denial in (6). -/
def metaNeg (q : Expr) : TwoDimProp W := TwoDimProp.neg (appropAssertion M wc sx ux q)

theorem appropAssertion_atIssue (q : Expr) (w : W) :
    (appropAssertion M wc sx ux q).atIssue w ↔
      M.quot q wc sx w ∧ M.box (M.utter sx ux q) w := Iff.rfl

/-- (3) is true iff it is not the case that the quoted clause holds and its verbatim use is
appropriate. -/
theorem metaNeg_atIssue (q : Expr) (w : W) :
    (metaNeg M wc sx ux q).atIssue w ↔
      ¬ (M.quot q wc sx w ∧ M.box (M.utter sx ux q) w) := Iff.rfl

theorem metaNeg_atIssue_iff (q : Expr) (w : W) :
    (metaNeg M wc sx ux q).atIssue w ↔
      ¬ M.quot q wc sx w ∨ ¬ M.box (M.utter sx ux q) w := not_and_or

/-- B's utterance in (6) expresses the negation of A's, the retrieved speaker and utterance
being the same: the disputants' contents are incompatible. -/
theorem metaNeg_atIssue_iff_not (q : Expr) (w : W) :
    (metaNeg M wc sx ux q).atIssue w ↔ ¬ (appropAssertion M wc sx ux q).atIssue w := Iff.rfl

/-- The correction in (3): its second clause `q'` ('mongooses') expresses in the mouth of
`s_x` what `q` ('mongeese') does, so together with it the first clause entails that using `q`
is not appropriate. -/
theorem metaNeg_correction {q q' : Expr} {w : W} (h : M.quot q wc sx = M.quot q' wc sx)
    (h₁ : (metaNeg M wc sx ux q).atIssue w) (h₂ : (mq M wc sx ux q').atIssue w) :
    ¬ M.box (M.utter sx ux q) w :=
  λ hb => h₁ ⟨by simpa [h] using h₂, hb⟩

/-- Whenever verbatim use of `q` is inappropriate, (3)'s form is true whatever the quoted
clause's truth value: (37) 'She's not happy' can be said of someone ecstatic, whereas (38)
'She's unhappy', whose negation is incorporated below the covert material, cannot. -/
theorem metaNeg_of_not_box {q : Expr} {w : W} (hb : ¬ M.box (M.utter sx ux q) w) :
    (metaNeg M wc sx ux q).atIssue w :=
  λ h => hb h.2

/-- (41) 'She's not not happy' with 'not happy' 𝔪-quoted says that she is happy or that
'not happy' is inappropriate, so (42) 'She's happy' does not follow: double negation is not
eliminated. -/
theorem metaNeg_compl {q q₀ : Expr} {w : W} (h : M.quot q wc sx = (M.quot q₀ wc sx)ᶜ) :
    (metaNeg M wc sx ux q).atIssue w ↔
      M.quot q₀ wc sx w ∨ ¬ M.box (M.utter sx ux q) w := by
  simp [metaNeg_atIssue_iff, h]

/-- (6) with its uncontroversial at-issue content granted: A asserts, and B denies, that
characterizing Secretariat with 'athlete' is appropriate. -/
theorem negotiation {q : Expr} {w : W} (hp : M.quot q wc sx w) :
    ((appropAssertion M wc sx ux q).atIssue w ↔ M.box (M.utter sx ux q) w) ∧
      ((metaNeg M wc sx ux q).atIssue w ↔ ¬ M.box (M.utter sx ux q) w) := by
  simp [appropAssertion_atIssue, metaNeg_atIssue, hp]

/-! ### 'In a sense' (paper §7) -/

/-- 'In The Sense That': `⌜𝔪S𝔪 in the sense that S′⌝` with `μ` the intension of `S′` is
`∃s_x[⦇S⦈(w_c)(s_x) ∧ [^⦇S⦈(w_c)(s_x)] = μ]`, (43). As a predicate of `μ` it is the relative
clause of (7′), the abstraction `which_μ` introduces. The rule eliminates 𝔐's peripheral
content. -/
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
