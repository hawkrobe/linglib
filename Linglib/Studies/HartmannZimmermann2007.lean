import Linglib.Fragments.Hausa.Focus
import Linglib.Fragments.Hausa.TAM
import Linglib.Core.Logic.FactorsThroughOn
import Linglib.Semantics.Focus.Interpretation
import Linglib.Data.Examples.HartmannZimmermann2007

/-!
# Hausa focus strategies and pragmatic types

Formalises the [hartmann-zimmermann-2007] argument that Hausa is a
counterexample to the universalist claims that focus marking is
obligatory and that focus position determines pragmatic
interpretation.

## Main definitions

* `PragType`: four pragmatic uses of focus (§1.2, 1a–d), after
  [uhmann-1991].
* `FocusControl`: what the preceding context supplies — question,
  prior assertion, explicit alternatives, or parallel focus; `PragType`
  is the image of `FocusControl.pragType`, and `FocusControl.Admits`
  is Roothian `fip` on the control's contrast set. Each matrix cell is
  built from its context's Hamblin model (`control22`–`control8`), so
  its pragmatic type is computed, not stipulated.
* `Focused`: subject vs nonSubject classification.
* `FocusUtterance`: a `FocusConfig` with pragmatic-use and
  focused-constituent tags.
* `FocusUtterance.IsHausaLicensed`: `FocusConfig.Licensed` plus the
  §2.2.2 ban on in-situ subject focus.
* `FocusUtterance.HasMorphosyntacticReflex`: overt reflex of focus —
  non-vacuous fronting, Relative-form morphology, or a stabilizer.
* `hzMatrix`: the 8-cell empirical matrix of §3.2.
* `UniversalBFR`: universalist Basic Focus Rule, instantiated at Hausa.

## Main results

* `strategy_does_not_determine_pragType`: `pragType` does not factor
  through `cfg.strategy` on Hausa-licensed utterances — the paper's
  refutation of its (21) "Meaning-Structure Mapping Hypothesis"; the
  same schema is *satisfied* for Hungarian in `Kiss1998.lean`.
* `pragType_not_factorsThrough_contrastSet`: distinct pragmatic uses
  can supply the same contrast set — the four-way split is invisible
  to the semantics, cashing out §1.2's "pragmatic uses of one semantic
  focus"; `controls_admit` shows the same Roothian felicity holds
  across all four uses in the matrix's own models.
* `strategy_underdetermines_pragType_inSitu`: the refutation persists
  restricted to in-situ utterances.
* `subject_focus_only_exSitu`: subject focus requires the ex-situ
  strategy (§2.2.2).
* `hausa_falsifies_UniversalBFR`: in-situ new-info utterances carry no
  morphosyntactic reflex; `exSitu_subject_subjunctive_no_reflex` is a
  second, subject-side counterexample ((8)).
* `cells_match_rows`: every cell's tags agree with the `paperFeatures`
  of its `Data.Examples.HartmannZimmermann2007` row.

## Implementation notes

The paper states the hypothesis it refutes as (21) "Meaning-Structure
Mapping Hypothesis" (§3.1), the label following
[vallduvi-vilkuna-1998]'s phrase "the meaning-structure mapping"; the
shared schema is `Function.FactorsThroughOn`
(`Core.Logic.FactorsThroughOn`), making the Hungarian/Hausa contrast
a difference of verdict on a single set-theoretic predicate.

Subject foci in TAMs lacking a Relative form (future, habitual,
subjunctive) are "syntactically and morphologically unmarked" (p. 4);
the paper analyses them as string-vacuously ex-situ, so
`IsHausaLicensed` bans in-situ subjects unconditionally and
`exSitu_subject_subjunctive` is licensed yet reflex-free.

§3.3's corpus tendencies stay prose: answers to *wh*-questions are
mostly in-situ (99 vs 25) while selective/corrective/contrastive foci
are >90% ex-situ (154 vs 12), but "none of the discussed instances of
focus is categorically excluded from occurring either in situ or ex
situ" — only the categorical no-determination claim is a theorem.

## TODO

* §3.2.5 exhaustivity contrast against Kiss 1998 requires an
  alternatives-semantics exhaustivity operator beyond `PragType` tags.
* §2.3 multiple foci: co-occurrence of one ex-situ focus with in-situ
  foci (18a-c).
* §4 focus pied-piping / partial focus movement and the (47) "Ex-Situ
  Generalisation, final version" need a structured-meaning overlap
  predicate.
* §5 prosodic pilot data and §6.1 emphasis motivation are quantitative
  tendencies, currently in docstring prose only.

## References

* [hartmann-zimmermann-2007], [newman-2000], [uhmann-1991],
  [selkirk-1995], [vallduvi-vilkuna-1998].
-/

namespace HartmannZimmermann2007

open Hausa
open Semantics.Focus.Interpretation (fip PropFocusValue qaCongruentWeak)

/-! ## Pragmatic focus types (§1.2) -/

/-- The four pragmatic uses of one Roothian semantic focus (§1.2, 1a–d;
after [uhmann-1991]): the image of `FocusControl.pragType`. The §3.2.5
*exhaustive* case is deferred to a real exhaustivity operator. -/
inductive PragType where
  | newInfo      -- (1a) Q/A new-information focus
  | corrective   -- (1b) correction of prior assertion
  | selective    -- (1c) selection from explicit alternatives
  | contrastive  -- (1d) parallel contrast across utterances
  deriving DecidableEq, Repr, Inhabited

/-! ## Focus control (§1.2)

The four uses are distinguished by what the preceding context supplies
("the context controls the focus", after [uhmann-1991]); the
contrast-set machinery is `Semantics.Focus.Interpretation`. -/

variable {W : Type*}

/-- A focus-controlling context (§1.2): the discourse object that
supplies the contrast set. -/
inductive FocusControl (W : Type*) where
  /-- (1a) A *wh*-question with denotation `q`. -/
  | question (q : PropFocusValue W)
  /-- (1b) A prior assertion `p` corrected among alternatives `alts`. -/
  | assertion (p : Set W) (alts : PropFocusValue W)
  /-- (1c) Explicitly offered alternatives. -/
  | alternatives (alts : PropFocusValue W)
  /-- (1d) A parallel focus with focus value `alts`. -/
  | parallel (alts : PropFocusValue W)

/-- The contrast set Γ a control supplies to the squiggle. -/
def FocusControl.contrastSet : FocusControl W → PropFocusValue W
  | .question q       => q
  | .assertion _ alts => alts
  | .alternatives alts => alts
  | .parallel alts    => alts

/-- The pragmatic use a control shape licenses. -/
def FocusControl.pragType : FocusControl W → PragType
  | .question _     => .newInfo
  | .assertion _ _  => .corrective
  | .alternatives _ => .selective
  | .parallel _     => .contrastive

/-- Roothian felicity of a focus value against a control: `fip` on the
control's contrast set. -/
def FocusControl.Admits (c : FocusControl W) (fv : PropFocusValue W) : Prop :=
  fip c.contrastSet fv

/-- The (1a) case is the substrate's Q-A congruence. -/
theorem question_admits_iff (q fv : PropFocusValue W) :
    (FocusControl.question q).Admits fv ↔ qaCongruentWeak fv q := Iff.rfl

/-- The Hamblin set of complete answers over a domain `D`. -/
def hamblin (D : Type*) : PropFocusValue D := Set.range fun d => ({d} : Set D)

/-- A *wh*-question control: the context supplies the full Hamblin set. -/
def whControl (D : Type*) : FocusControl D := .question (hamblin D)

theorem whControl_admits (D : Type*) : (whControl D).Admits (hamblin D) :=
  subset_rfl

/-- Felicity factors through the contrast set: the semantics sees Γ,
never the pragmatic label. -/
theorem admits_factorsThrough_contrastSet (fv : PropFocusValue W) :
    Function.FactorsThrough (FocusControl.Admits · fv)
      (FocusControl.contrastSet (W := W)) :=
  fun _ _ h => congrArg (fip · fv) h

/-- Distinct pragmatic uses can supply one and the same Γ, so the
four-way split is invisible to the Roothian semantics — pragmatic, not
semantic (§1.2). Concretely: a *wh*-question and an explicit offer
('Coffee or tea?', `control30`) can supply the same contrast set while
licensing newInfo vs selective uses. -/
theorem pragType_not_factorsThrough_contrastSet :
    ¬ Function.FactorsThrough (FocusControl.pragType (W := W))
        FocusControl.contrastSet :=
  fun h => absurd (h (a := .question ∅) (b := .alternatives ∅) rfl)
    (by simp [FocusControl.pragType])

/-! ## What is focused (§2.2.2) -/

/-- What is focused: Hausa singles out subjects (§2.2.2); everything
else collapses to `nonSubject`. -/
inductive Focused where
  | subject
  | nonSubject
  deriving DecidableEq, Repr, Inhabited

/-! ## Tagged focus utterances and Hausa licensing -/

/-- A `FocusConfig` tagged with its pragmatic use and focused
constituent. -/
structure FocusUtterance where
  cfg      : FocusConfig
  pragType : PragType
  focused  : Focused
  deriving Repr

/-- Morphosyntactic licensing (`FocusConfig.Licensed`) plus the §2.2.2
ban on in-situ subject focus. The ban is unconditional: in TAMs without
a Relative form the fronting is merely invisible (p. 4), not absent. -/
def FocusUtterance.IsHausaLicensed (u : FocusUtterance) : Prop :=
  u.cfg.Licensed ∧ (u.focused = .subject → u.cfg.strategy = .exSitu)

instance (u : FocusUtterance) : Decidable u.IsHausaLicensed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Controlling contexts of the §3.2 matrix

One small answer domain per Q/A pair (`other` stands in for the
unmentioned rest of open *wh*-domains); each control carries the
context's actual Hamblin denotation. -/

inductive Dish | kiifii | other
inductive City | birninKwanni | other
inductive Deceased | wife | mother
inductive Price | fifteen | twenty
inductive Route | front | behind
inductive Activity | eating | chatting
inductive Amount | whole | half
inductive Drink | tea | coffee
inductive Caller | daudaa | other
inductive Traveler | audu | other

/-- 'What is Kande cooking?' ((22)). -/
def control22 : FocusControl Dish := whControl Dish
/-- 'From which city do you come?' ((23)). -/
def control23 : FocusControl City := whControl City
/-- 'Was it his mother who died?' — asserted alternative to correct ((24)). -/
def control24 : FocusControl Deceased :=
  .assertion {Deceased.mother} (hamblin Deceased)
/-- 'It is twenty Naira that you will pay' — assertion to correct ((25)). -/
def control25 : FocusControl Price :=
  .assertion {Price.twenty} (hamblin Price)
/-- '…you shouldn't pass in front of him' — parallel focus ((26)). -/
def control26 : FocusControl Route := .parallel (hamblin Route)
/-- 'no one is chatting…' — parallel focus ((27)). -/
def control27 : FocusControl Activity := .parallel (hamblin Activity)
/-- 'A whole or a half?' — explicitly offered alternatives ((29)). -/
def control29 : FocusControl Amount := .alternatives (hamblin Amount)
/-- 'Coffee or tea?' — explicitly offered alternatives ((30)). -/
def control30 : FocusControl Drink := .alternatives (hamblin Drink)
/-- 'Who is calling her?' ((17)). -/
def control17 : FocusControl Caller := whControl Caller
/-- 'Who will go to Germany?' ((8)). -/
def control8 : FocusControl Traveler := whControl Traveler

/-- Roothian felicity holds uniformly: every §3.2 control admits its
answer's focus value. One semantics, four pragmatic uses. -/
theorem controls_admit :
    control22.Admits (hamblin Dish) ∧ control23.Admits (hamblin City) ∧
    control24.Admits (hamblin Deceased) ∧ control25.Admits (hamblin Price) ∧
    control26.Admits (hamblin Route) ∧ control27.Admits (hamblin Activity) ∧
    control29.Admits (hamblin Amount) ∧ control30.Admits (hamblin Drink) :=
  ⟨subset_rfl, subset_rfl, subset_rfl, subset_rfl,
   subset_rfl, subset_rfl, subset_rfl, subset_rfl⟩

/-- (25) is a real correction: the answer's ordinary value lies in the
contrast set and differs from the asserted alternative. -/
theorem ex25_corrects :
    ({Price.fifteen} : Set Price) ∈ control25.contrastSet ∧
    ({Price.fifteen} : Set Price) ≠ {Price.twenty} :=
  ⟨⟨Price.fifteen, rfl⟩, by simp⟩

/-- (26) is a real parallel contrast: 'in front' and 'behind' are
distinct members of one contrast set. -/
theorem ex26_parallel_contrast :
    ({Route.front} : Set Route) ∈ control26.contrastSet ∧
    ({Route.behind} : Set Route) ∈ control26.contrastSet ∧
    ({Route.front} : Set Route) ≠ {Route.behind} :=
  ⟨⟨Route.front, rfl⟩, ⟨Route.behind, rfl⟩, by simp⟩

/-! ## The 8-cell empirical matrix (§3.2)

Each cell's pragmatic type is *computed* from its controlling context:
the constructors take a `FocusControl`, not a tag. -/

private def mkExSituUtt (pac : PAC) (g : Gender) (sg hasStab : Bool)
    (h : pac.tam.HasRelativeForm → pac.mode = .relative)
    {W : Type*} (ctl : FocusControl W) (foc : Focused := .nonSubject) :
    FocusUtterance :=
  ⟨mkExSitu pac g sg h hasStab, ctl.pragType, foc⟩

private def mkInSituUtt (pac : PAC) (g : Gender) (sg : Bool)
    {W : Type*} (ctl : FocusControl W) (foc : Focused := .nonSubject)
    (hasStab : Bool := false) :
    FocusUtterance :=
  ⟨mkInSitu pac g sg hasStab, ctl.pragType, foc⟩

/-- Ex-situ new-information focus ((22), `Examples.ex22`). -/
def exSitu_newInfo : FocusUtterance :=
  mkExSituUtt cont_3sf_R .masculine true true (fun _ => rfl) control22

/-- Ex-situ corrective focus on a feminine subject ((24),
`Examples.ex24`). -/
def exSitu_corrective : FocusUtterance :=
  mkExSituUtt cmp_3sf_R .feminine true true (fun _ => rfl) control24 .subject

/-- Ex-situ selective focus, no stabilizer ((29), `Examples.ex29`). -/
def exSitu_selective : FocusUtterance :=
  mkExSituUtt cont_1sg_R .masculine true false (fun _ => rfl) control29

/-- Ex-situ contrastive focus, no stabilizer ((27), `Examples.ex27`);
the paper's 4sg impersonal *akèe* is approximated with the 3sg.M
Relative continuous. -/
def exSitu_contrastive : FocusUtterance :=
  mkExSituUtt cont_3sm_R .masculine true false (fun _ => rfl) control27

/-- In-situ new-information focus ((23), `Examples.ex23`). -/
def inSitu_newInfo : FocusUtterance := mkInSituUtt cmp_1sg_G .masculine true control23

/-- In-situ corrective focus with sentence-final *nèe* ((25),
`Examples.ex25`). -/
def inSitu_corrective : FocusUtterance :=
  mkInSituUtt fut_1sg .masculine true control25 (hasStab := true)

/-- In-situ selective focus ((30), `Examples.ex30`). -/
def inSitu_selective : FocusUtterance := mkInSituUtt fut_1sg .masculine true control30

/-- In-situ contrastive focus ((26), `Examples.ex26`). -/
def inSitu_contrastive : FocusUtterance := mkInSituUtt fut_1sg .masculine true control26

/-- The 8-cell matrix of §3.2: both strategies × all four pragmatic
types. -/
def hzMatrix : List FocusUtterance :=
  [exSitu_newInfo, exSitu_corrective, exSitu_selective, exSitu_contrastive,
   inSitu_newInfo, inSitu_corrective, inSitu_selective, inSitu_contrastive]

/-- Every cell of the §3.2 matrix is Hausa-licensed. -/
theorem all_hzMatrix_IsHausaLicensed :
    ∀ u ∈ hzMatrix, u.IsHausaLicensed := by decide

/-! ## Strategy does not determine pragmatic type (§3.2) -/

/-- On Hausa-licensed utterances `pragType` does not factor through
strategy: (22) and (24) are both ex-situ with distinct pragmatic
types. -/
theorem strategy_does_not_determine_pragType :
    ¬ Function.FactorsThroughOn
        FocusUtterance.pragType
        (fun u : FocusUtterance => u.cfg.strategy)
        {u | u.IsHausaLicensed} := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨exSitu_newInfo, exSitu_corrective,
    by decide, by decide, rfl, by decide⟩

/-- The refutation persists restricted to in-situ utterances: (23) vs
(25). -/
theorem strategy_underdetermines_pragType_inSitu :
    ¬ Function.FactorsThroughOn
        FocusUtterance.pragType
        (fun u : FocusUtterance => u.cfg.strategy)
        {u | u.IsHausaLicensed ∧ u.cfg.strategy = .inSitu} := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨inSitu_newInfo, inSitu_corrective,
    by decide, by decide, rfl, by decide⟩

/-! ## Subject-focus generalization (§2.2.2) -/

/-- Focused subjects front (§2.2.2); unpacks the second conjunct of
`IsHausaLicensed`. -/
theorem subject_focus_only_exSitu (u : FocusUtterance)
    (h : u.IsHausaLicensed) (hSubj : u.focused = .subject) :
    u.cfg.strategy = .exSitu := h.2 hSubj

/-- The starred in-situ subject focus ((17 A2), `Examples.ex17a2`). -/
def starred_inSitu_subject : FocusUtterance :=
  mkInSituUtt cont_3sm_G .masculine true control17 .subject

theorem starred_inSitu_subject_not_IsHausaLicensed :
    ¬ starred_inSitu_subject.IsHausaLicensed := by decide

/-- The grammatical ex-situ subject focus ((17 A1), `Examples.ex17a1`). -/
def licensed_exSitu_subject : FocusUtterance :=
  mkExSituUtt cont_3sm_R .masculine true true (fun _ => rfl) control17 .subject

theorem licensed_exSitu_subject_IsHausaLicensed :
    licensed_exSitu_subject.IsHausaLicensed := by decide

/-- Subject focus in a TAM with no Relative form (the (8) pattern,
`Examples.ex8`): string-vacuous fronting with no overt reflex — see
`exSitu_subject_subjunctive_no_reflex`. -/
def exSitu_subject_subjunctive : FocusUtterance :=
  mkExSituUtt subj_3sm .masculine true false (by decide) control8 .subject

theorem exSitu_subject_subjunctive_IsHausaLicensed :
    exSitu_subject_subjunctive.IsHausaLicensed := by decide

/-! ## Universalist Basic Focus Rule (§5, §6.2) -/

/-- An overt reflex of focus: non-vacuous fronting (subjects front
string-vacuously), Relative-form morphology, or a stabilizer. -/
def FocusUtterance.HasMorphosyntacticReflex (u : FocusUtterance) : Prop :=
  (u.focused = .nonSubject ∧ u.cfg.strategy = .exSitu) ∨
    u.cfg.pac.mode = .relative ∨ u.cfg.hasStab = true

instance (u : FocusUtterance) : Decidable u.HasMorphosyntacticReflex :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ _ ∨ _))

/-- The universalist claim — [selkirk-1995]'s Basic Focus Rule and its
tradition (§5, §6.2) — that every focused utterance carries some
structural reflex, weakened to morphosyntax and quantified over Hausa
utterances only. -/
def UniversalBFR : Prop :=
  ∀ u : FocusUtterance, u.IsHausaLicensed → u.HasMorphosyntacticReflex

/-- (23) is licensed and reflex-free; the §5 pilot finds no prosodic
reflex either. -/
theorem hausa_falsifies_UniversalBFR : ¬ UniversalBFR :=
  fun h => absurd (h inSitu_newInfo (by decide)) (by decide)

/-- The subject-side counterexample (the (8) pattern). -/
theorem exSitu_subject_subjunctive_no_reflex :
    ¬ exSitu_subject_subjunctive.HasMorphosyntacticReflex := by decide

/-! ## Polar tone of *nē/cē* (§2.1)

`Stabilizer.toneAfter` is `Hausa.polarOf`; the minimal pair below is
(3a, 3b). -/

/-- (3a): host *Kandè* ends low, the stabilizer surfaces high. -/
example : Stabilizer.cee.toneAfter .L = .H := rfl

/-- (3b): host *Kiifii* ends high, the stabilizer surfaces low. -/
example : Stabilizer.nee.toneAfter .H = .L := rfl

/-! ## Data linkage

Each cell's tags are pinned to the `paperFeatures` of its
`Data.Examples.HartmannZimmermann2007` row. -/

private def strategyLabel : Strategy → String
  | .inSitu => "inSitu"
  | .exSitu => "exSitu"

private def pragLabel : PragType → String
  | .newInfo => "newInfo"
  | .corrective => "corrective"
  | .selective => "selective"
  | .contrastive => "contrastive"

private def focusedLabel : Focused → String
  | .subject => "subject"
  | .nonSubject => "nonSubject"

private def stabLabel (c : FocusConfig) : String :=
  match c.stab? with
  | some .nee => "nee"
  | some .cee => "cee"
  | none      => "none"

private def cellRows :
    List (FocusUtterance × Data.Examples.LinguisticExample) :=
  [(exSitu_newInfo, Examples.ex22), (exSitu_corrective, Examples.ex24),
   (exSitu_selective, Examples.ex29), (exSitu_contrastive, Examples.ex27),
   (inSitu_newInfo, Examples.ex23), (inSitu_corrective, Examples.ex25),
   (inSitu_selective, Examples.ex30), (inSitu_contrastive, Examples.ex26),
   (starred_inSitu_subject, Examples.ex17a2),
   (licensed_exSitu_subject, Examples.ex17a1)]

/-- Every cell's tags agree with its row's `paperFeatures`. -/
theorem cells_match_rows :
    ∀ p ∈ cellRows,
      p.2.feature? "strategy" = some (strategyLabel p.1.cfg.strategy) ∧
      p.2.feature? "pragType" = some (pragLabel p.1.pragType) ∧
      p.2.feature? "focused" = some (focusedLabel p.1.focused) ∧
      p.2.feature? "stabilizer" = some (stabLabel p.1.cfg) := by decide

/-- The row the paper stars is the cell the licensing predicate
rejects. -/
theorem starred_row_is_the_unlicensed_cell :
    Examples.ex17a2.judgment = .unacceptable ∧
    ¬ starred_inSitu_subject.IsHausaLicensed := ⟨rfl, by decide⟩

end HartmannZimmermann2007
