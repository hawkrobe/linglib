import Linglib.Fragments.Hausa.Focus
import Linglib.Fragments.Hausa.TAM
import Linglib.Core.Logic.FactorsThroughOn

/-!
# Hausa focus strategies and pragmatic types

Formalises the [hartmann-zimmermann-2007] argument that Hausa is a
counterexample to the universalist claims that focus marking is
obligatory and that focus position determines pragmatic
interpretation.

## Main definitions

* `PragType`: four pragmatic uses of focus (new-info, corrective,
  selective, contrastive), paper §1.2 / eq. (1a-d), after
  [uhmann-1991].
* `Focused`: subject vs nonSubject classification.
* `FocusUtterance`: bundles `FocusConfig`, `PragType`, and `Focused`.
* `FocusUtterance.IsHausaLicensed`: morphosyntactic licensing plus
  the §2.2.2 subject-focus generalization (subjects cannot be
  focused in-situ).
* `FocusUtterance.HasMorphosyntacticReflex`: overt reflex of focus —
  non-vacuous fronting, Relative-form morphology, or a stabilizer.
* `hzMatrix`: the 8-cell empirical matrix from paper §3.2.
* `UniversalBFR`: universalist Basic Focus Rule (morphosyntactic
  reflex required on every focus), instantiated at Hausa.

## Main results

* `all_hzMatrix_IsHausaLicensed`: every cell of the 8-cell matrix is
  Hausa-licensed.
* `strategy_does_not_determine_pragType`: `pragType` does not factor
  through `cfg.strategy` on Hausa-licensed utterances — the paper's
  refutation of its (21) "Meaning-Structure Mapping Hypothesis". The
  same factor-through schema (`Function.FactorsThroughOn`) is
  *satisfied* for Hungarian in `Kiss1998.lean` with
  `position`/`focusType`.
* `strategy_underdetermines_pragType_inSitu`: the refutation persists
  restricted to in-situ utterances.
* `subject_focus_only_exSitu`: subject focus requires the ex-situ
  strategy (paper §2.2.2).
* `hausa_falsifies_UniversalBFR`: in-situ new-info utterances carry
  no morphosyntactic reflex, refuting the universalist BFR;
  `exSitu_subject_subjunctive_no_reflex` is a second, subject-side
  counterexample (paper §2.1, eq. 8).

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

## TODO

* §3.2.5 exhaustivity contrast against Kiss 1998 requires an
  alternatives-semantics exhaustivity operator beyond `PragType` tags.
* §2.3 multiple foci: co-occurrence of one ex-situ focus with in-situ
  foci (eq. 18a-c).
* §4 focus pied-piping / partial focus movement and the eq. (47)
  "Ex-Situ Generalisation, final version" need a structured-meaning
  overlap predicate.
* §5 prosodic pilot data and §6.1 emphasis motivation are
  quantitative tendencies, currently in docstring prose only.

## References

* [hartmann-zimmermann-2007], [newman-2000], [uhmann-1991],
  [selkirk-1995], [vallduvi-vilkuna-1998].
-/

namespace HartmannZimmermann2007

open Hausa.Focus
open Hausa.Inflection
  (PAC cmp_3sf_R cmp_1sg_G cont_3sm_R cont_3sm_G cont_3sf_R cont_1sg_R
   fut_1sg subj_3sm)

/-! ## Pragmatic focus types (paper §1.2, after [uhmann-1991]) -/

/-- The four pragmatic uses of focus distinguished in
    [hartmann-zimmermann-2007] §1.2 (eq. 1a–d), built on a single
    Roothian alternative-set semantics. The paper emphasises that these
    are *pragmatic* uses of one *semantic* focus, not distinct semantic
    types — so the type carries no semantic load, only a label for
    discourse role. The §3.2.5 *exhaustive* case is omitted: it would
    require an alternatives-semantics exhaustivity projection to be
    load-bearing rather than a tag. -/
inductive PragType where
  | newInfo      -- (1a) Q/A new-information focus
  | corrective   -- (1b) correction of prior assertion
  | selective    -- (1c) selection from explicit alternatives
  | contrastive  -- (1d) parallel contrast across utterances
  deriving DecidableEq, Repr, Inhabited

/-! ## What is focused (paper §2.2.2) -/

/-- A coarse classification of the focused constituent. Hausa singles
    out *subjects* as the cell where in-situ focus is unavailable
    (paper §2.2.2); everything else (object, adverbial, predicate,
    clause) collapses to `nonSubject`. -/
inductive Focused where
  | subject
  | nonSubject
  deriving DecidableEq, Repr, Inhabited

/-! ## Tagged focus utterances and Hausa licensing -/

/-- A *focus utterance* bundles a `FocusConfig` (morphosyntax, from
    `Fragments/Hausa/Focus.lean`) with its pragmatic interpretation and
    a tag for what the focused constituent is. The Focus Fragment is
    deliberately agnostic about pragmatic type and constituent identity;
    this study file is where those tags get attached to specific
    paper examples. -/
structure FocusUtterance where
  cfg      : FocusConfig
  pragType : PragType
  focused  : Focused
  deriving Repr

/-- A focus utterance is **Hausa-licensed** iff it satisfies *both* the
    morphosyntactic licensing condition (`FocusConfig.Licensed`,
    encoding the relative-TAM requirement on ex-situ focus) *and* the
    [hartmann-zimmermann-2007] §2.2.2 subject-focus generalization:
    "subjects cannot be realised in situ". The ban is unconditional —
    in TAMs without a Relative form the fronting is merely invisible
    ("subject foci are syntactically and morphologically unmarked in
    the future, habitual and subjunctive aspects", p. 4), not absent. -/
def FocusUtterance.IsHausaLicensed (u : FocusUtterance) : Prop :=
  u.cfg.Licensed ∧ (u.focused = .subject → u.cfg.strategy = .exSitu)

instance (u : FocusUtterance) : Decidable u.IsHausaLicensed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The 8-cell empirical matrix (paper §3.2)

Ex-situ × all four pragmatic types, then in-situ × all four. -/

/-- Smart constructor for an ex-situ focus utterance. The proof
    obligation `pac.tam.HasRelativeForm → pac.mode = .relative` is
    threaded explicitly (no tactic default); `hasStab` records whether
    the example's stabilizer actually surfaces. -/
private def mkExSituUtt (pac : PAC) (g : Gender) (sg hasStab : Bool)
    (h : pac.tam.HasRelativeForm → pac.mode = .relative)
    (pT : PragType) (foc : Focused := .nonSubject) :
    FocusUtterance :=
  ⟨mkExSitu pac g sg h hasStab, pT, foc⟩

/-- Smart constructor for an in-situ focus utterance. -/
private def mkInSituUtt (pac : PAC) (g : Gender) (sg : Bool)
    (pT : PragType) (foc : Focused := .nonSubject)
    (hasStab : Bool := false) :
    FocusUtterance :=
  ⟨mkInSitu pac g sg hasStab, pT, foc⟩

/-- Ex-situ + new-information focus (paper eq. 22):
    *Kiifii nèe Kandè takèe dafàawaa* 'Kande is cooking the FISH.'
    PAC: 3sg.F Relative continuous *takèe* (subject-marker for *Kande*);
    the stabilizer *nèe* surfaces. -/
def exSitu_newInfo : FocusUtterance :=
  mkExSituUtt cont_3sf_R .masculine true true (fun _ => rfl) .newInfo

/-- Ex-situ + corrective focus on a feminine subject (paper eq. 24):
    *màatar̃-sa cèe ta mutù* 'No, it was HIS WIFE who died.'
    PAC: 3sg.F Relative completive *ta*; the stabilizer *cèe*
    surfaces. -/
def exSitu_corrective : FocusUtterance :=
  mkExSituUtt cmp_3sf_R .feminine true true (fun _ => rfl) .corrective .subject

/-- Ex-situ + selective focus (paper eq. 29):
    *Gùdaa nakèe sô!* 'I want a WHOLE.' No stabilizer surfaces.
    PAC: 1sg Relative continuous *nakèe* — the paper's gloss reads
    "1sg.rel.perf", an apparent erratum: the *kèe* formative is the
    Relative continuous (cf. eq. 16, 22, 27). -/
def exSitu_selective : FocusUtterance :=
  mkExSituUtt cont_1sg_R .masculine true false (fun _ => rfl) .selective

/-- Ex-situ + contrastive focus (paper eq. 27):
    *cî kawài akèe ta yî* 'it is only EATING that is going on.'
    No stabilizer surfaces; the exhaustive flavour comes from *kawài*
    'only'. Approximated with the 3sg.M Relative continuous *yakèe* —
    the paper's *akèe* is the 4sg impersonal, which `Person.Category`
    does not yet expose. -/
def exSitu_contrastive : FocusUtterance :=
  mkExSituUtt cont_3sm_R .masculine true false (fun _ => rfl) .contrastive

/-- In-situ + new-information focus (paper eq. 23):
    *Naa tahoo dàgà Bir̃nin Ƙwànni* 'I came from BIRNIN KONNI.'
    PAC: 1sg General completive *naa*. -/
def inSitu_newInfo : FocusUtterance := mkInSituUtt cmp_1sg_G .masculine true .newInfo

/-- In-situ + corrective focus (paper eq. 25):
    *zân biyaa shâ bìyar̃ nèe* 'No, I will pay FIFTEEN.'
    PAC: 1sg future *zân* (no G/R contrast); the stabilizer *nèe*
    surfaces sentence-finally — an in-situ focus with a particle but
    no fronting and no Relative morphology. -/
def inSitu_corrective : FocusUtterance :=
  mkInSituUtt fut_1sg .masculine true .corrective (hasStab := true)

/-- In-situ + selective focus (paper eq. 30):
    *Zân shaa shaayìi* 'I will drink TEA.'
    PAC: 1sg future *zân*. -/
def inSitu_selective : FocusUtterance := mkInSituUtt fut_1sg .masculine true .selective

/-- In-situ + contrastive focus (paper eq. 26):
    *Tô, zân iyà bî ta baayansà?* 'Alright, but can I pass BEHIND
    him?' — B's reply, whose *baayansà* 'behind him' contrasts with A's
    *ta gàbansà* 'in front of him'. PAC: 1sg future *zân*. -/
def inSitu_contrastive : FocusUtterance := mkInSituUtt fut_1sg .masculine true .contrastive

/-- The 8-cell empirical matrix from paper §3.2. Every cell is
    Hausa-licensed; together they witness `strategy_does_not_determine_pragType`
    below. -/
def hzMatrix : List FocusUtterance :=
  [exSitu_newInfo, exSitu_corrective, exSitu_selective, exSitu_contrastive,
   inSitu_newInfo, inSitu_corrective, inSitu_selective, inSitu_contrastive]

/-- **Every cell of the H&Z matrix is Hausa-licensed.** Both strategies
    attest each pragmatic type; the only subject-focus cell
    (`exSitu_corrective`, eq. 24) is ex-situ, consistent with the
    §2.2.2 generalization. -/
theorem all_hzMatrix_IsHausaLicensed :
    ∀ u ∈ hzMatrix, u.IsHausaLicensed := by decide

/-! ## Strategy does not determine pragmatic type (paper §3.2)

The 8-cell matrix witnesses that, on Hausa-licensed utterances,
`pragType` does *not* factor through `cfg.strategy`. The same
factor-through schema (`Function.FactorsThroughOn`) is *satisfied*
for Hungarian in `Kiss1998.lean` with `position`/`focusType`.

The failure is categorical, not statistical: §3.3's corpus counts
find clear tendencies — answers to *wh*-questions are mostly in-situ
(99 vs 25), while selective/corrective/contrastive foci are >90%
ex-situ (154 vs 12) — but "none of the discussed instances of focus
is categorically excluded from occurring either in situ or ex situ".
Only the categorical claim is a theorem; the tendencies stay prose. -/

/-- Hausa-licensed utterances do not exhibit a factor-through from
strategy to pragmatic type: `exSitu_newInfo` (eq. 22) and
`exSitu_corrective` (eq. 24) are both ex-situ but have distinct
pragmatic types. -/
theorem strategy_does_not_determine_pragType :
    ¬ Function.FactorsThroughOn
        FocusUtterance.pragType
        (fun u : FocusUtterance => u.cfg.strategy)
        {u | u.IsHausaLicensed} := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨exSitu_newInfo, exSitu_corrective,
    by decide, by decide, rfl, by decide⟩

/-- The refutation persists on the in-situ restriction:
`inSitu_newInfo` (eq. 23) and `inSitu_corrective` (eq. 25) are both
in-situ but have distinct pragmatic types. -/
theorem strategy_underdetermines_pragType_inSitu :
    ¬ Function.FactorsThroughOn
        FocusUtterance.pragType
        (fun u : FocusUtterance => u.cfg.strategy)
        {u | u.IsHausaLicensed ∧ u.cfg.strategy = .inSitu} := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨inSitu_newInfo, inSitu_corrective,
    by decide, by decide, rfl, by decide⟩

/-! ## Subject-focus generalization (paper §2.2.2) -/

/-- **Subject-focus generalization** (paper §2.2.2): focused subjects
    cannot stay in-situ; the auxiliary appears in the Relative form
    where the TAM has one, indicating (string-vacuous) movement. The
    theorem unpacks the second conjunct of `IsHausaLicensed`. -/
theorem subject_focus_only_exSitu (u : FocusUtterance)
    (h : u.IsHausaLicensed) (hSubj : u.focused = .subject) :
    u.cfg.strategy = .exSitu := h.2 hSubj

/-- The paper's ungrammatical in-situ subject focus (§2.2.2, eq. 17 A2):
    *\*Daudàa ya-nàa kirà-ntà* — 3sg.M subject with the General
    continuous *yanàa*. -/
def starred_inSitu_subject : FocusUtterance :=
  mkInSituUtt cont_3sm_G .masculine true .newInfo .subject

/-- **The starred in-situ subject focus is not Hausa-licensed.** Its
    morphosyntactic licensing succeeds (in-situ is vacuously licensed
    by `FocusConfig.Licensed`) but the subject-focus conjunct fails. -/
theorem starred_inSitu_subject_not_IsHausaLicensed :
    ¬ starred_inSitu_subject.IsHausaLicensed := by decide

/-- The paper's grammatical ex-situ subject focus (§2.2.2, eq. 17 A1):
    *Daudàa (nee) ya-kèe kirà-ntà*. PAC: 3sg.M Relative continuous
    *yakèe*; the optional stabilizer surfaces. -/
def licensed_exSitu_subject : FocusUtterance :=
  mkExSituUtt cont_3sm_R .masculine true true (fun _ => rfl) .newInfo .subject

/-- **The grammatical ex-situ subject focus IS Hausa-licensed.** The
    minimal pair with `starred_inSitu_subject` is the empirical content
    of the §2.2.2 generalization. -/
theorem licensed_exSitu_subject_IsHausaLicensed :
    licensed_exSitu_subject.IsHausaLicensed := by decide

/-- **Subject focus in a TAM without a Relative form is licensed but
    unmarked** (paper §2.1, eq. 8 for the future): "subject foci are
    syntactically and morphologically unmarked in the future, habitual
    and subjunctive aspects" (p. 4). The fronting is string-vacuous and
    the subjunctive has no Relative form to shift to, so nothing overt
    betrays the focus — see `exSitu_subject_subjunctive_no_reflex`. -/
def exSitu_subject_subjunctive : FocusUtterance :=
  mkExSituUtt subj_3sm .masculine true false (by decide) .newInfo .subject

theorem exSitu_subject_subjunctive_IsHausaLicensed :
    exSitu_subject_subjunctive.IsHausaLicensed := by decide

/-! ## Universalist Basic Focus Rule (paper §5, §6.2) -/

/-- A focus utterance carries an **overt morphosyntactic reflex of
    focus** iff it fronts a non-subject (subject fronting is
    string-vacuous: subjects are clause-initial in the base order, so
    only the auxiliary can betray movement), surfaces Relative-form
    morphology, or surfaces a stabilizer. -/
def FocusUtterance.HasMorphosyntacticReflex (u : FocusUtterance) : Prop :=
  (u.focused = .nonSubject ∧ u.cfg.strategy = .exSitu) ∨
    u.cfg.pac.mode = .relative ∨ u.cfg.hasStab = true

instance (u : FocusUtterance) : Decidable u.HasMorphosyntacticReflex :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ _ ∨ _))

/-- **Universalist Basic Focus Rule, instantiated at Hausa.** The
    strong claim — implicit in [selkirk-1995]'s Basic Focus Rule and
    the prosodic-marking universalist tradition the paper targets in
    §5 and §6.2 — that every grammatically focused utterance carries
    *some* structural reflex of focus (movement, particle, stress, …).
    Restricted to morphosyntactic reflexes because Hausa refutes even
    this weaker version, and quantified over Hausa utterances only:
    one language's counterexample defeats the universal. -/
def UniversalBFR : Prop :=
  ∀ u : FocusUtterance, u.IsHausaLicensed → u.HasMorphosyntacticReflex

/-- **Hausa falsifies the universalist BFR.** Witness: `inSitu_newInfo`
    (paper eq. 23, *Naa tahoo dàgà Bir̃nin Ƙwànni*) is Hausa-licensed
    yet has no non-vacuous fronting, no Relative morphology, and no
    stabilizer. The §5 pilot finds no prosodic reflex either (pitch,
    duration, intensity), so even the unweakened BFR fails; only the
    morphosyntactic weakening is formalised. -/
theorem hausa_falsifies_UniversalBFR : ¬ UniversalBFR :=
  fun h => absurd (h inSitu_newInfo (by decide)) (by decide)

/-- **Unmarked subject focus is a second counterexample** (paper §2.1,
    eq. 8): a licensed subjunctive subject focus fronts string-vacuously,
    has no Relative form to shift to, and surfaces no stabilizer — the
    subject-side gap in Hausa focus marking. -/
theorem exSitu_subject_subjunctive_no_reflex :
    ¬ exSitu_subject_subjunctive.HasMorphosyntacticReflex := by decide

/-! ## Polar tone of *nē/cē* (paper §2.1)

The focus-sensitive particle *nē/cē* surfaces with low tone after a
high syllable and high tone after a low syllable — exactly
`Stabilizer.toneAfter`, which `stabilizer_tone_is_polar` in
`Fragments/Hausa/Focus.lean` grounds in the cross-fragment
`Tone.polarOf`. The minimal pair below is paper eq. (3a, 3b). -/

/-- Eq. (3a): *[DP Kandè] cee* — the host *Kandè* ends in a low
    syllable (*-dè* with grave accent), so the stabilizer surfaces
    high. -/
example : Stabilizer.cee.toneAfter .L = .H := rfl

/-- Eq. (3b): *[DP Kiifii] nèe* — the host *Kiifii* ends in a high
    syllable (unmarked vowel = high), so the stabilizer surfaces low. -/
example : Stabilizer.nee.toneAfter .H = .L := rfl

end HartmannZimmermann2007
