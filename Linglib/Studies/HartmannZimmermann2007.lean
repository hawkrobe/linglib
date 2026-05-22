import Linglib.Fragments.Hausa.Focus
import Linglib.Fragments.Hausa.TAM
import Linglib.Fragments.Hausa.Tone
import Linglib.Core.Logic.FactorsThroughOn

/-!
# Hausa focus strategies and pragmatic types

Formalises the Hartmann & Zimmermann (2007) argument that Hausa is a
counterexample to the universalist claims that focus marking is
obligatory and that focus position determines pragmatic
interpretation.

## Main definitions

* `PragType`: four pragmatic uses of focus (new-info, corrective,
  selective, contrastive), paper §1.2 / eq. (1a-d).
* `Focused`: subject vs nonSubject classification.
* `FocusUtterance`: bundles `FocusConfig`, `PragType`, and `Focused`.
* `FocusUtterance.IsHausaLicensed`: morphosyntactic licensing plus
  the §2.2.2 subject-focus generalization conditional on
  `TAM.HasRelativeForm`.
* `FocusUtterance.HasMorphosyntacticReflex`: ex-situ position or
  stabilizer.
* `hzMatrix`: the 8-cell empirical matrix from paper §3.2.
* `UniversalBFR`: universalist Basic Focus Rule (morphosyntactic
  reflex required on every focus).

## Main results

* `all_hzMatrix_IsHausaLicensed`: every cell of the 8-cell matrix is
  Hausa-licensed.
* `strategy_does_not_determine_pragType`: `pragType` does not factor
  through `cfg.strategy` on Hausa-licensed utterances. The same
  factor-through schema (`Function.FactorsThroughOn`) is *satisfied*
  for Hungarian in `Kiss1998.lean` with `position`/`focusType`.
* `strategy_underdetermines_pragType_inSitu`: even restricted to
  in-situ utterances, strategy underdetermines pragType.
* `subject_focus_only_exSitu`: subject focus requires ex-situ when
  the TAM admits a relative form (paper §2.2.2).
* `hausa_falsifies_UniversalBFR`: in-situ new-info utterances carry
  no morphosyntactic reflex, refuting the universalist BFR.
* `polar_tone_from_polarOf`: the *nē/cē* polar-tone description
  derives from the cross-fragment `Tone.polarOf` operator.

## Implementation notes

The "Meaning-Structure Mapping Hypothesis" the substrate used to
ascribe to this paper (eq. 21) is the formaliser's coinage; neither
H&Z nor Kiss 1998 use that label. The shared schema is now
`Function.FactorsThroughOn` (in `Core.Logic.FactorsThroughOn`),
making the typological contrast a difference of verdict on a single
set-theoretic factor-through predicate.

The specific equation numbers in paper-citation comments (eq. 22-30)
have been verified against the same authors' Tangale paper
(Studia Linguistica 61(2)) which shares the pragmatic-focus
taxonomy and the focus-marking assumptions, but the Hausa book
chapter itself has not been spot-checked. Equation references in
this file are flagged `-- UNVERIFIED` accordingly.

## TODO

* §3.2.5 exhaustivity contrast against Kiss 1998 requires an
  alternatives-semantics exhaustivity operator beyond `PragType` tags.
* §4 focus pied-piping / partial focus movement and the eq. (47)
  "Ex-Situ Generalisation, final version" need a structured-meaning
  overlap predicate.
* §5 prosodic pilot data and §6.1 emphasis motivation are
  quantitative tendencies, currently in docstring prose only.

## References

* @cite{hartmann-zimmermann-2007}, @cite{newman-2000}.
-/

namespace HartmannZimmermann2007

open Fragments.Hausa.Focus
open Fragments.Hausa.Inflection
  (PAC Mode TAM cmp_3sm_R cmp_3sm_G cmp_3sf_R cont_3sm_R cont_3sm_G cont_3sf_R
   cmp_1sg_G cont_1sg_R fut_1sg subj_3sm)
open Fragments.Hausa.Tone (polarOf)
open Phonology.Autosegmental.RegisterTier (TRN)
open Features (SurfaceGender)

/-! ## Pragmatic focus types (paper §1.2, after Uhmann 1991) -/

/-- The four pragmatic uses of focus distinguished in
    @cite{hartmann-zimmermann-2007} §1.2 (eq. 1a–d), built on a single
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
    out *subjects* as the cell where in-situ focus is unavailable in the
    perfective/continuous (paper §2.2.2); everything else (object,
    adverbial, predicate, clause) collapses to `nonSubject`. -/
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
    @cite{hartmann-zimmermann-2007} §2.2.2 subject-focus generalization,
    *conditional on the TAM admitting a relative form*. Per the paper
    (p. 4): "subject foci are syntactically and morphologically
    unmarked in the future, habitual and subjunctive aspects". The
    asymmetry is therefore tied to `TAM.HasRelativeForm`, not to focus
    per se — making the licensing predicate derive from a structural
    fact about the TAM rather than stipulate a global subject ban. -/
def FocusUtterance.IsHausaLicensed (u : FocusUtterance) : Prop :=
  u.cfg.Licensed ∧
  ((u.focused = .subject ∧ u.cfg.pac.tam.HasRelativeForm) →
    u.cfg.strategy = .exSitu)

instance (u : FocusUtterance) : Decidable u.IsHausaLicensed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The 8-cell empirical matrix (paper §3.2)

Ex-situ × all four pragmatic types, then in-situ × all four. -/

/-- Smart constructor for an ex-situ focus utterance. The proof
    obligation `pac.tam.HasRelativeForm → pac.mode = .relative` is
    threaded explicitly (no tactic default). -/
private def mkExSituUtt (pac : PAC) (g : SurfaceGender) (sg : Bool)
    (h : pac.tam.HasRelativeForm → pac.mode = .relative)
    (pT : PragType) (foc : Focused := .nonSubject) :
    FocusUtterance :=
  ⟨mkExSitu pac g sg true h, pT, foc⟩

/-- Smart constructor for an in-situ focus utterance. -/
private def mkInSituUtt (pac : PAC) (g : SurfaceGender) (sg : Bool)
    (pT : PragType) (foc : Focused := .nonSubject) :
    FocusUtterance :=
  ⟨mkInSitu pac g sg, pT, foc⟩

/-- Ex-situ + new-information focus (paper eq. 22):
    *Kiifii nèe Kandè takèe dafàawaa* 'Kande is cooking the FISH.'
    PAC: 3sg.F relative continuous *takèe* (subject-marker for *Kande*). -/
def exSitu_newInfo : FocusUtterance :=
  mkExSituUtt cont_3sf_R .masculine true (fun _ => rfl) .newInfo

/-- Ex-situ + corrective focus on a feminine subject (paper eq. 24):
    *màataŕ-sa cèe ta mutù* 'No, it was HIS WIFE who died.'
    PAC: 3sg.F relative completive *ta*. -/
def exSitu_corrective : FocusUtterance :=
  mkExSituUtt cmp_3sf_R .feminine true (fun _ => rfl) .corrective .subject

/-- Ex-situ + selective focus (paper eq. 29):
    *Gùdaa nakèe sô!* 'I want a WHOLE.'
    PAC: 1sg relative continuous *nakèe*. -/
def exSitu_selective : FocusUtterance :=
  mkExSituUtt cont_1sg_R .masculine true (fun _ => rfl) .selective

/-- Ex-situ + contrastive focus (paper eq. 27):
    *cî kawài akèe ta yî* 'it is only EATING that is going on.'
    Approximated with 3sg.M relative completive — paper uses the 4sg
    impersonal *akèe* which `Features.Person.Category` does not yet expose. -/
def exSitu_contrastive : FocusUtterance :=
  mkExSituUtt cmp_3sm_R .masculine true (fun _ => rfl) .contrastive

/-- In-situ + new-information focus (paper eq. 23):
    *Naa tahoo dàgà Bířnin Kwànni* 'I came from BIRNIN KONNI.'
    PAC: 1sg general completive *naa*. -/
def inSitu_newInfo : FocusUtterance := mkInSituUtt cmp_1sg_G .masculine true .newInfo

/-- In-situ + corrective focus (paper eq. 25):
    *zân biyaa shâ bìyař̀ nèe* 'No, I will pay FIFTEEN.'
    PAC: 1sg future *zân* (no G/R contrast). -/
def inSitu_corrective : FocusUtterance := mkInSituUtt fut_1sg .masculine true .corrective

/-- In-situ + selective focus (paper eq. 30):
    *Zân shaa shaayìi* 'I will drink TEA.'
    PAC: 1sg future *zân*. -/
def inSitu_selective : FocusUtterance := mkInSituUtt fut_1sg .masculine true .selective

/-- In-situ + contrastive focus (paper eq. 26):
    *...baa àa bî ta gàbansà* '...you shouldn't pass IN FRONT of him.'
    Approximated with 3sg.M general completive — paper uses the 4sg
    impersonal *àa*. -/
def inSitu_contrastive : FocusUtterance := mkInSituUtt cmp_3sm_G .masculine true .contrastive

/-- The 8-cell empirical matrix from paper §3.2. Every cell is
    Hausa-licensed; together they witness `strategy_does_not_determine_pragType`
    below. -/
def hzMatrix : List FocusUtterance :=
  [exSitu_newInfo, exSitu_corrective, exSitu_selective, exSitu_contrastive,
   inSitu_newInfo, inSitu_corrective, inSitu_selective, inSitu_contrastive]

/-- **Every cell of the H&Z matrix is Hausa-licensed.** Both strategies
    attest each pragmatic type; the only subject-focus cell
    (`exSitu_corrective`, eq. 24) is ex-situ in a relative-form TAM,
    consistent with the §2.2.2 generalization. -/
theorem all_hzMatrix_IsHausaLicensed :
    ∀ u ∈ hzMatrix, u.IsHausaLicensed := by
  intro u hu
  simp only [hzMatrix, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Strategy does not determine pragmatic type (paper §3.2)

The 8-cell matrix witnesses that, on Hausa-licensed utterances,
`pragType` does *not* factor through `cfg.strategy`. The same
factor-through schema (`Function.FactorsThroughOn`) is *satisfied*
for Hungarian in `Kiss1998.lean` with `position`/`focusType`. -/

/-- Hausa-licensed utterances do not exhibit a factor-through from
strategy to pragmatic type: `exSitu_newInfo` (eq. 22, -- UNVERIFIED)
and `exSitu_corrective` (eq. 24, -- UNVERIFIED) are both ex-situ but
have distinct pragmatic types. -/
theorem strategy_does_not_determine_pragType :
    ¬ Function.FactorsThroughOn
        FocusUtterance.pragType
        (fun u : FocusUtterance => u.cfg.strategy)
        {u | u.IsHausaLicensed} := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨exSitu_newInfo, exSitu_corrective,
    by decide, by decide, rfl, by decide⟩

/-- The same-strategy / different-pragType pattern obtains in-situ too:
`inSitu_newInfo` (eq. 23, -- UNVERIFIED) and `inSitu_corrective`
(eq. 25, -- UNVERIFIED) are both in-situ but have distinct pragmatic
types. -/
theorem strategy_underdetermines_pragType_inSitu :
    ∃ u₁ u₂ : FocusUtterance,
      u₁.IsHausaLicensed ∧ u₂.IsHausaLicensed ∧
      u₁.cfg.strategy = u₂.cfg.strategy ∧ u₁.pragType ≠ u₂.pragType :=
  ⟨inSitu_newInfo, inSitu_corrective, by decide, by decide, rfl, by decide⟩

/-! ## Subject-focus generalization (paper §2.2.2) -/

/-- **Subject-focus generalization** (paper §2.2.2). Hausa subjects can
    only be focused via the ex-situ strategy *when the TAM admits a
    relative form* (perfective/continuous). The theorem unpacks the
    second conjunct of `IsHausaLicensed`. -/
theorem subject_focus_only_exSitu (u : FocusUtterance) (h : u.IsHausaLicensed)
    (hSubj : u.focused = .subject)
    (hRel : u.cfg.pac.tam.HasRelativeForm) :
    u.cfg.strategy = .exSitu := h.2 ⟨hSubj, hRel⟩

/-- The paper's ungrammatical in-situ subject focus (§2.2.2):
    *\*Daudàa ya-nàa kirà-ntà* — 3sg.M subject, in-situ, *continuous*
    (cont_3sm_G — *yanā*). Continuous has a relative form, so the
    licensing predicate fires and rejects this. -/
def starred_inSitu_subject : FocusUtterance :=
  ⟨mkInSitu cont_3sm_G .masculine true, .newInfo, .subject⟩

/-- **The starred in-situ subject focus is not Hausa-licensed.** Its
    morphosyntactic licensing succeeds (in-situ is vacuously licensed
    by `FocusConfig.Licensed`) but the subject-focus conjunct fails:
    a `subject` constituent paired with `inSitu` strategy in a TAM
    with a relative form contradicts the §2.2.2 generalization. -/
theorem starred_inSitu_subject_not_IsHausaLicensed :
    ¬ starred_inSitu_subject.IsHausaLicensed := by decide

/-- The paper's grammatical ex-situ subject focus (§2.2.2):
    *Daudàa (nee) ya-kèe kirà-ntà*. PAC: 3sg.M relative continuous
    *yake*. -/
def licensed_exSitu_subject : FocusUtterance :=
  ⟨mkExSitu cont_3sm_R .masculine true true (fun _ => rfl),
   .newInfo, .subject⟩

/-- **The grammatical ex-situ subject focus IS Hausa-licensed.** The
    minimal pair with `starred_inSitu_subject` is the empirical content
    of the §2.2.2 generalization. -/
theorem licensed_exSitu_subject_IsHausaLicensed :
    licensed_exSitu_subject.IsHausaLicensed := by decide

/-- **In-situ subject focus IS licensed when the TAM has no relative
    form.** The paper's qualification (p. 4): "subject foci are
    syntactically and morphologically unmarked in the future,
    habitual and subjunctive aspects". A 3sg.M subjunctive subject
    in-situ is Hausa-licensed because `subj_3sm.tam.HasRelativeForm`
    is `False`, so the second conjunct of `IsHausaLicensed` is
    vacuous. -/
def inSitu_subject_subjunctive : FocusUtterance :=
  ⟨mkInSitu subj_3sm .masculine true, .newInfo, .subject⟩

theorem inSitu_subject_subjunctive_IsHausaLicensed :
    inSitu_subject_subjunctive.IsHausaLicensed := by decide

/-! ## Universalist Basic Focus Rule (paper §5, §6.2) -/

/-- A focus utterance carries a **morphosyntactic reflex of focus** iff
    it fronts the focus (`exSitu`) or surfaces a stabilizer. This is
    the structural property the universalist Basic Focus Rule says
    every focused utterance must exhibit. -/
def FocusUtterance.HasMorphosyntacticReflex (u : FocusUtterance) : Prop :=
  u.cfg.strategy = .exSitu ∨ u.cfg.hasStab = true

instance (u : FocusUtterance) : Decidable u.HasMorphosyntacticReflex :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- **Universalist Basic Focus Rule.** The strong claim — implicit in
    Selkirk's BFR and the broader prosodic-marking universalist
    tradition — that every grammatically focused utterance carries
    *some* structural reflex of focus (movement, particle, stress, …).
    Restricted to morphosyntactic reflexes here because Hausa
    refutes even this weaker version. -/
def UniversalBFR : Prop :=
  ∀ u : FocusUtterance, u.IsHausaLicensed → u.HasMorphosyntacticReflex

/-- **Hausa falsifies the universalist BFR.** Witness: `inSitu_newInfo`
    (paper eq. 23, *Naa tahoo dàgà Bířnin Kwànni*) is Hausa-licensed
    yet carries neither ex-situ position nor a stabilizer. The §5
    prosodic-pilot finding (no significant pitch/duration/intensity
    reflex either) is documented in docstring prose only — even the
    morphosyntactic-only weakening already refutes the universal. -/
theorem hausa_falsifies_UniversalBFR : ¬ UniversalBFR := by
  intro h
  have hLic : inSitu_newInfo.IsHausaLicensed := by decide
  have hRef : inSitu_newInfo.HasMorphosyntacticReflex := h _ hLic
  revert hRef; decide

/-! ## Polar tone of *nē/cē* (paper §2.1)

The focus-sensitive particle *nē/cē* surfaces with low tone after a
high syllable and high tone after a low syllable — exactly
`Stabilizer.toneAfter`, which delegates to `Tone.polarOf`. The minimal
pair below is paper eq. (3a, 3b). -/

/-- Eq. (3a): *[DP Kandè] cee* — the host *Kandè* ends in a low
    syllable (*-dè* with grave accent), so the stabilizer surfaces
    high. -/
example : Stabilizer.cee.toneAfter .L = .H := rfl

/-- Eq. (3b): *[DP Kiifii] nèe* — the host *Kiifii* ends in a high
    syllable (unmarked vowel = high), so the stabilizer surfaces low. -/
example : Stabilizer.nee.toneAfter .H = .L := rfl

/-- **The polar-tone description is structural, not stipulative.**
    Re-derives `stabilizer_tone_is_polar` from the cross-fragment
    bridge as a one-liner, anchoring the H&Z §2.1 generalization in
    the same `Tone.polarOf` operator that handles the genitive linker
    *-n* and other Hausa polarity phenomena. -/
theorem polar_tone_from_polarOf (s : Stabilizer) (host : TRN) :
    s.toneAfter host = polarOf host :=
  stabilizer_tone_is_polar s host

end HartmannZimmermann2007
