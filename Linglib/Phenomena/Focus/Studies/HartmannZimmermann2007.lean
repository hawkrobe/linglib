import Linglib.Fragments.Hausa.Focus
import Linglib.Fragments.Hausa.TAM
import Linglib.Fragments.Hausa.Tone

/-!
# Hartmann & Zimmermann (2007) — Focus in Hausa
@cite{hartmann-zimmermann-2007} @cite{newman-2000}

@cite{hartmann-zimmermann-2007} argue that Hausa is a counterexample to
the universalist claim that focus marking is obligatory and that focus
position determines pragmatic interpretation. The empirical claims
formalised in this study file are:

- **Two focus strategies** (§2): *ex-situ* (fronted, with relative TAM
  and optional stabilizer *nē/cē*) and *in-situ* (base position, no
  morphosyntactic reflex). Already encoded in `Fragments/Hausa/Focus.lean`'s
  `Strategy`/`FocusConfig`.
- **Subject-focus generalization** (§2.2.2, eq. 17): subjects cannot
  be focused in-situ — they obligatorily front. The paper's
  `*Daudàa ya-nàa kirà-ntà` registers as a structural failure of
  `FocusUtt.HausaLicensed`, not a stipulated star.
- **Meaning-Structure Mapping Hypothesis** (eq. 21): focus position
  ↔ pragmatic interpretation. Hausa **falsifies** this — both
  strategies attest each of the four pragmatic uses
  (new-information, corrective, selective, contrastive; §3.2).
- **Polar tone of *nē/cē*** (§2.1): the stabilizer surfaces with the
  *opposite* tone of the immediately preceding syllable. This is
  exactly `stabilizer_tone_is_polar` from `Fragments/Hausa/Focus.lean`
  §8 — re-instantiated here on the minimal pair from paper eq. (3) so
  the empirical anchor is visible.

Out of scope (deferred): the section 4 *focus pied-piping* /
*partial focus movement* data and the eq. (47) "Ex-Situ Generalisation,
final version" — these need a structured-meaning-style overlap
predicate on focus constituents that the current Fragment doesn't
expose. The section 5 prosodic pilot study and section 6 *emphasis*
motivation are also out of scope (they are *quantitative tendencies*
and *functional pressures* rather than categorical claims).
-/

namespace Phenomena.Focus.Studies.HartmannZimmermann2007

open Fragments.Hausa.Focus
open Fragments.Hausa.Inflection (cmp_3sm_R cmp_3sm_G cont_3sm_R)
open Fragments.Hausa.Tone (polarOf)
open Phonology.Autosegmental.RegisterTier (ToneFeature)
open Core (SurfaceGender)

-- ============================================================================
-- § 1: Pragmatic Focus Types (paper §1.2, after Uhmann 1991)
-- ============================================================================

/-- The four pragmatic uses of focus distinguished in
    @cite{hartmann-zimmermann-2007} §1.2 (eq. 1a–d), built on a single
    Roothian alternative-set semantics. The paper emphasises that these
    are *pragmatic* uses of one *semantic* focus, not distinct semantic
    types — so the type carries no semantic load, only a label for
    discourse role. -/
inductive PragType where
  | newInfo      -- (1a) Q/A new-information focus
  | corrective   -- (1b) correction of prior assertion
  | selective    -- (1c) selection from explicit alternatives
  | contrastive  -- (1d) parallel contrast across utterances
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: What is Focused (subject vs non-subject; for the eq. 17 generalization)
-- ============================================================================

/-- A coarse classification of the focused constituent. Hausa singles
    out *subjects* as the one cell where in-situ focus is unavailable
    (paper eq. 17); everything else (object, adverbial, predicate,
    clause) collapses to `nonSubject` for present purposes. -/
inductive Focused where
  | subject
  | nonSubject
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 3: Tagged Focus Utterances + Hausa Licensing
-- ============================================================================

/-- A *focus utterance* bundles a `FocusConfig` (morphosyntax, from
    `Fragments/Hausa/Focus.lean`) with its pragmatic interpretation and
    a tag for what the focused constituent is. The Focus Fragment is
    deliberately agnostic about pragmatic type and constituent identity;
    this study file is where those tags get attached to specific
    paper examples. -/
structure FocusUtt where
  cfg      : FocusConfig
  pragType : PragType
  focused  : Focused
  deriving Repr

/-- A focus utterance is **Hausa-licensed** iff it satisfies *both* the
    morphosyntactic licensing condition (`FocusConfig.Licensed`,
    encoding the relative-TAM requirement on ex-situ focus) *and* the
    @cite{hartmann-zimmermann-2007} eq. (17) subject-focus generalization:
    focused subjects must surface ex-situ. The conjunction is what
    "Hausa-grammatical focus" means in this paper. -/
def FocusUtt.HausaLicensed (u : FocusUtt) : Prop :=
  u.cfg.Licensed ∧ (u.focused = .subject → u.cfg.strategy = .exSitu)

instance (u : FocusUtt) : Decidable u.HausaLicensed :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- § 4: The 8-Cell Empirical Matrix (paper §3.2)
--     Both strategies × all four pragmatic types
-- ============================================================================

/-- Helper: ex-situ relative-completive focus on a 3sg.M non-feminine
    constituent with stabilizer present. The proof obligation
    `cmp_3sm_R.tam.HasRelativeForm → cmp_3sm_R.mode = .relative` reduces
    to `True → rfl`. -/
private def es (pT : PragType) (foc : Focused := .nonSubject) : FocusUtt :=
  ⟨mkExSitu cmp_3sm_R .masculine true true (fun _ => rfl), pT, foc⟩

/-- Helper: in-situ absolute-completive focus on a 3sg.M constituent.
    In-situ licensing is vacuous; the absolute (general) PAC is
    diagnostic of in-situ in the perfective/continuous (paper §2.2). -/
private def is_ (pT : PragType) (foc : Focused := .nonSubject) : FocusUtt :=
  ⟨mkInSitu cmp_3sm_G .masculine true, pT, foc⟩

/-- Ex-situ + new-information focus (paper eq. 22):
    *Kiifii nèe Kandè takèe dafàawaa* 'Kande is cooking the FISH.' -/
def es_newInfo : FocusUtt := es .newInfo

/-- Ex-situ + corrective focus on a feminine subject (paper eq. 24):
    *màataŕ-sa cèe ta mutù* 'No, it was HIS WIFE who died.' This is
    one of the few subject-focus cells in the matrix; the subject-focus
    generalization (§6) requires it to be ex-situ, which it is. -/
def es_corrective : FocusUtt :=
  ⟨mkExSitu cmp_3sm_R .feminine true true (fun _ => rfl), .corrective, .subject⟩

/-- Ex-situ + selective focus (paper eq. 29):
    *Gùdaa nakèe sô!* 'I want a WHOLE.' -/
def es_selective : FocusUtt := es .selective

/-- Ex-situ + contrastive focus (paper eq. 27):
    *cî kawài akèe ta yî* 'it is only EATING that is going on.' -/
def es_contrastive : FocusUtt := es .contrastive

/-- In-situ + new-information focus (paper eq. 23):
    *Naa tahoo dàgà Bířnin Kwànni* 'I came from BIRNIN KONNI.' -/
def is_newInfo : FocusUtt := is_ .newInfo

/-- In-situ + corrective focus (paper eq. 25):
    *zân biyaa shâ bìyař̀ nèe* 'No, I will pay FIFTEEN.' -/
def is_corrective : FocusUtt := is_ .corrective

/-- In-situ + selective focus (paper eq. 30):
    *Zân shaa shaayìi* 'I will drink TEA.' -/
def is_selective : FocusUtt := is_ .selective

/-- In-situ + contrastive focus (paper eq. 26):
    *...baa àa bî ta gàbansà* '...you shouldn't pass IN FRONT of him.' -/
def is_contrastive : FocusUtt := is_ .contrastive

/-- The 8-cell empirical matrix from paper §3.2. Every cell is
    Hausa-licensed; together they witness the failure of the MSMH
    (§5 below). -/
def hzMatrix : List FocusUtt :=
  [es_newInfo, es_corrective, es_selective, es_contrastive,
   is_newInfo, is_corrective, is_selective, is_contrastive]

/-- **Every cell of the H&Z matrix is Hausa-licensed.** Both strategies
    attest each pragmatic type; the only subject-focus cell
    (`es_corrective`, eq. 24) is ex-situ, consistent with the
    eq. (17) generalization. -/
theorem all_hzMatrix_HausaLicensed :
    ∀ u ∈ hzMatrix, u.HausaLicensed := by
  intro u hu
  simp only [hzMatrix, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

-- ============================================================================
-- § 5: Meaning-Structure Mapping Hypothesis (paper eq. 21) — refuted
-- ============================================================================

/-- **Meaning-Structure Mapping Hypothesis** (paper eq. 21):
    "Different focus positions are linked to different semantic
    interpretations." Formalised as the claim that focus strategy
    *determines* pragmatic interpretation — any two attested utterances
    sharing a strategy must share a pragmatic type. -/
def MSMH : Prop :=
  ∀ u₁ u₂ : FocusUtt, u₁.cfg.strategy = u₂.cfg.strategy →
    u₁.pragType = u₂.pragType

/-- **Hausa falsifies the MSMH** (paper §3.2). Witness: `es_newInfo`
    (eq. 22) and `es_corrective` (eq. 24) are both ex-situ but differ
    in pragmatic type. The 8-cell matrix supplies many further
    same-strategy / different-pragType pairs. -/
theorem hausa_falsifies_MSMH : ¬ MSMH := by
  intro h
  exact PragType.noConfusion (h es_newInfo es_corrective rfl)

/-- **In-situ also falsifies the MSMH.** The same-strategy /
    different-pragType pattern is not unique to ex-situ:
    `is_newInfo` (eq. 23) and `is_corrective` (eq. 25) are both
    in-situ. -/
theorem hausa_falsifies_MSMH_inSitu :
    ∃ u₁ u₂ : FocusUtt,
      u₁.cfg.strategy = u₂.cfg.strategy ∧ u₁.pragType ≠ u₂.pragType :=
  ⟨is_newInfo, is_corrective, rfl, by decide⟩

-- ============================================================================
-- § 6: Subject-Focus Generalization (paper §2.2.2, eq. 17)
-- ============================================================================

/-- **Subject-focus generalization** (paper eq. 17). Hausa subjects can
    only be focused via the ex-situ strategy. The theorem unpacks the
    second conjunct of `HausaLicensed` — the empirical content of
    eq. (17) is bundled into the licensing predicate, not stipulated
    as a star. -/
theorem subject_focus_only_exSitu (u : FocusUtt)
    (h : u.HausaLicensed) (hSubj : u.focused = .subject) :
    u.cfg.strategy = .exSitu := h.2 hSubj

/-- The paper's ungrammatical in-situ subject focus (eq. 17 A2):
    *\*Daudàa ya-nàa kirà-ntà* — 3sg.M subject, in-situ, absolute
    completive. Constructed directly to demonstrate that the predicate
    has bite. -/
def starred_inSitu_subject : FocusUtt :=
  ⟨mkInSitu cmp_3sm_G .masculine true, .newInfo, .subject⟩

/-- **The starred in-situ subject focus is not Hausa-licensed.** Its
    morphosyntactic licensing succeeds (in-situ is vacuously licensed
    by `FocusConfig.Licensed`) but the subject-focus conjunct fails:
    a `subject` constituent paired with `inSitu` strategy contradicts
    the eq. (17) generalization. -/
theorem starred_inSitu_subject_not_HausaLicensed :
    ¬ starred_inSitu_subject.HausaLicensed := by decide

/-- The paper's grammatical ex-situ subject focus (eq. 17 A1):
    *Daudàa (nee) ya-kèe kirà-ntà*. -/
def licensed_exSitu_subject : FocusUtt :=
  ⟨mkExSitu cont_3sm_R .masculine true true (fun _ => rfl),
   .newInfo, .subject⟩

/-- **The grammatical ex-situ subject focus IS Hausa-licensed.** The
    minimal pair with `starred_inSitu_subject` is the empirical content
    of eq. (17). -/
theorem licensed_exSitu_subject_HausaLicensed :
    licensed_exSitu_subject.HausaLicensed := by decide

-- ============================================================================
-- § 7: Polar Tone of *nē/cē* — Cross-Fragment Bridge (paper §2.1)
-- ============================================================================

/-! Paper §2.1: the focus-sensitive particle *nē/cē* surfaces "with low
tone if the immediately preceding syllable is high, and with high
tone if the preceding syllable is low" — i.e. polar tone. This is
*exactly* `Stabilizer.toneAfter` from `Fragments/Hausa/Focus.lean` §8,
which delegates to `Tone.polarOf` from `Fragments/Hausa/Tone.lean`.
The two minimal-pair examples below are paper eq. (3a, 3b). -/

/-- Eq. (3a): *[DP Kandè] cee* — the host *Kandè* ends in a low
    syllable (*-dè* with grave accent), so the stabilizer surfaces
    high. -/
example : Stabilizer.cee.toneAfter .L = .H := rfl

/-- Eq. (3b): *[DP Kiifii] nèe* — the host *Kiifii* ends in a high
    syllable (unmarked vowel = high), so the stabilizer surfaces low. -/
example : Stabilizer.nee.toneAfter .H = .L := rfl

/-- **Generalised polarity claim from paper §2.1.** The stabilizer's
    surface tone is a *function of the host tone alone* — independent
    of which allomorph (*nē* vs *cē*) the gender/number agreement
    selects. The polar-tone description in @cite{hartmann-zimmermann-2007}
    §2.1 follows from `Tone.polarOf` being a unary function on the
    host, not a property of the stabilizer's lexical entry. -/
theorem stabilizer_tone_independent_of_allomorph
    (s₁ s₂ : Stabilizer) (host : ToneFeature) :
    s₁.toneAfter host = s₂.toneAfter host := rfl

/-- **The polar-tone description is structural, not stipulative.**
    Re-derives `stabilizer_tone_is_polar` from the cross-fragment
    bridge as a one-liner, anchoring the H&Z §2.1 generalization in
    the same `Tone.polarOf` operator that handles the genitive linker
    *-n* and other Hausa polarity phenomena. -/
theorem polar_tone_from_polarOf (s : Stabilizer) (host : ToneFeature) :
    s.toneAfter host = polarOf host :=
  stabilizer_tone_is_polar s host

end Phenomena.Focus.Studies.HartmannZimmermann2007
