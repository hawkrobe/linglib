/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Indonesian.TAM
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Studies.Kiparsky2002

/-!
# Arka (2013): the typology and syntax of TAM in Indonesian

[arka-2013] argues that Indonesian TAM is *morphosemantic and contextual*,
not grammatical: there is no obligatory morphosyntactic TAM opposition, yet
the language shows a genuine finiteness contrast, diagnosed by the
distribution of the TAM auxiliaries (*sudah/telah*, *mau*, *sedang*, *akan*)
occupying I(NFL).

Formalized over `Time.ReichenbachFrame` and the [sneddon-1996] marker
inventory (`Fragments/Indonesian/TAM.lean`):

1. **Grammaticalization contrast** (§2): *sudah/telah* expresses bare E < R;
   the English present perfect additionally pins R to speech time. Hence
   [klein-1992]'s present perfect puzzle (`Kiparsky2002.present_perfect_puzzle`)
   does not arise: *Dia sudah pergi kemarin* is satisfiable (E < R < S).
   Following [kibort-2009], the underlying semantics is shared and only the
   grammaticalized E,R,S configuration differs.
2. **Finiteness** (§3): auxiliaries sit in I; truncated/controlled
   complements are bare VPs; equational/nominal predications project no I —
   jointly predicting the auxiliary-acceptability paradigm.
3. **Cross-source bridge**: Arka's auxiliary class matches the
   [sneddon-1996] temporal markers except *mau*, which Sneddon sets apart as
   a full verb — a genuine classification divergence between the sources.

Not formalized (documented for follow-up): the default-past temporal axis of
=nya nominalization and its cancellability by *nanti* (Arka's kapan-question
evidence), the voice–TAM affinities, and evidential *katanya*.
-/

namespace Arka2013

open Time Indonesian

/-! ### Reichenbachian semantics of the TAM auxiliaries -/

variable {T : Type*} [LinearOrder T]

/-- The frame relation [arka-2013] assigns to each auxiliary meaning:
*sudah/telah* E < R with R free, *sedang* E = R, *akan* future R with E at R
(point form of his S < E-R). `none` for marker meanings the paper does not
analyze. -/
def frameSemantics : TemporalMeaning → Option (ReichenbachFrame T → Prop)
  | .occurred => some (·.isPerfect)
  | .inProgress => some (·.isPerfective)
  | .future => some (λ f => f.isFuture ∧ f.isPerfective)
  | _ => none

/-- The English present perfect grammaticalizes E < R together with R pinned
to the deictic centre ([arka-2013] §2, after [klein-1992] and
[kibort-2009]). -/
def englishPresentPerfect (f : ReichenbachFrame T) : Prop :=
  f.isPerfect ∧ f.isPresent

instance (f : ReichenbachFrame T) : Decidable (englishPresentPerfect f) := by
  unfold englishPresentPerfect; infer_instance

/-- *telah* expresses the same frame relation as *sudah* — the fragment's
register-only contrast (`Indonesian.telah_sudah_same_meaning_distinct_register`)
transported through [arka-2013]'s semantic assignment. -/
theorem telah_sudah_same_semantics :
    frameSemantics (T := T) telah.meaning = frameSemantics sudah.meaning := rfl

/-- *Dia sudah pergi kemarin*: *sudah* tolerates a past reference time —
witness frame E < R < P = S. "Sudah/telah is also compatible with a specific
past reference such as kemarin." -/
theorem sudah_allows_past_reference :
    ∃ f : ReichenbachFrame ℤ, f.isPerfect ∧ f.isPast ∧ f.isSimpleCase :=
  ⟨⟨2, 2, 1, 0⟩, by decide⟩

/-- *Dia sudah pergi (sekarang)*: the English-present-perfect-like reading
E < R = S is also available — R is genuinely free. -/
theorem sudah_allows_present_reference :
    ∃ f : ReichenbachFrame ℤ, f.isPerfect ∧ f.isPresent ∧ f.isSimpleCase :=
  ⟨⟨1, 1, 1, 0⟩, by decide⟩

/-- [klein-1992]'s puzzle and its Indonesian dissolution: with a past-time
adverbial (R < P), the English present perfect is contradictory
(`Kiparsky2002.present_perfect_puzzle`), while *sudah* under the same
constraint is satisfiable. Languages grammaticalize different E,R,S
configurations of one underlying semantics ([kibort-2009]). -/
theorem klein_puzzle_dissolved :
    (∀ f : ReichenbachFrame ℤ, englishPresentPerfect f → f.isPast → False) ∧
    ∃ f : ReichenbachFrame ℤ, f.isPerfect ∧ f.isPast :=
  ⟨λ f hpp hpast => Kiparsky2002.present_perfect_puzzle f hpp.2
      ((ReichenbachFrame.isPast_def f).mp hpast),
   ⟨⟨2, 2, 1, 0⟩, by decide⟩⟩

/-- The English present perfect strictly strengthens *sudah*: every English
present-perfect frame is a *sudah* frame, but not conversely. -/
theorem english_pp_strictly_stronger :
    (∀ f : ReichenbachFrame T, englishPresentPerfect f → f.isPerfect) ∧
    ∃ f : ReichenbachFrame ℤ, f.isPerfect ∧ ¬ englishPresentPerfect f :=
  ⟨λ _ h => h.1, ⟨⟨2, 2, 1, 0⟩, by decide⟩⟩

/-! ### Finiteness: auxiliaries in I, truncated complements as bare VPs -/

/-- Clause projections in [arka-2013]'s LFG analysis: finite clauses project
IP whose I hosts the TAM auxiliaries; truncated/controlled complements are
bare VPs; equational/nominal predications project no verbal structure. -/
inductive Projection where
  | ip | vp | nominal
  deriving DecidableEq, Repr

/-- The I(NFL) position exists only in IP. -/
def Projection.hasInfl (p : Projection) : Prop := p = .ip

instance : DecidablePred Projection.hasInfl := λ p =>
  inferInstanceAs (Decidable (p = .ip))

/-- A clause type from [arka-2013]'s finiteness paradigm: the construction,
the projection his analysis assigns, and the observed acceptability of a TAM
auxiliary inside it. -/
structure ClauseType where
  construction : String
  projection : Projection
  /-- Observed: a TAM auxiliary is acceptable inside the clause. -/
  auxAcceptable : Bool
  deriving DecidableEq, Repr

/-- Root clause: *Dia akan/sudah/sedang makan*. -/
def rootClause : ClauseType := ⟨"root clause", .ip, true⟩

/-- Finite *bahwa* 'that' complement: *Saya tahu bahwa mereka akan datang*. -/
def bahwaComplement : ClauseType := ⟨"bahwa complement", .ip, true⟩

/-- Finite *agar* 'so that' purposive: *Saya belajar agar (bisa) menembak*. -/
def agarPurposive : ClauseType := ⟨"agar purposive", .ip, true⟩

/-- Truncated complement of *ingin* 'want': *Mereka ingin [(ˣakan) datang]*. -/
def inginComplement : ClauseType := ⟨"ingin complement", .vp, false⟩

/-- Controlled complement of *menyuruh* 'order': *Saya menyuruh dia
[(ˣakan/sudah/sedang) makan]*. -/
def menyuruhComplement : ClauseType := ⟨"menyuruh complement", .vp, false⟩

/-- Resultative complement: *Orang itu mendorong saya [(ˣakan/sedang/sudah)
jatuh]*. -/
def resultativeComplement : ClauseType := ⟨"resultative complement", .vp, false⟩

/-- *sambil* 'while' adjunct: *Dia datang [(sambil) (ˣsedang) menangis]*. -/
def sambilAdjunct : ClauseType := ⟨"sambil adjunct", .vp, false⟩

/-- Complement of *belajar* 'learn': *Saya belajar [(ˣbisa) menembak]*. -/
def belajarComplement : ClauseType := ⟨"belajar complement", .vp, false⟩

/-- Equational/nominal predication: *(ˣakan) tanyanya*, *(ˣsedang)
tampaknya* — "a nominal predicate cannot take an auxiliary". -/
def nominalPredication : ClauseType := ⟨"nominal predication", .nominal, false⟩

/-- [arka-2013]'s finiteness paradigm. -/
def paradigm : List ClauseType :=
  [rootClause, bahwaComplement, agarPurposive, inginComplement,
   menyuruhComplement, resultativeComplement, sambilAdjunct,
   belajarComplement, nominalPredication]

/-- The I-position account predicts the paradigm exactly: an auxiliary is
acceptable iff the clause projects I. Auxiliary distribution thereby
diagnoses finiteness in a language with no inflectional TAM — Arka's central
claim. -/
theorem aux_distribution_diagnoses_finiteness :
    ∀ c ∈ paradigm, (c.projection.hasInfl ↔ c.auxAcceptable = true) := by
  decide

/-! ### Arka's auxiliary class vs the Sneddon inventory -/

/-- [arka-2013]'s TAM auxiliaries: "sudah/telah, mau, sedang, and akan". -/
def auxiliaryForms : List String := ["sudah", "telah", "mau", "sedang", "akan"]

/-- Every Arka auxiliary except *mau* is a [sneddon-1996] temporal marker,
and *mau* is not one: Sneddon sets volitional *mau*/*ingin* apart as full
verbs where Arka classifies *mau* as an I-position auxiliary — a genuine
classification divergence between the sources. -/
theorem auxiliaries_vs_sneddon_markers :
    auxiliaryForms.filter (λ s => (temporalMarkers.map (·.form)).contains s) =
      ["sudah", "telah", "sedang", "akan"] ∧
    ¬ (temporalMarkers.map (·.form)).contains "mau" := by decide

/-- [arka-2013]'s glosses (akan 'FUT', sedang 'PROG', sudah/telah 'PERF')
agree with the [sneddon-1996]-derived meanings in the fragment. -/
theorem glosses_match_fragment :
    akan.meaning = .future ∧ sedang.meaning = .inProgress ∧
    sudah.meaning = .occurred ∧ telah.meaning = .occurred := by decide

end Arka2013
