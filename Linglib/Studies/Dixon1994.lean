import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Linglib.Syntax.Case.Alignment
import Linglib.Fragments.Dargwa.Case
import Linglib.Fragments.Japanese.Case
import Linglib.Fragments.Hindi.Case

/-!
# Dixon (1994): Ergativity — typology + Silverstein hierarchy + ditransitives
[dixon-1994] [dixon-1972] [silverstein-1976] [blake-1994]
[comrie-1978] [comrie-2013] [haspelmath-2005]
[haspelmath-2021] [bohnemeyer-2004] [sumbatova-2021]

R. M. W. Dixon. *Ergativity*. Cambridge University Press, 1994. The
canonical typological reference for ergative alignment + split ergativity,
covering [silverstein-1976]'s prominence hierarchy and
[dixon-1972]'s Dyirbal split-ergative analysis.

This study file holds:

1. **The 22-language exemplar sample** spanning all five `AlignmentType`
   values across the three WALS dimensions (Ch 98/99/100).
2. **Cross-linguistic generalisations** including Dixon's NP-vs-pronoun
   ergativity asymmetry, the absence of reverse-Dixon splits, and the
   rarity of tripartite/active patterns.
3. **Silverstein's hierarchy** as a threshold-based prominence function
   with monotonicity proven, and the Dyirbal split as a specific instance.
4. **Ditransitive alignment** ([haspelmath-2005]): the 6-language
   indirective/secundative/neutral sample.
5. **Fragment bridges**: theorems verifying the per-language alignment
   classifications match the Fragment grammatical descriptions.
6. **Bridges to `Syntax/Case/Alignment`**: theorems verifying
   `marksAgent`/`marksPatient` projections agree with the case-assignment
   functions on canonical S/A/P inputs.

WALS aggregate distribution theorems are kept with the WALS data, not here.
Per-language Fragment-vs-WALS data-equality theorems are deliberately absent
— see `feedback_no_per_lang_wals_grounding_in_studies` for the rationale.
-/

set_option autoImplicit false

namespace Dixon1994

open Alignment

-- ============================================================================
-- §0. AlignmentProfile: the bundled per-language record (with its data here)
-- ============================================================================

/-- A language's morphosyntactic alignment across the three case/agreement
    domains (WALS Chs 98/99/100). The bundled per-language record for the
    exemplar sample below; lives here with its data and analysis (relocated out
    of the dissolved `Typology/Alignment.lean` — its only consumers are this
    file and `Comrie1989`, which imports it). -/
structure AlignmentProfile where
  /-- Language name. -/
  name : String
  /-- ISO 639-3 code. -/
  iso639 : String
  /-- Ch 98: alignment of case marking of full NPs. -/
  npAlignment : AlignmentType
  /-- Ch 99: alignment of case marking of pronouns. -/
  pronAlignment : AlignmentType
  /-- Ch 100: alignment of verbal person marking. -/
  verbAlignment : AlignmentType
  /-- Notes on the alignment system. -/
  notes : String := ""
  deriving Repr, DecidableEq

/-- Whether the language shows the classic NP-ergative / pronoun-accusative
    split (Dixon's generalization). -/
def AlignmentProfile.dixonSplit (p : AlignmentProfile) : Bool :=
  p.npAlignment == .ergative && p.pronAlignment == .accusative

/-- Whether all three alignment domains agree. -/
def AlignmentProfile.fullyUniform (p : AlignmentProfile) : Bool :=
  p.npAlignment == p.pronAlignment && p.pronAlignment == p.verbAlignment

-- ============================================================================
-- §1. The 22-language exemplar sample
-- ============================================================================

/-- English: accusative case marking on pronouns (I/me, he/him), no case
    on full NPs (neutral), and accusative verb agreement. -/
def english : AlignmentProfile :=
  { name := "English", iso639 := "eng"
  , npAlignment := .neutral
  , pronAlignment := .accusative
  , verbAlignment := .accusative
  , notes := "Case only on pronouns (I/me); verb agrees with S/A" }

/-- Hindi-Urdu: split-ergative. Ergative case marking (-ne on A) in
    perfective aspect for both NPs and pronouns. WALS codes the dominant
    pattern as ergative for NPs, accusative for pronouns. Verb agreement
    is neutral (agrees with unmarked argument). -/
def hindiUrdu : AlignmentProfile :=
  { name := "Hindi-Urdu", iso639 := "hin"
  , npAlignment := .ergative
  , pronAlignment := .accusative
  , verbAlignment := .neutral
  , notes := "Split ergative: -ne on A in perfective; verb agrees with unmarked arg" }

/-- Basque: consistently ergative across all three domains. -/
def basque : AlignmentProfile :=
  { name := "Basque", iso639 := "eus"
  , npAlignment := .ergative
  , pronAlignment := .ergative
  , verbAlignment := .ergative
  , notes := "Consistently ergative; -k on A; verb cross-references abs and erg" }

/-- Dyirbal (Pama-Nyungan, Australia): the textbook case of split
    ergativity. NPs ergative, 1st/2nd person pronouns accusative.
    No verb person agreement. -/
def dyirbal : AlignmentProfile :=
  { name := "Dyirbal", iso639 := "dbl"
  , npAlignment := .ergative
  , pronAlignment := .accusative
  , verbAlignment := .neutral
  , notes := "Dixon's (1972) textbook split-ergative: NPs erg, pronouns acc" }

/-- Georgian: active (split-S) alignment determined by verb class. -/
def georgian : AlignmentProfile :=
  { name := "Georgian", iso639 := "kat"
  , npAlignment := .active
  , pronAlignment := .active
  , verbAlignment := .active
  , notes := "Active (split-S); verb class determines S alignment" }

/-- Tagalog: WALS codes Philippine voice system as neutral. -/
def tagalog : AlignmentProfile :=
  { name := "Tagalog", iso639 := "tgl"
  , npAlignment := .neutral
  , pronAlignment := .neutral
  , verbAlignment := .neutral
  , notes := "Philippine voice system; WALS codes as neutral" }

/-- Japanese: accusative NPs and pronouns; no verb agreement. -/
def japanese : AlignmentProfile :=
  { name := "Japanese", iso639 := "jpn"
  , npAlignment := .accusative
  , pronAlignment := .accusative
  , verbAlignment := .neutral
  , notes := "ga/o case particles; no verb agreement" }

/-- Latin: accusative NPs, pronouns, verb agreement. -/
def latin : AlignmentProfile :=
  { name := "Latin", iso639 := "lat"
  , npAlignment := .accusative
  , pronAlignment := .accusative
  , verbAlignment := .accusative
  , notes := "Nom/acc case; verb agrees with S/A" }

/-- Russian: accusative across all three domains. -/
def russian : AlignmentProfile :=
  { name := "Russian", iso639 := "rus"
  , npAlignment := .accusative
  , pronAlignment := .accusative
  , verbAlignment := .accusative
  , notes := "Nom/acc; animacy-conditioned acc syncretism" }

/-- Mandarin Chinese: neutral across all three. -/
def mandarin : AlignmentProfile :=
  { name := "Mandarin Chinese", iso639 := "cmn"
  , npAlignment := .neutral
  , pronAlignment := .neutral
  , verbAlignment := .neutral
  , notes := "No case, no agreement; word order encodes relations" }

/-- Turkish: accusative. -/
def turkish : AlignmentProfile :=
  { name := "Turkish", iso639 := "tur"
  , npAlignment := .accusative
  , pronAlignment := .accusative
  , verbAlignment := .accusative
  , notes := "Nom/acc case with DOM; verb agrees with S/A" }

/-- Tongan (Austronesian): ergative on NPs and pronouns; no verb agreement. -/
def tongan : AlignmentProfile :=
  { name := "Tongan", iso639 := "ton"
  , npAlignment := .ergative
  , pronAlignment := .ergative
  , verbAlignment := .neutral
  , notes := "Ergative case on both NPs and pronouns; no verb agreement" }

/-- Guarani (Tupian): active verb agreement with split-S prefixes. -/
def guarani : AlignmentProfile :=
  { name := "Guarani", iso639 := "grn"
  , npAlignment := .neutral
  , pronAlignment := .neutral
  , verbAlignment := .active
  , notes := "Active verb agreement; oral/nasal prefix split for S" }

/-- Samoan: ergative NPs (e before A), accusative pronouns. -/
def samoan : AlignmentProfile :=
  { name := "Samoan", iso639 := "smo"
  , npAlignment := .ergative
  , pronAlignment := .accusative
  , verbAlignment := .neutral
  , notes := "Ergative NPs (e before A); accusative pronouns" }

/-- German: accusative. -/
def german : AlignmentProfile :=
  { name := "German", iso639 := "deu"
  , npAlignment := .accusative
  , pronAlignment := .accusative
  , verbAlignment := .accusative
  , notes := "Nom/acc case; verb agrees with S/A" }

/-- Swahili (Bantu): no case, accusative verb agreement (subject prefix). -/
def swahili : AlignmentProfile :=
  { name := "Swahili", iso639 := "swh"
  , npAlignment := .neutral
  , pronAlignment := .neutral
  , verbAlignment := .accusative
  , notes := "No case; S/A subject prefix on verb" }

/-- Tibetan (Lhasa): ergative NPs and pronouns; no verb agreement. -/
def tibetan : AlignmentProfile :=
  { name := "Tibetan (Lhasa)", iso639 := "bod"
  , npAlignment := .ergative
  , pronAlignment := .ergative
  , verbAlignment := .neutral
  , notes := "Ergative -gis, -kyis on A; no verb agreement" }

/-- Nez Perce: tripartite NPs and pronouns (distinct nom, erg, acc);
    accusative verb agreement. -/
def nezPerce : AlignmentProfile :=
  { name := "Nez Perce", iso639 := "nez"
  , npAlignment := .tripartite
  , pronAlignment := .tripartite
  , verbAlignment := .accusative
  , notes := "Tripartite case: distinct nom, erg, acc" }

/-- Finnish: accusative. -/
def finnish : AlignmentProfile :=
  { name := "Finnish", iso639 := "fin"
  , npAlignment := .accusative
  , pronAlignment := .accusative
  , verbAlignment := .accusative
  , notes := "Nom/acc(partitive); verb agrees with S/A" }

/-- Warlpiri (Pama-Nyungan): split-ergative — ergative NPs, accusative
    pronouns; no verb agreement. -/
def warlpiri : AlignmentProfile :=
  { name := "Warlpiri", iso639 := "wbp"
  , npAlignment := .ergative
  , pronAlignment := .accusative
  , verbAlignment := .neutral
  , notes := "Split ergative: NPs erg, pronouns acc; free word order" }

/-- Dargwa (Tanti; [sumbatova-2021]): consistently ergative across
    all three domains. -/
def dargwa : AlignmentProfile :=
  { name := "Dargwa (Tanti)", iso639 := "dar"
  , npAlignment := .ergative
  , pronAlignment := .ergative
  , verbAlignment := .ergative
  , notes := "Consistently ergative; -li on A; gender agrees with absolutive" }

/-- Yukatek Maya ([bohnemeyer-2004]): aspect-conditioned split
    intransitivity — perfective triggers ergative-like marking, imperfective
    triggers accusative-like marking. -/
def yukatek : AlignmentProfile :=
  { name := "Yukatek Maya", iso639 := "yua"
  , npAlignment := .neutral
  , pronAlignment := .neutral
  , verbAlignment := .active
  , notes := "Aspect-conditioned split-S: PRV → erg (set-B), IMPFV → acc (set-A)" }

/-- All 22 alignment profiles. -/
def allProfiles : List AlignmentProfile :=
  [ english, hindiUrdu, basque, dyirbal, georgian, tagalog
  , japanese, latin, russian, mandarin, turkish, tongan
  , guarani, samoan, german, swahili, tibetan, nezPerce
  , finnish, warlpiri, dargwa, yukatek ]

theorem allProfiles_count : allProfiles.length = 22 := by native_decide

-- ============================================================================
-- §2. Sample-level statistics
-- ============================================================================

theorem all_iso_nonempty :
    allProfiles.all (λ p => p.iso639.length > 0) = true := by native_decide

theorem all_iso_length_3 :
    allProfiles.all (λ p => p.iso639.length == 3) = true := by native_decide

theorem iso_codes_unique :
    (allProfiles.map (·.iso639)).eraseDups.length = allProfiles.length := by
  native_decide

/-- Sample distribution counts. -/
theorem sample_counts :
    (allProfiles.filter (λ p => p.npAlignment == .ergative)).length = 8 ∧
    (allProfiles.filter (λ p => p.pronAlignment == .ergative)).length = 4 ∧
    (allProfiles.filter (·.dixonSplit)).length = 4 ∧
    (allProfiles.filter (·.fullyUniform)).length = 10 := by
  native_decide

-- ============================================================================
-- §3. Cross-linguistic generalisations (Dixon 1994)
-- ============================================================================

/-- Accusative is the most common alignment for pronouns
    ([dixon-1994]'s prominence hierarchy prediction). -/
theorem accusative_most_common_pronouns :
    (allProfiles.filter (fun p => p.pronAlignment == .accusative)).length >=
    (allProfiles.filter (fun p => p.pronAlignment == .ergative)).length := by
  native_decide

/-- [dixon-1994]'s generalisation: ergative case marking is more
    common on full NPs than on pronouns. -/
theorem dixon_generalization :
    (allProfiles.filter (fun p => p.npAlignment == .ergative)).length >
    (allProfiles.filter (fun p => p.pronAlignment == .ergative)).length := by
  native_decide

/-- Split ergativity (NP-ergative + pronoun-accusative) is attested in
    multiple languages (Dyirbal, Hindi-Urdu, Samoan, Warlpiri). -/
theorem split_ergativity_attested :
    (allProfiles.filter (fun p => p.dixonSplit)).length >= 4 := by
  native_decide

/-- The reverse-Dixon pattern (accusative NPs + ergative pronouns) is
    predicted not to occur. The sample confirms it: whenever pronouns are
    ergative, NPs are at least ergative too. -/
theorem no_reverse_dixon :
    allProfiles.all (fun p =>
      if p.pronAlignment == .ergative
      then p.npAlignment == .ergative || p.npAlignment == .tripartite
      else true) = true := by
  native_decide

/-- Tripartite NP alignment is rare: only Nez Perce in the sample. -/
theorem tripartite_rare_nps :
    (allProfiles.filter (fun p => p.npAlignment == .tripartite)).length <= 1 := by
  native_decide

/-- Tripartite pronoun alignment is equally rare. -/
theorem tripartite_rare_pronouns :
    (allProfiles.filter (fun p => p.pronAlignment == .tripartite)).length <= 1 := by
  native_decide

/-- Active alignment is rare for case marking: only Georgian in the sample. -/
theorem active_rare_case :
    (allProfiles.filter (fun p => p.npAlignment == .active)).length <= 2 := by
  native_decide

/-- Aspect-conditioned split intransitivity ([bohnemeyer-2004]):
    Yukatek Maya and Georgian both show active verbal person marking. -/
theorem aspect_split_languages :
    (allProfiles.filter (fun p => p.verbAlignment == .active)).length >= 2 := by
  native_decide

theorem yukatek_and_georgian_both_active :
    yukatek.verbAlignment = .active ∧ georgian.verbAlignment = .active :=
  ⟨rfl, rfl⟩

/-- Languages with ergative NP marking tend to have ergative or neutral
    verbal person marking (or accusative as a third option). -/
theorem erg_np_verb_pattern :
    allProfiles.all (fun p =>
      if p.npAlignment == .ergative
      then p.verbAlignment == .ergative || p.verbAlignment == .neutral ||
           p.verbAlignment == .accusative
      else true) = true := by
  native_decide

/-- All five alignment types are attested for NPs. -/
theorem all_np_types_attested :
    allProfiles.any (fun p => p.npAlignment == .neutral) &&
    allProfiles.any (fun p => p.npAlignment == .accusative) &&
    allProfiles.any (fun p => p.npAlignment == .ergative) &&
    allProfiles.any (fun p => p.npAlignment == .tripartite) &&
    allProfiles.any (fun p => p.npAlignment == .active) = true := by
  native_decide

/-- All five alignment types are attested for pronouns. -/
theorem all_pron_types_attested :
    allProfiles.any (fun p => p.pronAlignment == .neutral) &&
    allProfiles.any (fun p => p.pronAlignment == .accusative) &&
    allProfiles.any (fun p => p.pronAlignment == .ergative) &&
    allProfiles.any (fun p => p.pronAlignment == .tripartite) &&
    allProfiles.any (fun p => p.pronAlignment == .active) = true := by
  native_decide

/-- Four of the five alignment types are attested for verbal person marking;
    tripartite verb agreement is exceedingly rare cross-linguistically and
    not represented here. -/
theorem verb_types_attested :
    allProfiles.any (fun p => p.verbAlignment == .neutral) &&
    allProfiles.any (fun p => p.verbAlignment == .accusative) &&
    allProfiles.any (fun p => p.verbAlignment == .ergative) &&
    allProfiles.any (fun p => p.verbAlignment == .active) = true := by
  native_decide

theorem tripartite_verb_unattested :
    allProfiles.all (fun p => p.verbAlignment != .tripartite) = true := by
  native_decide

/-- Neutral NP alignment implies neutral or accusative pronoun alignment
    (English-style: case survives only on pronouns). Never ergative. -/
theorem neutral_np_pronoun :
    allProfiles.all (fun p =>
      if p.npAlignment == .neutral
      then p.pronAlignment == .neutral || p.pronAlignment == .accusative
      else true) = true := by
  native_decide

/-- Fully uniform alignment is common (Basque, Mandarin, Latin, Russian,
    Turkish, Georgian, etc.). -/
theorem uniform_common :
    (allProfiles.filter (fun p => p.fullyUniform)).length >= 5 := by
  native_decide

/-- Among languages with non-neutral verb alignment, accusative agreement
    is the most common (verb agrees with S/A). -/
theorem accusative_verb_dominant :
    (allProfiles.filter (fun p => p.verbAlignment == .accusative)).length >
    (allProfiles.filter (fun p => p.verbAlignment == .ergative)).length ∧
    (allProfiles.filter (fun p => p.verbAlignment == .accusative)).length >
    (allProfiles.filter (fun p => p.verbAlignment == .active)).length := by
  native_decide

-- ============================================================================
-- §4. Cross-domain correlation patterns
-- ============================================================================

/-- Every language with accusative NP case also has accusative pronoun case
    in the sample. Accusative does not split across NP/pronoun like ergative. -/
theorem accusative_np_implies_accusative_pron :
    allProfiles.all (fun p =>
      if p.npAlignment == .accusative
      then p.pronAlignment == .accusative
      else true) = true := by
  native_decide

/-- No language has tripartite NP without tripartite pronoun in the sample. -/
theorem tripartite_np_implies_tripartite_pron :
    allProfiles.all (fun p =>
      if p.npAlignment == .tripartite
      then p.pronAlignment == .tripartite
      else true) = true := by
  native_decide

/-- Active NP alignment implies active pronoun alignment in the sample. -/
theorem active_np_implies_active_pron :
    allProfiles.all (fun p =>
      if p.npAlignment == .active
      then p.pronAlignment == .active
      else true) = true := by
  native_decide

-- ============================================================================
-- §5. Type-level alignment properties
-- ============================================================================

/-- Languages with no case on NPs do not have ergative NP alignment. -/
theorem neutral_np_not_ergative :
    allProfiles.all (fun p =>
      if p.npAlignment == .neutral then !p.npAlignment.marksAgent
      else true) = true := by
  native_decide

/-- Languages with tripartite case mark both A and P. -/
theorem tripartite_marks_both :
    allProfiles.all (fun p =>
      if p.npAlignment == .tripartite
      then p.npAlignment.marksAgent && p.npAlignment.marksPatient
      else true) = true := by
  native_decide

/-- Ergative alignment marks agent but not patient (S = P grouping). -/
theorem ergative_marks_agent_only :
    AlignmentType.ergative.marksAgent = true ∧
    AlignmentType.ergative.marksPatient = false := by native_decide

/-- Accusative alignment marks patient but not agent (S = A grouping). -/
theorem accusative_marks_patient_only :
    AlignmentType.accusative.marksPatient = true ∧
    AlignmentType.accusative.marksAgent = false := by native_decide

-- ============================================================================
-- §6. Silverstein hierarchy (1976)
-- ============================================================================

/-! [silverstein-1976] predicts that ergative marking targets the **less
    prominent** end of the animacy/definiteness scale. More prominent NPs
    (pronouns, 1st/2nd person) get accusative treatment; less prominent NPs
    (full NPs, 3rd person, inanimate) get ergative treatment. -/

section SilversteinSplit

open Features.Prominence (AnimacyLevel)

/-- Map the binary Core alignment family to the full alignment type. -/
private def toAlignmentType : Features.AlignmentFamily → AlignmentType
  | .accusative => .accusative
  | .ergative   => .ergative

/-- Silverstein's hierarchy: NPs at or above the prominence threshold get
    accusative alignment; those below get ergative. -/
def silverstein (threshold : Nat) (npProminence : Nat) : Features.AlignmentFamily :=
  if npProminence ≥ threshold then .accusative else .ergative

/-- Silverstein is monotone: if prominence p₁ ≥ p₂ and p₂ gets accusative,
    then p₁ gets accusative. -/
theorem silverstein_monotone (threshold p₁ p₂ : Nat)
    (h_ge : p₁ ≥ p₂) (h_acc : silverstein threshold p₂ = .accusative) :
    silverstein threshold p₁ = .accusative := by
  simp only [silverstein] at *
  split at h_acc
  · split
    · rfl
    · omega
  · contradiction

/-- Silverstein predicts Dixon's generalisation: with threshold 1, full NPs
    (prominence 0) get ergative, pronouns (prominence 1) get accusative. -/
theorem silverstein_predicts_dixon :
    silverstein 1 0 = .ergative ∧ silverstein 1 1 = .accusative := ⟨rfl, rfl⟩

/-- [dixon-1972] Dyirbal split: human/animate → accusative,
    inanimate → ergative. -/
def dyirbalSplit : Alignment.SplitErgativity AnimacyLevel :=
  { ergCondition := fun a => a == .inanimate }

theorem dyirbal_human_acc :
    dyirbalSplit.alignment .human = .accusative := rfl

theorem dyirbal_inanimate_erg :
    dyirbalSplit.alignment .inanimate = .ergative := rfl

/-- Dyirbal split matches the Dyirbal alignment profile: inanimate NPs get
    ergative alignment. -/
theorem dyirbal_split_matches_np :
    toAlignmentType (dyirbalSplit.alignment .inanimate)
    = dyirbal.npAlignment := rfl

/-- Human/animate arguments get accusative alignment. -/
theorem dyirbal_split_matches_pron :
    toAlignmentType (dyirbalSplit.alignment .human)
    = dyirbal.pronAlignment := rfl

end SilversteinSplit

-- ============================================================================
-- §7. Ditransitive alignment ([haspelmath-2005])
-- ============================================================================

def ditrans_english : DitransitiveProfile :=
  { name := "English", iso639 := "eng"
  , alignment := .indirective
  , notes := "T = P (acc); R marked with 'to'" }

def ditrans_german : DitransitiveProfile :=
  { name := "German", iso639 := "deu"
  , alignment := .indirective
  , notes := "T = accusative; R = dative" }

def ditrans_latin : DitransitiveProfile :=
  { name := "Latin", iso639 := "lat"
  , alignment := .indirective
  , notes := "T = accusative; R = dative" }

def ditrans_japanese : DitransitiveProfile :=
  { name := "Japanese", iso639 := "jpn"
  , alignment := .indirective
  , notes := "T = o (accusative); R = ni (dative)" }

def ditrans_swahili : DitransitiveProfile :=
  { name := "Swahili", iso639 := "swh"
  , alignment := .secundative
  , notes := "R = P in applicative; T marked differently" }

def ditrans_mandarin : DitransitiveProfile :=
  { name := "Mandarin", iso639 := "cmn"
  , alignment := .neutral
  , notes := "R and T both unmarked; order distinguishes" }

def allDitransProfiles : List DitransitiveProfile :=
  [ ditrans_english, ditrans_german, ditrans_latin
  , ditrans_japanese, ditrans_swahili, ditrans_mandarin ]

theorem ditrans_indirective_attested :
    allDitransProfiles.any (λ p => p.alignment == .indirective) = true := by
  native_decide

theorem ditrans_secundative_attested :
    allDitransProfiles.any (λ p => p.alignment == .secundative) = true := by
  native_decide

theorem ditrans_neutral_attested :
    allDitransProfiles.any (λ p => p.alignment == .neutral) = true := by
  native_decide

/-- Indirective is more common than secundative (parallel to accusative
    being more common than ergative for monotransitives). -/
theorem ditrans_indirective_more_common :
    (allDitransProfiles.filter (λ p => p.alignment == .indirective)).length >
    (allDitransProfiles.filter (λ p => p.alignment == .secundative)).length := by
  native_decide

-- ============================================================================
-- §8. Fragment bridges
-- ============================================================================

/-! Theorems verifying that the inline `AlignmentProfile` entries are
    consistent with the grammatical facts described in each language's
    Fragment directory. -/

/-- Dargwa: Fragment says A=ERG, S/P=ABS → Typology says ergative NP
    alignment. -/
theorem dargwa_fragment_bridge :
    Dargwa.Case.agentCase = .erg ∧
    Dargwa.Case.patientCase = .abs ∧
    dargwa.npAlignment = .ergative := ⟨rfl, rfl, rfl⟩

/-- Dargwa: Fragment alignment family is ergative → Typology profile is
    consistently ergative. -/
theorem dargwa_alignment_family_bridge :
    toAlignmentType Dargwa.Case.alignment
    = dargwa.npAlignment := rfl

/-- Japanese: Fragment case inventory contains NOM and ACC → Typology says
    accusative NP alignment. -/
theorem japanese_fragment_bridge :
    .nom ∈ Japanese.Case.caseInventory ∧
    .acc ∈ Japanese.Case.caseInventory ∧
    japanese.npAlignment = .accusative := ⟨by decide, by decide, rfl⟩

/-- Hindi: Fragment split-ergative system perfective → ERG matches
    Typology's ergative NP alignment. -/
theorem hindi_fragment_bridge :
    Alignment.hindiSplit.alignment .perfective = .ergative ∧
    toAlignmentType (Alignment.hindiSplit.alignment .perfective)
      = hindiUrdu.npAlignment := ⟨rfl, rfl⟩

/-- Hindi: Fragment imperfective → ACC matches Typology's accusative
    pronoun alignment. -/
theorem hindi_split_bridge :
    Alignment.hindiSplit.alignment .imperfective = .accusative ∧
    toAlignmentType (Alignment.hindiSplit.alignment .imperfective)
      = hindiUrdu.pronAlignment := ⟨rfl, rfl⟩

-- ============================================================================
-- §9. Bridges to Syntax/Case/Alignment
-- ============================================================================

/-! The typology classifier `AlignmentType` (substrate) and the
    case-assignment functions `_root_.Alignment.X.assignCase`
    (`Syntax/Case/Alignment.lean`) are two views of the same
    alignment dimension. The bridge theorems confirm that the typology's
    `marksAgent`/`marksPatient` Bool projections agree pointwise with what
    the case-assignment functions actually do on the canonical S/A/P inputs. -/

section BridgesToTheoriesAlignment

open Features.Prominence (ArgumentRole)

theorem ergative_function_marks_A :
    (_root_.Alignment.ergative.assignCase .A != _root_.Alignment.ergative.assignCase .S) =
      AlignmentType.ergative.marksAgent := by decide

theorem ergative_function_does_not_mark_P :
    (_root_.Alignment.ergative.assignCase .P != _root_.Alignment.ergative.assignCase .S) =
      AlignmentType.ergative.marksPatient := by decide

theorem accusative_function_marks_P :
    (_root_.Alignment.nominativeAccusative.assignCase .P
        != _root_.Alignment.nominativeAccusative.assignCase .S) =
      AlignmentType.accusative.marksPatient := by decide

theorem accusative_function_does_not_mark_A :
    (_root_.Alignment.nominativeAccusative.assignCase .A
        != _root_.Alignment.nominativeAccusative.assignCase .S) =
      AlignmentType.accusative.marksAgent := by decide

/-- Extended ergative is non-canonical (no `AlignmentType` constructor): it
    groups S with A like accusative does, but marks them with GEN rather than
    NOM. The Cholan non-perfective pattern is captured by the function only. -/
theorem extendedErgative_groups_S_with_A_like_accusative :
    (_root_.Alignment.extendedErgative.assignCase .S
        = _root_.Alignment.extendedErgative.assignCase .A) ∧
    _root_.Alignment.extendedErgative.assignCase .A ≠
      _root_.Alignment.nominativeAccusative.assignCase .A := ⟨rfl, by decide⟩

end BridgesToTheoriesAlignment

end Dixon1994
