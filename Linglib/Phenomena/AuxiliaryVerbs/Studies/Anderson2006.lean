import Linglib.Phenomena.AuxiliaryVerbs.Typology
import Linglib.Phenomena.AuxiliaryVerbs.NegativeAuxiliaries
import Linglib.Phenomena.AuxiliaryVerbs.Selection

/-!
# Anderson (2006): Auxiliary Verb Constructions
@cite{anderson-2006}

Cross-linguistic typology of auxiliary verb constructions (AVCs), establishing
a five-pattern classification based on how inflection distributes between
auxiliary and lexical verb.

## Key contributions formalized

1. **Five-pattern inflectional typology** (`InflPattern`): auxHeaded, lexHeaded,
   doubled, split, splitDoubled — defined in `Typology.lean`, verified here
2. **Semantic head invariant**: the lexical verb is always the semantic head,
   regardless of where inflection sits
3. **Typed inflectional distribution**: `InflDistribution` (from `Core.Morphology`)
   records which `MorphCategory` values each element hosts, replacing ad-hoc
   string lists in Fragment files
4. **Grammaticalization cline**: full verb → auxiliary → clitic → affix → zero

## Coverage

Data from 7 languages (8 data points): English (aux-headed), Doyayo (split),
Gorum (doubled), Jakaltek (split), Pipil (split + lex-headed), Finnish (split),
Hemba (split/doubled). All five patterns attested.
-/

namespace Phenomena.AuxiliaryVerbs.Studies.Anderson2006

open Phenomena.AuxiliaryVerbs.Typology
open Phenomena.AuxiliaryVerbs.NegativeAuxiliaries (NegStrategy)
open Phenomena.AuxiliaryVerbs.Selection
open Core.Morphology (InflDistribution MorphCategory)

/-! ## Grammaticalization Cline

@cite{anderson-2006} Ch 7: auxiliaries arise diachronically from full verbs
and may further grammaticalize through clitic and affix stages. The cline
is universally unidirectional: movement is always toward greater
morphological boundedness. -/

/-- Stage on Anderson's grammaticalization cline for auxiliary elements. -/
inductive GramStage where
  | fullVerb    -- lexical verb with full argument structure
  | auxiliary   -- grammaticalized verb, restricted morphosyntax
  | clitic      -- phonologically reduced, syntactically dependent
  | affix       -- bound morpheme, part of the verbal word
  | zero        -- no overt marker (grammaticalization endpoint)
  deriving DecidableEq, Repr, BEq

/-- Boundedness increases monotonically along the cline. -/
def GramStage.boundedness : GramStage → Nat
  | .fullVerb  => 0
  | .auxiliary => 1
  | .clitic    => 2
  | .affix     => 3
  | .zero      => 4

/-- The cline is strictly ordered: each stage is more bound than the previous. -/
theorem cline_strictly_ordered :
    GramStage.fullVerb.boundedness < GramStage.auxiliary.boundedness ∧
    GramStage.auxiliary.boundedness < GramStage.clitic.boundedness ∧
    GramStage.clitic.boundedness < GramStage.affix.boundedness ∧
    GramStage.affix.boundedness < GramStage.zero.boundedness :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The grammaticalization cline maps to `MorphStatus` categories.
    Auxiliaries and full verbs are free words; clitics and affixes map to
    their respective statuses; zero has no overt realization. -/
def GramStage.toMorphStatus : GramStage → Option Core.Morphology.MorphStatus
  | .fullVerb  => some .freeWord
  | .auxiliary => some .freeWord
  | .clitic    => some .simpleClitic
  | .affix     => some .inflAffix
  | .zero      => none

/-- Negative auxiliary strategies map to stages on the cline:
    neg verb = auxiliary stage, neg affix = affix stage,
    neg particle = auxiliary stage (free word). -/
def negStrategyStage : NegStrategy → GramStage
  | .negVerb     => .auxiliary
  | .negAffix    => .affix
  | .negParticle => .auxiliary

/-- Negative affixes are further along the cline than negative verbs. -/
theorem negAffix_more_grammaticalized :
    (negStrategyStage .negAffix).boundedness >
    (negStrategyStage .negVerb).boundedness := by decide

/-! ## Source Constructions

@cite{anderson-2006} identifies four main diachronic sources for AVCs.
These are the construction types from which auxiliaries grammaticalize. -/

/-- Diachronic source construction from which an AVC grammaticalizes. -/
inductive AVCSource where
  /-- Serial verb constructions: two verbs in sequence, one
      grammaticalizes into an auxiliary. Common in West African, SE Asian. -/
  | serialVerb
  /-- Complement-taking verb: matrix verb takes clausal complement,
      the matrix verb grammaticalizes. Common source for modals. -/
  | complementTaking
  /-- Motion verb: 'go'/'come' grammaticalize into future/past markers.
      Cross-linguistically one of the most common paths. -/
  | motionVerb
  /-- Postural verb: 'sit'/'stand'/'lie' grammaticalize into
      progressive/habitual aspect markers. -/
  | posturalVerb
  deriving DecidableEq, Repr, BEq

/-! ## Pattern Coverage Theorems -/

/-- All five of Anderson's inflectional patterns are attested in current data. -/
theorem five_patterns_attested :
    allData.any (·.inflPattern == .auxHeaded) = true ∧
    allData.any (·.inflPattern == .lexHeaded) = true ∧
    allData.any (·.inflPattern == .doubled) = true ∧
    allData.any (·.inflPattern == .split) = true ∧
    allData.any (·.inflPattern == .splitDoubled) = true :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

/-! ## Structural Theorems on Distribution

These theorems verify structural properties of the typed `InflDistribution`
data, connecting Fragment-level category lists to Anderson's pattern
classification. -/

/-- In Gorum's doubled AVC, aux and lex host exactly the same categories. -/
theorem gorum_doubled_same_categories :
    let dist := Fragments.Gorum.AuxiliaryVerbs.inflDistribution
    dist.onAux == dist.onLex = true := by native_decide

/-- In Doyayo's split AVC, aux and lex host disjoint category types. -/
theorem doyayo_split_disjoint :
    let dist := Fragments.Doyayo.AuxiliaryVerbs.inflDistribution
    dist.onAux.all (fun c => !dist.onLex.contains c) = true := by native_decide

/-- In Pipil's split AVC, aux and lex host disjoint category types. -/
theorem pipil_split_disjoint :
    let dist := Fragments.Pipil.AuxiliaryVerbs.inflDistribution
    dist.onAux.all (fun c => !dist.onLex.contains c) = true := by native_decide

/-- In Finnish's split AVC, aux and lex host disjoint category types.
    (`.stem` on the lex side is a base, not an inflectional overlap.) -/
theorem finnish_split_disjoint :
    let dist := Fragments.Finnish.Negation.finnishNegDistribution
    dist.onAux.all (fun c => !dist.onLex.contains c) = true := by native_decide

/-- Jakaltek's split distributes agreement across both elements — absolutive
    on AUX and ergative on LV. At the `MorphCategory` level, both are
    `.agreement`, so the split is *within* a single category type rather than
    *between* category types. This is the correct representation: Anderson
    classifies Jakaltek as split despite the shared `.agreement` label because
    the specific agreement relations (absolutive vs. ergative) differ. -/
theorem jakaltek_split_within_agreement :
    let dist := Fragments.Jakaltek.AuxiliaryVerbs.inflDistribution
    dist.onAux.contains .agreement = true ∧
    dist.onLex.contains .agreement = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- In Pipil's lex-headed AVC, the auxiliary hosts no inflection. -/
theorem pipil_lexHeaded_aux_empty :
    Fragments.Pipil.AuxiliaryVerbs.lexHeadedDistribution.onAux = [] := rfl

/-- In Hemba's split/doubled AVC, agreement is doubled (on both elements),
    while tense is AUX-only and mood is LV-only. This is the defining
    characteristic of the split/doubled pattern: some categories are shared
    (doubled) while others are exclusive to one element (split). -/
theorem hemba_splitDoubled_agreement_doubled :
    let dist := Fragments.Hemba.AuxiliaryVerbs.inflDistribution
    dist.onAux.contains .agreement = true ∧
    dist.onLex.contains .agreement = true ∧
    dist.onAux.contains .tense = true ∧
    dist.onLex.contains .tense = false ∧
    dist.onAux.contains .mood = false ∧
    dist.onLex.contains .mood = true := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide, by native_decide⟩

/-! ## Dual Headedness

Anderson's central insight: AVCs have two distinct notions of head.
The semantic head (content provider) is always the lexical verb.
The inflectional host varies by pattern. This mismatch is what makes
AVCs typologically distinctive. -/

/-- The semantic head and inflectional host coincide only in lex-headed AVCs.
    In all other patterns, they diverge: the semantic head is always the
    lexical verb, but inflection may sit on the auxiliary. -/
theorem heads_coincide_iff_lexHeaded (p : InflPattern) :
    (p.semanticHead == p.inflHost) = (p == .lexHeaded) := by
  cases p <;> rfl

/-! ## Negative Auxiliaries as AVCs

@cite{anderson-2006} treats negative auxiliaries (Finnish *ei*, Komi *oz*)
as a special case of aux-headed AVCs: the negative element IS the auxiliary,
hosting inflection that the lexical verb would otherwise carry. -/

/-- Negative verb strategy creates aux-headed AVCs. -/
theorem negVerb_creates_auxHeaded :
    NegStrategy.negVerb.expectedInflPattern = some InflPattern.auxHeaded := rfl

/-- Non-verbal negation strategies do not create AVCs. -/
theorem negAffix_no_avc :
    NegStrategy.negAffix.expectedInflPattern = none := rfl
theorem negParticle_no_avc :
    NegStrategy.negParticle.expectedInflPattern = none := rfl

/-! ## LV Form Predictions (Anderson's Table 2.3)

Anderson predicts the verb form of the lexical verb from the inflectional
pattern. Aux-headed AVCs have a nonfinite LV (infinitive/participle);
all other patterns have a finite LV (carrying at least some inflection).
This is formalized in `Typology.lvVerbForm` and verified here. -/

/-- Aux-headed → nonfinite LV. -/
theorem auxHeaded_predicts_nonfinite_lv :
    InflPattern.auxHeaded.lvVerbForm = UD.VerbForm.Inf := rfl

/-- Lex-headed → finite LV. -/
theorem lexHeaded_predicts_finite_lv :
    InflPattern.lexHeaded.lvVerbForm = UD.VerbForm.Fin := rfl

/-- Doubled → finite LV. -/
theorem doubled_predicts_finite_lv :
    InflPattern.doubled.lvVerbForm = UD.VerbForm.Fin := rfl

/-- Split → finite LV. -/
theorem split_predicts_finite_lv :
    InflPattern.split.lvVerbForm = UD.VerbForm.Fin := rfl

/-- Split/doubled → finite LV. -/
theorem splitDoubled_predicts_finite_lv :
    InflPattern.splitDoubled.lvVerbForm = UD.VerbForm.Fin := rfl

/-! ## Bridge to Auxiliary Selection

Be/have auxiliary selection (`Selection.lean`) operates within aux-headed
AVCs: the question of *which* auxiliary appears presupposes the auxiliary
hosts inflection. All split-auxiliary languages in `Selection.allData`
are aux-headed (the auxiliary carries tense, the LV is a past participle). -/

/-- Auxiliary selection presupposes aux-headed pattern: the selecting
    auxiliary hosts tense/agreement (is the inflectional head). -/
theorem selection_presupposes_auxHeaded :
    InflPattern.auxHeaded.inflHost = .aux := rfl

/-- In aux-headed AVCs with be/have selection, the LV is nonfinite
    (past participle). This connects Selection's `selectedAux` to
    Typology's `lvVerbForm`. -/
theorem selection_lv_is_nonfinite :
    InflPattern.auxHeaded.lvVerbForm = UD.VerbForm.Inf := rfl

/-- Italian *arrivare* (Selection datum) selects *be* and lives in an
    aux-headed system where the LV is nonfinite: *è arrivat-o*
    (AUX.3SG arrive-PTCP.M.SG). -/
theorem italian_selection_is_auxHeaded :
    italianArrivare.selectionRule = .split ∧
    canonicalSelection italianArrivare.transitivityClass = .be := ⟨rfl, rfl⟩

end Phenomena.AuxiliaryVerbs.Studies.Anderson2006
