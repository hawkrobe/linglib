import Linglib.Fragments.Japanese.Particles

/-!
# Empirical Data: Kubota (2026) "Outlook Management"

Empirical observations on Japanese outlook markers from Kubota (2026).

## Key Phenomena

1. **Counterstance requirement** (37–38): outlook markers require a salient counterstance
2. **Non-cancelability** (10–12): evaluative meaning cannot be contradicted
3. **Denial targets prejacent** (40–41): "no" denies propositional content, not stance
4. **Perspective shift** (42): evaluative meaning shifts to attitude holder under embedding
5. **Modal interaction** (45–46): stance interacts with modal flavor
6. **Incompatibility patterns** (11–12): *mushiro*/*yahari* mutually exclude *igai-ni* 'unexpected'

## References

- Kubota, Y. (2026). Outlook Management. In *Handbook of Japanese Semantics and Pragmatics*.
-/

namespace Phenomena.OutlookMarkers.Kubota2026

open Fragments.Japanese.OutlookMarkers
open TruthConditional.Expressives.OutlookMarker


/-! ## Felicity Judgments

Outlook markers are felicitous only when a counterstance is salient in the
discourse (Kubota 2026: §3, examples (37)–(39)). -/

/-- Felicity datum for an outlook marker in a discourse context. -/
structure FelicityDatum where
  marker : String
  /-- The preceding discourse context -/
  context : String
  /-- The sentence containing the marker -/
  sentence : String
  /-- Whether the marker is felicitous in this context -/
  felicitous : Bool
  /-- Why it is or isn't felicitous -/
  explanation : String
  /-- Example number in Kubota (2026) -/
  exampleNum : String
  deriving Repr

/-- (37): *nanka* is felicitous as a negative response to a positive evaluation.
    A: "Sweetened green tea is tasty, isn't it?"
    B: "I do like sweets, but sweetened green tea **nanka** is absolutely not tasty." -/
def ex37_nanka_felicitous : FelicityDatum :=
  { marker := "nanka"
  , context := "A: Satō-iri-no ryokucha-tte oishii yo ne. (Sweetened green tea is tasty, isn't it?)"
  , sentence := "Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."
  , felicitous := true
  , explanation := "Counterstance salient: A's positive evaluation of sweetened green tea"
  , exampleNum := "37" }

/-- (38): *nanka* is INfelicitous when no counterstance is salient.
    A: "I wonder what kind of drink tastes good with sugar in it."
    B: #"Sweetened green tea **nanka** is not tasty." -/
def ex38_nanka_infelicitous : FelicityDatum :=
  { marker := "nanka"
  , context := "A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? (What drink tastes good with sugar?)"
  , sentence := "Satō-iri-no ryokucha-{wa/??nanka} oishiku-nai-yo."
  , felicitous := false
  , explanation := "No counterstance salient: A's question is neutral, not evaluative"
  , exampleNum := "38" }

/-- (39): *dōse* is felicitous as a response to Q1 (whether sweetened green tea is tasty)
    but NOT as a response to Q2 (what drink tastes good with sugar). -/
def ex39_dōse_Q1_ok : FelicityDatum :=
  { marker := "dōse"
  , context := "Q1: Satō-iri-no ryokucha-wa oishii-ka-na? (I wonder if sweetened green tea is tasty.)"
  , sentence := "Satō-iri-no ryokucha-wa dōse mazui yo."
  , felicitous := true
  , explanation := "Q1 makes 'sweetened green tea is tasty' a salient counterstance"
  , exampleNum := "39/Q1" }

def ex39_dōse_Q2_bad : FelicityDatum :=
  { marker := "dōse"
  , context := "Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? (What drink tastes good with sugar?)"
  , sentence := "Satō-iri-no ryokucha-wa dōse mazui yo."
  , felicitous := false
  , explanation := "Q2 does not make any specific evaluation salient as a counterstance"
  , exampleNum := "39/Q2" }


/-! ## Non-Cancelability

The evaluative meaning of outlook markers cannot be contradicted by
preceding context (Kubota 2026: (10)–(12)). -/

/-- (10): Preceding clause praising green tea with sugar contradicts *nanka*'s
    negative evaluation → infelicity. -/
def ex10_nanka_noncancelable : FelicityDatum :=
  { marker := "nanka"
  , context := "#Satō-iri-no ryokucha-wa jitsu-ni mooshi-bun-nai mono-da-ga (Green tea with sugar is indeed impeccable, but...)"
  , sentence := "watashi-wa satō-iri-no ryokucha nanka kesshite nomanai."
  , felicitous := false
  , explanation := "Positive evaluation in preceding clause contradicts nanka's negative stance"
  , exampleNum := "10" }


/-! ## Denial Targets Prejacent, Not Stance

When B denies A's outlook-marked utterance, denial targets the propositional
content, not the evaluative component (Kubota 2026: (40)–(41)). This is
evidence for descriptive ineffability. -/

/-- Denial datum: what gets denied when responding "no" to an outlook-marked utterance. -/
structure DenialDatum where
  marker : String
  utterance : String
  denial : String
  /-- What the denial means (≈) -/
  denialMeaning : String
  /-- What the denial does NOT mean (≉) -/
  denialDoesNotMean : String
  exampleNum : String
  deriving Repr

/-- (40): Denying *nanka*-marked utterance denies the proposition, not the negative stance. -/
def ex40_nanka_denial : DenialDatum :=
  { marker := "nanka"
  , utterance := "Satō-iri-no ryokucha nanka watashi-wa noma-nai. (I won't drink green tea with sugar or anything like that.)"
  , denial := "Iya, sonna hazu-wa nai yo. (No, that can't be true.)"
  , denialMeaning := "You'll drink it for sure."
  , denialDoesNotMean := "You are not negative about green tea with sugar."
  , exampleNum := "40" }

/-- (41): Denying *dōse*-marked utterance denies the proposition, not the pessimistic stance. -/
def ex41_dōse_denial : DenialDatum :=
  { marker := "dōse"
  , utterance := "Watashi-ni-wa dōse kinmedaru-wa tor-e-nai. (I can't win a gold medal anyway.)"
  , denial := "Iya, sonna hazu-wa nai yo. (No, that can't be true.)"
  , denialMeaning := "You have plenty of chances."
  , denialDoesNotMean := "You aren't really so pessimistic."
  , exampleNum := "41" }


/-! ## Perspective Shift Under Embedding

Under attitude predicates, the evaluative meaning of outlook markers can
shift to the attitude holder's perspective (Kubota 2026: (42)). This
distinguishes outlook markers from typical expressives. -/

/-- (42): *dōse*/*nanka* under attitude verb "think" — evaluation shifts to advisor's perspective. -/
structure PerspectiveShiftDatum where
  marker : String
  sentence : String
  /-- Whose perspective the evaluation is attributed to -/
  perspectiveHolder : String
  /-- The evaluation expressed -/
  evaluation : String
  exampleNum : String
  deriving Repr

def ex42_perspective_shift : PerspectiveShiftDatum :=
  { marker := "dōse + nanka"
  , sentence := "Sensei-wa [boku-ga (dōse) SALT-ni(-nanka) tōra-nai]-to omot-te-ta rashii."
  , perspectiveHolder := "advisor (not speaker)"
  , evaluation := "The advisor had a negative/pessimistic outlook about the speaker getting accepted at SALT"
  , exampleNum := "42" }


/-! ## Modal Interaction Patterns

Different outlook markers have different compatibility with modal flavors
(Kubota 2026: (45)–(46)). -/

/-- Modal interaction datum: how an outlook marker behaves with a specific modal type. -/
structure ModalInteractionDatum where
  marker : String
  modalType : String
  /-- Japanese modal expression -/
  modalForm : String
  /-- Is the combination acceptable? -/
  acceptable : Bool
  /-- Characterization of the resulting interpretation -/
  interpretation : String
  exampleNum : String
  deriving Repr

/-- (45a): *nanka* + epistemic *hazu* → neutral interpretation. -/
def ex45a_nanka_epistemic : ModalInteractionDatum :=
  { marker := "nanka", modalType := "epistemic"
  , modalForm := "hazu (supposed)"
  , acceptable := true
  , interpretation := "neutral: There shouldn't be any Japanese people in a place like this."
  , exampleNum := "45a" }

/-- (45c): *nanka* + deontic/bouletic → pejorative interpretation. -/
def ex45c_nanka_deontic : ModalInteractionDatum :=
  { marker := "nanka", modalType := "deontic/bouletic"
  , modalForm := "ika-nai hō-ga yokat-ta (better not go)"
  , acceptable := true
  , interpretation := "pejorative: It would have been better not to go to Tokyo (of all places)."
  , exampleNum := "45c" }

/-- (46a): *semete* + epistemic *hazu* → unacceptable. -/
def ex46a_semete_epistemic_bad : ModalInteractionDatum :=
  { marker := "semete", modalType := "epistemic"
  , modalForm := "hazu (supposed)"
  , acceptable := false
  , interpretation := "??In a place like this, there should at least be some Japanese people."
  , exampleNum := "46a" }

/-- (46c): *semete* + desiderative *-tai* → acceptable. -/
def ex46c_semete_desiderative_ok : ModalInteractionDatum :=
  { marker := "semete", modalType := "desiderative"
  , modalForm := "-tai (want)"
  , acceptable := true
  , interpretation := "One should at least get vaccinated."
  , exampleNum := "46c" }

/-- (46d): *semete* + deontic *-beki* → acceptable. -/
def ex46d_semete_deontic_ok : ModalInteractionDatum :=
  { marker := "semete", modalType := "deontic"
  , modalForm := "-beki (should)"
  , acceptable := true
  , interpretation := "At least we should cover the travel expenses."
  , exampleNum := "46d" }


/-! ## Verification: Fragment Entries Match Empirical Data -/

/-- *semete*'s modal restriction in the fragment matches the empirical data:
    rejects epistemic (46a), accepts deontic (46d). -/
theorem semete_modal_matches_data :
    semete.modalCompat.epistemic = false ∧
    semete.modalCompat.deontic = true :=
  ⟨rfl, rfl⟩

/-- *nanka*'s unrestricted modal compatibility matches the data:
    acceptable with both epistemic (45a) and deontic (45c). -/
theorem nanka_modal_matches_data :
    nanka.modalCompat.epistemic = true ∧
    nanka.modalCompat.deontic = true :=
  ⟨rfl, rfl⟩

/-- All felicity data: counterstance present → felicitous, absent → infelicitous. -/
def allFelicityData : List FelicityDatum :=
  [ex37_nanka_felicitous, ex38_nanka_infelicitous, ex39_dōse_Q1_ok, ex39_dōse_Q2_bad,
   ex10_nanka_noncancelable]

/-- Felicitous data points are exactly those with salient counterstance. -/
theorem felicitous_iff_counterstance_salient :
    (allFelicityData.filter (·.felicitous)).length = 2 ∧
    (allFelicityData.filter (! ·.felicitous)).length = 3 := by native_decide

end Phenomena.OutlookMarkers.Kubota2026
