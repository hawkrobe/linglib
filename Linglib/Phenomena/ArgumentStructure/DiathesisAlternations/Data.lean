import Linglib.Core.Lexical.DiathesisAlternation

/-!
# Diathesis Alternation Data
@cite{levin-1993}

Theory-neutral empirical data on diathesis alternation participation.

The four verbs *break*, *cut*, *hit*, *touch* form a canonical diagnostic
quadruple (@cite{levin-1993}:5–10): each participates in a distinct subset of
the causative/inchoative, middle, conative, and body-part possessor
ascension alternations. Additional verbs demonstrate the locative
(*spray/load*) and dative (*give/send*) alternations.

| Verb | Class | CI | Mid | Con | BPPA |
|------|-------|----|-----|-----|------|
| break | 45.1 | ✓ | ✓ | ✗ | ✗ |
| cut | 21.1 | ✗ | ✓ | ✓ | ✓ |
| hit | 18.1 | ✗ | ✗ | ✓ | ✓ |
| touch | 20 | ✗ | ✗ | ✗ | ✓ |
-/

namespace Phenomena.ArgumentStructure.DiathesisAlternations.Data

open Core.Verbs
open LevinClass DiathesisAlternation

/-- Result of testing whether a verb participates in a diathesis alternation. -/
inductive AlternationResult where
  | participates   -- Verb participates in this alternation
  | blocked        -- Verb does not participate
  | marginal       -- Intermediate or speaker-variable judgment
  deriving DecidableEq, Repr

/-- A single alternation judgment for a verb–alternation pair. -/
structure AlternationDatum where
  verbForm : String
  verbClass : LevinClass
  alternation : DiathesisAlternation
  result : AlternationResult
  sentence : String
  variant : Option String := none
  note : String := ""
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § Break (45.1) — CI ✓, Mid ✓, Con ✗, BPPA ✗
-- ════════════════════════════════════════════════════

def ci_break : AlternationDatum :=
  { verbForm := "break"
  , verbClass := .break_
  , alternation := .causativeInchoative
  , result := .participates
  , sentence := "The little boy broke the window."
  , variant := some "The window broke."
  , note := "Levin p. 9, ex. (22)" }

def mid_break : AlternationDatum :=
  { verbForm := "break"
  , verbClass := .break_
  , alternation := .middle
  , result := .participates
  , sentence := "Crystal vases break easily."
  , note := "Levin p. 6, ex. (13b)" }

def con_break : AlternationDatum :=
  { verbForm := "break"
  , verbClass := .break_
  , alternation := .conative
  , result := .blocked
  , sentence := "*Janet broke at the vase."
  , note := "No contact or motion component; Levin p. 6, ex. (14b)" }

def bppa_break : AlternationDatum :=
  { verbForm := "break"
  , verbClass := .break_
  , alternation := .bodyPartPossessorAscension
  , result := .blocked
  , sentence := "*Janet broke Bill on the finger."
  , note := "No contact component; Levin p. 7, ex. (16b)" }

-- ════════════════════════════════════════════════════
-- § Cut (21.1) — CI ✗, Mid ✓, Con ✓, BPPA ✓
-- ════════════════════════════════════════════════════

def ci_cut : AlternationDatum :=
  { verbForm := "cut"
  , verbClass := .cut
  , alternation := .causativeInchoative
  , result := .blocked
  , sentence := "*The string cut."
  , note := "Blocked: instrument specification requires an agent (Levin p. 9, ex. 23b)" }

def mid_cut : AlternationDatum :=
  { verbForm := "cut"
  , verbClass := .cut
  , alternation := .middle
  , result := .participates
  , sentence := "The bread cuts easily."
  , note := "Levin p. 6, ex. (13a)" }

def con_cut : AlternationDatum :=
  { verbForm := "cut"
  , verbClass := .cut
  , alternation := .conative
  , result := .participates
  , sentence := "Margaret cut at the bread."
  , note := "Levin p. 6, ex. (14a)" }

def bppa_cut : AlternationDatum :=
  { verbForm := "cut"
  , verbClass := .cut
  , alternation := .bodyPartPossessorAscension
  , result := .participates
  , sentence := "Margaret cut Bill on the arm."
  , note := "Levin p. 7, ex. (15b)" }

-- ════════════════════════════════════════════════════
-- § Hit (18.1) — CI ✗, Mid ✗, Con ✓, BPPA ✓
-- ════════════════════════════════════════════════════

def ci_hit : AlternationDatum :=
  { verbForm := "hit"
  , verbClass := .hit
  , alternation := .causativeInchoative
  , result := .blocked
  , sentence := "*The door hit."
  , note := "No change of state or causation component; Levin p. 9, ex. (25b)" }

def mid_hit : AlternationDatum :=
  { verbForm := "hit"
  , verbClass := .hit
  , alternation := .middle
  , result := .blocked
  , sentence := "*Door frames hit easily."
  , note := "No change of state component; Levin p. 6, ex. (13d)" }

def con_hit : AlternationDatum :=
  { verbForm := "hit"
  , verbClass := .hit
  , alternation := .conative
  , result := .participates
  , sentence := "Carla hit at the door."
  , note := "Levin p. 6, ex. (14d)" }

def bppa_hit : AlternationDatum :=
  { verbForm := "hit"
  , verbClass := .hit
  , alternation := .bodyPartPossessorAscension
  , result := .participates
  , sentence := "Carla hit Bill on the back."
  , note := "Levin p. 7, ex. (18b)" }

-- ════════════════════════════════════════════════════
-- § Touch (20) — CI ✗, Mid ✗, Con ✗, BPPA ✓
-- ════════════════════════════════════════════════════

def ci_touch : AlternationDatum :=
  { verbForm := "touch"
  , verbClass := .touch
  , alternation := .causativeInchoative
  , result := .blocked
  , sentence := "*The cat touched."
  , note := "No change of state or causation component; Levin p. 9, ex. (24b)" }

def mid_touch : AlternationDatum :=
  { verbForm := "touch"
  , verbClass := .touch
  , alternation := .middle
  , result := .blocked
  , sentence := "*Cats touch easily."
  , note := "No change of state component; Levin p. 6, ex. (13c)" }

def con_touch : AlternationDatum :=
  { verbForm := "touch"
  , verbClass := .touch
  , alternation := .conative
  , result := .blocked
  , sentence := "*Terry touched at the cat."
  , note := "No motion component; Levin p. 6, ex. (14c)" }

def bppa_touch : AlternationDatum :=
  { verbForm := "touch"
  , verbClass := .touch
  , alternation := .bodyPartPossessorAscension
  , result := .participates
  , sentence := "Terry touched Bill on the shoulder."
  , note := "Levin p. 7, ex. (17b)" }

-- ════════════════════════════════════════════════════
-- § Push (12) — Con ✓
-- ════════════════════════════════════════════════════

def con_push : AlternationDatum :=
  { verbForm := "push"
  , verbClass := .pushPull
  , alternation := .conative
  , result := .participates
  , sentence := "She pushed at the door." }

-- ════════════════════════════════════════════════════
-- § Spray/Load (9.7) — Locative ✓
-- ════════════════════════════════════════════════════

def loc_spray : AlternationDatum :=
  { verbForm := "spray"
  , verbClass := .sprayLoad
  , alternation := .locative
  , result := .participates
  , sentence := "She sprayed paint on the wall."
  , variant := some "She sprayed the wall with paint." }

def loc_load : AlternationDatum :=
  { verbForm := "load"
  , verbClass := .sprayLoad
  , alternation := .locative
  , result := .participates
  , sentence := "She loaded hay onto the truck."
  , variant := some "She loaded the truck with hay." }

-- ════════════════════════════════════════════════════
-- § Give/Send (13.1/11.1) — Dative ✓
-- ════════════════════════════════════════════════════

def dat_give : AlternationDatum :=
  { verbForm := "give"
  , verbClass := .give
  , alternation := .dative
  , result := .participates
  , sentence := "She gave a book to him."
  , variant := some "She gave him a book." }

def dat_send : AlternationDatum :=
  { verbForm := "send"
  , verbClass := .send
  , alternation := .dative
  , result := .participates
  , sentence := "She sent a package to him."
  , variant := some "She sent him a package." }

-- ════════════════════════════════════════════════════
-- § Benefactive (2.2) — Build/Create ✓
-- ════════════════════════════════════════════════════

def ben_carve : AlternationDatum :=
  { verbForm := "carve"
  , verbClass := .build
  , alternation := .benefactive
  , result := .participates
  , sentence := "Martha carved a toy for the baby."
  , variant := some "Martha carved the baby a toy."
  , note := "Levin p. 49, ex. (121)" }

-- ════════════════════════════════════════════════════
-- § Substance/Source (1.1.3) — Emission ✓
-- ════════════════════════════════════════════════════

def ss_radiate : AlternationDatum :=
  { verbForm := "radiate"
  , verbClass := .substanceEmission
  , alternation := .substanceSource
  , result := .participates
  , sentence := "Heat radiates from the sun."
  , variant := some "The sun radiates heat."
  , note := "Levin p. 32, ex. (36)" }

-- ════════════════════════════════════════════════════
-- § Material/Product (2.4.1) — Build ✓
-- ════════════════════════════════════════════════════

def mp_carve : AlternationDatum :=
  { verbForm := "carve"
  , verbClass := .build
  , alternation := .materialProduct
  , result := .participates
  , sentence := "Martha carved a toy out of the piece of wood."
  , variant := some "Martha carved the piece of wood into a toy."
  , note := "Levin p. 56, ex. (147)" }

-- ════════════════════════════════════════════════════
-- § Unspecified Object (1.2.1) — Eat ✓, Devour ✗
-- ════════════════════════════════════════════════════

def uo_eat : AlternationDatum :=
  { verbForm := "eat"
  , verbClass := .eat
  , alternation := .unspecifiedObject
  , result := .participates
  , sentence := "Mike ate the cake."
  , variant := some "Mike ate."
  , note := "Levin p. 33, ex. (38)" }

def uo_devour : AlternationDatum :=
  { verbForm := "devour"
  , verbClass := .devour
  , alternation := .unspecifiedObject
  , result := .blocked
  , sentence := "*Mike devoured."
  , note := "Devour requires an expressed object (not listed in §1.2.1)" }

-- ════════════════════════════════════════════════════
-- § Understood Reciprocal Object (1.2.4) — Social Interaction ✓
-- ════════════════════════════════════════════════════

def uro_meet : AlternationDatum :=
  { verbForm := "meet"
  , verbClass := .socialInteraction
  , alternation := .understoodReciprocalObject
  , result := .participates
  , sentence := "Anne met Cathy."
  , variant := some "Anne and Cathy met."
  , note := "Levin p. 36, ex. (59)" }

-- ════════════════════════════════════════════════════
-- § There-Insertion (6.1) — Exist ✓, Appear ✓
-- ════════════════════════════════════════════════════

def ti_develop : AlternationDatum :=
  { verbForm := "develop"
  , verbClass := .appear
  , alternation := .thereInsertion
  , result := .participates
  , sentence := "A problem developed."
  , variant := some "There developed a problem."
  , note := "Levin p. 89, ex. (321)" }

def ti_appear : AlternationDatum :=
  { verbForm := "appear"
  , verbClass := .appear
  , alternation := .thereInsertion
  , result := .participates
  , sentence := "A ship appeared on the horizon."
  , variant := some "There appeared a ship on the horizon."
  , note := "Levin p. 89, ex. (322)" }

-- ════════════════════════════════════════════════════
-- § Locative Inversion (6.2) — Exist ✓
-- ════════════════════════════════════════════════════

def li_live : AlternationDatum :=
  { verbForm := "live"
  , verbClass := .exist
  , alternation := .locativeInversion
  , result := .participates
  , sentence := "An old woman lives in the woods."
  , variant := some "In the woods lives an old woman."
  , note := "Levin p. 92, ex. (335)" }

-- ════════════════════════════════════════════════════
-- § Instrument Subject (3.3) — Break ✓, Cut ✗
-- ════════════════════════════════════════════════════

def is_break : AlternationDatum :=
  { verbForm := "break"
  , verbClass := .break_
  , alternation := .instrumentSubject
  , result := .participates
  , sentence := "David broke the window with a hammer."
  , variant := some "The hammer broke the window."
  , note := "Levin p. 80, ex. (275)" }

def is_eat : AlternationDatum :=
  { verbForm := "eat"
  , verbClass := .eat
  , alternation := .instrumentSubject
  , result := .blocked
  , sentence := "*The spoon ate the ice cream."
  , note := "Enabling instrument, not intermediary (Levin p. 80, ex. 276)" }

-- ════════════════════════════════════════════════════
-- § Induced Action (1.1.2.2) — Manner of Motion ✓
-- ════════════════════════════════════════════════════

def ia_run : AlternationDatum :=
  { verbForm := "run"
  , verbClass := .mannerOfMotion
  , alternation := .inducedAction
  , result := .participates
  , sentence := "The horse ran."
  , variant := some "Bill ran the horse."
  , note := "Levin §1.1.2.2" }

-- ════════════════════════════════════════════════════
-- § Understood Body-Part Object (1.2.2) — Body ✓
-- ════════════════════════════════════════════════════

def ubpo_wave : AlternationDatum :=
  { verbForm := "wave"
  , verbClass := .bodyProcess
  , alternation := .understoodBodyPartObject
  , result := .participates
  , sentence := "Bill waved his hand."
  , variant := some "Bill waved."
  , note := "Levin §1.2.2" }

-- ════════════════════════════════════════════════════
-- § Understood Reflexive Object (1.2.3) — Grooming ✓
-- ════════════════════════════════════════════════════

def uro_wash : AlternationDatum :=
  { verbForm := "wash"
  , verbClass := .dress
  , alternation := .understoodReflexiveObject
  , result := .participates
  , sentence := "Bill washed himself."
  , variant := some "Bill washed."
  , note := "Levin §1.2.3" }

-- ════════════════════════════════════════════════════
-- § Total Transformation (2.4.3) — Turn ✓
-- ════════════════════════════════════════════════════

def tt_turn : AlternationDatum :=
  { verbForm := "turn"
  , verbClass := .turn
  , alternation := .totalTransformation
  , result := .participates
  , sentence := "The witch turned the prince into a frog."
  , note := "Levin §2.4.3" }

-- ════════════════════════════════════════════════════
-- § Way Construction (7.4) — Manner of Motion ✓
-- ════════════════════════════════════════════════════

def way_elbow : AlternationDatum :=
  { verbForm := "elbow"
  , verbClass := .mannerOfMotion
  , alternation := .wayConstruction
  , result := .participates
  , sentence := "She elbowed her way through the crowd."
  , note := "Levin §7.4" }

-- ════════════════════════════════════════════════════
-- § Cognate Object (7.1) — Manner of Speaking ✓, Manner of Motion ✓
-- ════════════════════════════════════════════════════

def co_laugh : AlternationDatum :=
  { verbForm := "laugh"
  , verbClass := .mannerOfSpeaking
  , alternation := .cognateObject
  , result := .participates
  , sentence := "She laughed a bitter laugh."
  , note := "Levin §7.1" }

def co_run : AlternationDatum :=
  { verbForm := "run"
  , verbClass := .mannerOfMotion
  , alternation := .cognateObject
  , result := .participates
  , sentence := "He ran a good race."
  , note := "Levin §7.1" }

-- ════════════════════════════════════════════════════
-- § Directional Phrase (7.8) — Manner of Motion ✓
-- ════════════════════════════════════════════════════

def dp_run : AlternationDatum :=
  { verbForm := "run"
  , verbClass := .mannerOfMotion
  , alternation := .directionalPhrase
  , result := .participates
  , sentence := "She ran to the store."
  , note := "Levin §7.8" }

-- ════════════════════════════════════════════════════
-- § Verbal Passive (5.1) — Most Transitive ✓, Measure ✗
-- ════════════════════════════════════════════════════

def vp_break : AlternationDatum :=
  { verbForm := "break"
  , verbClass := .break_
  , alternation := .verbalPassive
  , result := .participates
  , sentence := "The window was broken by the boy."
  , note := "Levin §5.1" }

def vp_give : AlternationDatum :=
  { verbForm := "give"
  , verbClass := .give
  , alternation := .verbalPassive
  , result := .participates
  , sentence := "The book was given to her."
  , note := "Levin §5.1" }

def vp_eat : AlternationDatum :=
  { verbForm := "eat"
  , verbClass := .eat
  , alternation := .verbalPassive
  , result := .participates
  , sentence := "The cake was eaten."
  , note := "Levin §5.1" }

def vp_see : AlternationDatum :=
  { verbForm := "see"
  , verbClass := .see
  , alternation := .verbalPassive
  , result := .participates
  , sentence := "The ship was seen on the horizon."
  , note := "Levin §5.1" }

def vp_measure : AlternationDatum :=
  { verbForm := "weigh"
  , verbClass := .measure
  , alternation := .verbalPassive
  , result := .blocked
  , sentence := "*Five pounds are weighed by this box."
  , note := "Stative measure verbs resist passivization (Levin §5.1)" }

-- ════════════════════════════════════════════════════
-- § Prepositional Passive (5.2) — Unergative ✓
-- ════════════════════════════════════════════════════

def pp_sleep : AlternationDatum :=
  { verbForm := "sleep"
  , verbClass := .assumePosition
  , alternation := .prepositionalPassive
  , result := .participates
  , sentence := "The bed was slept in."
  , note := "Levin §5.2 — classic unergative diagnostic" }

def pp_talk : AlternationDatum :=
  { verbForm := "talk"
  , verbClass := .mannerOfSpeaking
  , alternation := .prepositionalPassive
  , result := .participates
  , sentence := "The matter was talked about."
  , note := "Levin §5.2" }

-- ════════════════════════════════════════════════════
-- § Swarm (2.3.4) — Existence/Motion ✓
-- ════════════════════════════════════════════════════

def sw_swarm : AlternationDatum :=
  { verbForm := "swarm"
  , verbClass := .exist
  , alternation := .swarm
  , result := .participates
  , sentence := "Bees swarmed in the garden."
  , variant := some "The garden swarmed with bees."
  , note := "Levin §2.3.4" }

def sw_crawl : AlternationDatum :=
  { verbForm := "crawl"
  , verbClass := .mannerOfMotion
  , alternation := .swarm
  , result := .participates
  , sentence := "Ants crawled on the counter."
  , variant := some "The counter crawled with ants."
  , note := "Levin §2.3.4" }

-- ════════════════════════════════════════════════════
-- § Induced Action (1.1.2.2) — additional
-- ════════════════════════════════════════════════════

def ia_walk : AlternationDatum :=
  { verbForm := "walk"
  , verbClass := .mannerOfMotion
  , alternation := .inducedAction
  , result := .participates
  , sentence := "The dog walked."
  , variant := some "She walked the dog."
  , note := "Levin §1.1.2.2" }

def ia_appear : AlternationDatum :=
  { verbForm := "appear"
  , verbClass := .appear
  , alternation := .inducedAction
  , result := .blocked
  , sentence := "*She appeared the ghost."
  , note := "Unaccusative verbs resist induced action (no agentive S)" }

-- ════════════════════════════════════════════════════
-- § Collections
-- ════════════════════════════════════════════════════

/-- The canonical diagnostic quadruple. -/
def canonicalData : List AlternationDatum :=
  [ ci_break, mid_break, con_break, bppa_break
  , ci_cut, mid_cut, con_cut, bppa_cut
  , ci_hit, mid_hit, con_hit, bppa_hit
  , ci_touch, mid_touch, con_touch, bppa_touch ]

/-- All alternation data including class-specific alternations. -/
def allData : List AlternationDatum :=
  canonicalData ++
  [ con_push
  , loc_spray, loc_load
  , dat_give, dat_send
  , ben_carve
  , ss_radiate
  , mp_carve
  , uo_eat, uo_devour
  , uro_meet
  , ti_develop, ti_appear
  , li_live
  , is_break, is_eat
  , ia_run, ia_walk, ia_appear
  , ubpo_wave
  , uro_wash
  , tt_turn
  , way_elbow
  , co_laugh, co_run
  , dp_run
  , vp_break, vp_give, vp_eat, vp_see, vp_measure
  , pp_sleep, pp_talk
  , sw_swarm, sw_crawl ]

end Phenomena.ArgumentStructure.DiathesisAlternations.Data
