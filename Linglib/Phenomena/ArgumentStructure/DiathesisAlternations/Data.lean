import Linglib.Core.RootDimensions

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

open LevinClass DiathesisAlternation

/-- Result of testing whether a verb participates in a diathesis alternation. -/
inductive AlternationResult where
  | participates   -- Verb participates in this alternation
  | blocked        -- Verb does not participate
  | marginal       -- Intermediate or speaker-variable judgment
  deriving DecidableEq, Repr, BEq

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
  , dat_give, dat_send ]

end Phenomena.ArgumentStructure.DiathesisAlternations.Data
