import Linglib.Syntax.Category.Coordinator

/-!
# Irish Coordination Morphemes
[haspelmath-2007]

Irish coordination morphemes. Irish is a J-only language for conjunction:
"agus" is the sole conjunctive coordinator. There is no MU (additive
particle) strategy for conjunction attested.

Connection to Typology.lean: `Haspelmath2007.irish`
encodes the structural pattern (a_co_b only, J-only strategy).

-/

namespace Irish.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *agus* — conjunction, J particle. Free, prepositive.
    "Sean agus Maire" = "Sean and Maire". -/
def agus : Coordinator :=
  { form := "agus", gloss := "and"
  , role := .j, kind := .free }

/-- *no* — disjunction. Free, prepositive.
    "Sean no Maire" = "Sean or Maire". -/
def no_ : Coordinator :=
  { form := "nó", gloss := "or"
  , role := .disj, kind := .free }

/-- *na* — negative disjunction / comparative particle.
    "ni Sean na Maire" = "neither Sean nor Maire".
    Also used in comparatives: "nios mo na" = "bigger than". -/
def na_ : Coordinator :=
  { form := "ná", gloss := "nor, than"
  , role := .negDisj, kind := .free
  , note := "also comparative particle" }

/-- *ach* — adversative conjunction.
    "Ta se fuar ach tirim" = "It is cold but dry". -/
def ach : Coordinator :=
  { form := "ach", gloss := "but"
  , role := .advers, kind := .free }

def allEntries : List Coordinator :=
  [agus, no_, na_, ach]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Irish coordination morphemes are free (no bound clitics). -/
theorem all_free :
    allEntries.all (fun e => decide (e.kind = .free)) = true := by
  decide

/-- Irish has exactly one conjunction morpheme (J-only, no MU). -/
theorem one_conjunction :
    (allEntries.filter (·.role == .j)).length = 1 := by
  decide

end Irish.Coordination
