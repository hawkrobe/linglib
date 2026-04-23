import Linglib.Features.Coordination

/-!
# Irish Coordination Morphemes
@cite{haspelmath-2007}

Irish coordination morphemes. Irish is a J-only language for conjunction:
"agus" is the sole conjunctive coordinator. There is no MU (additive
particle) strategy for conjunction attested.

Connection to Typology.lean: `Phenomena.Coordination.Typology.irish`
encodes the structural pattern (a_co_b only, J-only strategy).

-/

namespace Fragments.Irish.Coordination

open Features.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *agus* — conjunction, J particle. Free, prepositive.
    "Sean agus Maire" = "Sean and Maire". -/
def agus : CoordEntry :=
  { form := "agus", gloss := "and"
  , role := .j, boundness := .free }

/-- *no* — disjunction. Free, prepositive.
    "Sean no Maire" = "Sean or Maire". -/
def no_ : CoordEntry :=
  { form := "nó", gloss := "or"
  , role := .disj, boundness := .free }

/-- *na* — negative disjunction / comparative particle.
    "ni Sean na Maire" = "neither Sean nor Maire".
    Also used in comparatives: "nios mo na" = "bigger than". -/
def na_ : CoordEntry :=
  { form := "ná", gloss := "nor, than"
  , role := .negDisj, boundness := .free
  , note := "also comparative particle" }

/-- *ach* — adversative conjunction.
    "Ta se fuar ach tirim" = "It is cold but dry". -/
def ach : CoordEntry :=
  { form := "ach", gloss := "but"
  , role := .advers, boundness := .free }

def allEntries : List CoordEntry :=
  [agus, no_, na_, ach]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Irish coordination morphemes are free (no bound clitics). -/
theorem all_free :
    allEntries.all (·.boundness == .free) = true := by
  native_decide

/-- Irish has exactly one conjunction morpheme (J-only, no MU). -/
theorem one_conjunction :
    (allEntries.filter (·.role == .j)).length = 1 := by
  native_decide

end Fragments.Irish.Coordination
