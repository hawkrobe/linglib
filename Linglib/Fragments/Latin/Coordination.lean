import Linglib.Core.Coordination

/-!
# Latin Coordination Morphemes
@cite{haspelmath-2007}

Latin has a rich coordination system with both free and bound forms.
The J/MU decomposition (@cite{mitrovic-sauerland-2014}, @cite{mitrovic-sauerland-2016}) maps cleanly:

- *et* — J, free, prepositive: "A et B"
- *-que* — MU, bound enclitic, postpositive: "A B-que" (= "A and B")
- *atque*/*ac* — emphatic J variant (before consonants: *ac*)
- *neque*/*nec* — negative coordination ("neither...nor")

The *et...et* pattern ("both...and") and *neque...neque* pattern are
bisyndetic uses of J particles.

Connection to Typology.lean: `Phenomena.Coordination.Typology.latin`
encodes the structural patterns (a_co_b, a_b'co, co'a_b'co).

-/

namespace Fragments.Latin.Coordination

open Core.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *et* — primary conjunction, J particle. Free, prepositive.
    "Caesar et Brutus" = "Caesar and Brutus".
    Also used correlatively: "et A et B" = "both A and B". -/
def et : CoordEntry :=
  { form := "et", gloss := "and"
  , role := .j, boundness := .free
  , correlative := true }

/-- *-que* — enclitic conjunction, MU particle. Bound, postpositive.
    "senatus populusque" = "senate and people".
    Historically connected to the additive/inclusive particle. -/
def que : CoordEntry :=
  { form := "-que", gloss := "and (enclitic)"
  , role := .mu, boundness := .bound
  , alsoAdditive := true
  , note := "postpositive enclitic; archaic/formal register" }

/-- *atque* / *ac* — emphatic conjunction, J variant.
    *ac* before consonants, *atque* before vowels.
    "atque" < *ad-que (lit. "and to that"). -/
def atque : CoordEntry :=
  { form := "atque/ac", gloss := "and also, and moreover"
  , role := .j, boundness := .free
  , note := "ac before consonants; emphatic variant of et" }

/-- *neque* / *nec* — negative coordination.
    "neque A neque B" = "neither A nor B".
    Morphologically ne + -que (negation + MU enclitic). -/
def neque : CoordEntry :=
  { form := "neque/nec", gloss := "and not, neither...nor"
  , role := .negCoord, boundness := .free
  , correlative := true
  , note := "ne + -que; always correlative for 'neither...nor'" }

/-- *aut* — exclusive/strong disjunction.
    "aut A aut B" = "either A or B (but not both)". -/
def aut : CoordEntry :=
  { form := "aut", gloss := "or (exclusive)"
  , role := .disj, boundness := .free
  , correlative := true }

/-- *vel* — inclusive/weak disjunction.
    "vel A vel B" = "A or B (or both)". -/
def vel : CoordEntry :=
  { form := "vel", gloss := "or (inclusive)"
  , role := .disj, boundness := .free
  , correlative := true }

/-- *sed* — adversative conjunction.
    "non A sed B" = "not A but B". -/
def sed : CoordEntry :=
  { form := "sed", gloss := "but"
  , role := .advers, boundness := .free }

def allEntries : List CoordEntry :=
  [et, que, atque, neque, aut, vel, sed]

-- ============================================================================
-- Verification
-- ============================================================================

/-- Latin has exactly one bound morpheme: -que. -/
theorem one_bound_morpheme :
    (allEntries.filter (·.boundness == .bound)).length = 1 := by
  native_decide

/-- The bound morpheme is the MU particle -que. -/
theorem bound_is_mu :
    (allEntries.filter (·.boundness == .bound)).all (·.role == .mu) = true := by
  native_decide

/-- Latin has correlative uses of J, disjunction, and negative coordination. -/
theorem correlative_entries :
    (allEntries.filter (·.correlative)).length = 4 := by
  native_decide

end Fragments.Latin.Coordination
