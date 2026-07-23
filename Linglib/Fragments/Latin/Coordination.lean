import Linglib.Syntax.Category.Coordinator

/-!
# Latin Coordination Morphemes
[haspelmath-2007]

Latin has a rich coordination system with both free and bound forms.
The J/MU decomposition ([mitrovic-sauerland-2014], [mitrovic-sauerland-2016]) maps cleanly:

- *et* — J, free, prepositive: "A et B"
- *-que* — MU, bound enclitic, postpositive: "A B-que" (= "A and B")
- *atque*/*ac* — emphatic J variant (before consonants: *ac*)
- *neque*/*nec* — negative coordination ("neither...nor")

The *et...et* pattern ("both...and") and *neque...neque* pattern are
bisyndetic uses of J particles.

Connection to Typology.lean: `Haspelmath2007.latin`
encodes the structural patterns (a_co_b, a_b'co, co'a_b'co).

-/

namespace Latin.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *et* — primary conjunction, J particle. Free, prepositive.
    "Caesar et Brutus" = "Caesar and Brutus".
    Also used correlatively: "et A et B" = "both A and B". -/
def et : Coordinator :=
  { form := "et", gloss := "and"
  , role := .j, kind := .free
  , correlative := true }

/-- *-que* — enclitic conjunction, MU particle. Bound, postpositive.
    "senatus populusque" = "senate and people".
    Historically connected to the additive/inclusive particle. -/
def que : Coordinator :=
  { form := "-que", gloss := "and (enclitic)"
  , role := .mu, kind := .bound .after .clitic
  , alsoAdditive := true
  , note := "postpositive enclitic; archaic/formal register" }

/-- *atque* / *ac* — emphatic conjunction, J variant.
    *ac* before consonants, *atque* before vowels.
    "atque" < *ad-que (lit. "and to that"). -/
def atque : Coordinator :=
  { form := "atque/ac", gloss := "and also, and moreover"
  , role := .j, kind := .free
  , note := "ac before consonants; emphatic variant of et" }

/-- *neque* / *nec* — negative coordination.
    "neque A neque B" = "neither A nor B".
    Morphologically ne + -que (negation + MU enclitic). -/
def neque : Coordinator :=
  { form := "neque/nec", gloss := "and not, neither...nor"
  , role := .negCoord, kind := .free
  , correlative := true
  , note := "ne + -que; always correlative for 'neither...nor'" }

/-- *aut* — exclusive/strong disjunction.
    "aut A aut B" = "either A or B (but not both)". -/
def aut : Coordinator :=
  { form := "aut", gloss := "or (exclusive)"
  , role := .disj, kind := .free
  , correlative := true }

/-- *vel* — inclusive/weak disjunction.
    "vel A vel B" = "A or B (or both)". -/
def vel : Coordinator :=
  { form := "vel", gloss := "or (inclusive)"
  , role := .disj, kind := .free
  , correlative := true }

/-- *sed* — adversative conjunction.
    "non A sed B" = "not A but B". -/
def sed : Coordinator :=
  { form := "sed", gloss := "but"
  , role := .advers, kind := .free }

def allEntries : List Coordinator :=
  [et, que, atque, neque, aut, vel, sed]

-- ============================================================================
-- Verification
-- ============================================================================

/-- Latin has exactly one bound morpheme: -que. -/
theorem one_bound_morpheme :
    (allEntries.filter (fun e => e.kind matches .bound ..)).length = 1 := by
  decide

/-- The bound morpheme is the MU particle -que. -/
theorem bound_is_mu :
    (allEntries.filter (fun e => e.kind matches .bound ..)).all (·.role == .mu) = true := by
  decide

/-- Latin has correlative uses of J, disjunction, and negative coordination. -/
theorem correlative_entries :
    (allEntries.filter (·.correlative)).length = 4 := by
  decide

end Latin.Coordination
