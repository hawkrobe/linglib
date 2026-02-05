/-!
# Georgian Coordination Morphemes

Georgian is one of two languages in our sample (with Hungarian) that attests
all three M&S conjunction strategies: J-only, MU-only, and J-MU.

- *da* — J, free, prepositive: "A da B"
- *-c* — MU, bound clitic, postpositive: "A-c B-c"
- *-c da...-c* — J-MU combined

The MU particle *-c* is also Georgian's additive/focus particle, confirming
the M&S prediction. Crucially, *-c* is a **bound clitic**, unlike Hungarian
*is* (free). Bill et al. (2025) speculate this morphological difference may
explain why Georgian children found MU-involving strategies harder.

Connection to Typology.lean: `Phenomena.Coordination.Typology.georgian`
Connection to BillEtAl2025: Georgian children found J-MU hardest (contrary
to the Transparency Principle prediction).

## References

- Bill et al. (2025). Is DP conjunction always complex? S&P 18(5).
- Mitrović & Sauerland (2016). Two conjunctions are better than one.
  Acta Linguistica Hungarica 63(4), 471-494.
- Haspelmath (2007). Coordination. In Shopen (ed.), Language Typology
  and Syntactic Description. Cambridge University Press.
-/

namespace Fragments.Georgian.Coordination

/-- Role of a coordination morpheme in the M&S decomposition. -/
inductive CoordRole where
  | j          -- Set intersection (conjunction)
  | mu         -- Subset/additive (conjunction)
  | disj       -- Disjunction
  | advers     -- Adversative ("but")
  deriving DecidableEq, BEq, Repr

/-- Morphological boundness. -/
inductive Boundness where
  | free
  | bound   -- clitic or suffix
  deriving DecidableEq, BEq, Repr

/-- A Georgian coordination entry. -/
structure CoordEntry where
  form : String
  gloss : String
  role : CoordRole
  boundness : Boundness
  /-- Does this morpheme also serve as an additive/focus particle? -/
  alsoAdditive : Bool := false
  /-- Notes on usage or distribution -/
  note : String := ""
  deriving Repr, BEq

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *da* — primary conjunction, J particle. Free, prepositive.
    "nino da giorgi" = "Nino and Giorgi". -/
def da : CoordEntry :=
  { form := "da", gloss := "and"
  , role := .j, boundness := .free }

/-- *-c* — MU particle / additive focus particle. Bound clitic, postpositive.
    Conjunction: "nino-c giorgi-c" = "both Nino and Giorgi".
    Additive: "nino-c dzinavs" = "Nino also sleeps".
    The bound status of -c contrasts with Hungarian free "is". -/
def c_ : CoordEntry :=
  { form := "-c", gloss := "also, too; and (MU)"
  , role := .mu, boundness := .bound
  , alsoAdditive := true }

/-- *an* — disjunction. Free, prepositive.
    "nino an giorgi" = "Nino or Giorgi". -/
def an : CoordEntry :=
  { form := "an", gloss := "or"
  , role := .disj, boundness := .free }

/-- *magram* — adversative conjunction.
    "lamazia magram dzviri" = "beautiful but expensive". -/
def magram : CoordEntry :=
  { form := "magram", gloss := "but"
  , role := .advers, boundness := .free }

def allEntries : List CoordEntry :=
  [da, c_, an, magram]

-- ============================================================================
-- Verification
-- ============================================================================

/-- Georgian has exactly one bound morpheme: the MU clitic -c. -/
theorem one_bound :
    (allEntries.filter (·.boundness == .bound)).length = 1 := by
  native_decide

/-- The bound morpheme is the MU particle. -/
theorem bound_is_mu :
    (allEntries.filter (·.boundness == .bound)).all (·.role == .mu) = true := by
  native_decide

/-- The MU particle -c also serves as an additive particle. -/
theorem mu_is_additive :
    (allEntries.filter (·.role == .mu)).all (·.alsoAdditive) = true := by
  native_decide

end Fragments.Georgian.Coordination
