/-!
# Hungarian Coordination Morphemes

Hungarian is one of two languages in our sample (with Georgian) that attests
all three M&S conjunction strategies: J-only, MU-only, and J-MU.

- *és* — J, free, prepositive: "A és B"
- *is* — MU, free, postpositive: "A is B is"
- *és...is* — J-MU combined: "A is és B is"

The MU particle *is* is also Hungarian's additive/focus particle ("also/too"),
confirming Mitrović & Sauerland's prediction that MU = additive particle.

Bill et al. (2025) found no significant sentence-type effect on comprehension
in Hungarian children (possibly ceiling effects).

Connection to Typology.lean: `Phenomena.Coordination.Typology.hungarian`
Connection to BillEtAl2025: Hungarian is one of two test languages.

## References

- Bill et al. (2025). Is DP conjunction always complex? S&P 18(5).
- Mitrović & Sauerland (2016). Two conjunctions are better than one.
  Acta Linguistica Hungarica 63(4), 471-494.
- Szabolcsi (2015). What do quantifier particles do? L&P 38(2).
-/

namespace Fragments.Hungarian.Coordination

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
  | bound
  deriving DecidableEq, BEq, Repr

/-- A Hungarian coordination entry. -/
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

/-- *és* — primary conjunction, J particle. Free, prepositive.
    "Péter és Mari" = "Péter and Mari". -/
def es : CoordEntry :=
  { form := "és", gloss := "and"
  , role := .j, boundness := .free }

/-- *is* — MU particle / additive focus particle. Free, postpositive.
    Conjunction: "Péter is Mari is" = "both Péter and Mari".
    Additive: "Péter is alszik" = "Péter also sleeps".
    One of the key pieces of evidence for M&S's MU = additive particle claim. -/
def is_ : CoordEntry :=
  { form := "is", gloss := "also, too; and (MU)"
  , role := .mu, boundness := .free
  , alsoAdditive := true }

/-- *vagy* — disjunction. Free, prepositive.
    "Péter vagy Mari" = "Péter or Mari". -/
def vagy : CoordEntry :=
  { form := "vagy", gloss := "or"
  , role := .disj, boundness := .free }

/-- *de* — adversative conjunction.
    "szép de drága" = "beautiful but expensive". -/
def de : CoordEntry :=
  { form := "de", gloss := "but"
  , role := .advers, boundness := .free }

def allEntries : List CoordEntry :=
  [es, is_, vagy, de]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Hungarian coordination morphemes are free (no bound clitics).
    This contrasts with Georgian, where MU (-c) is bound.
    Bill et al. (2025) speculate this difference may explain why
    Georgian children found MU harder than Hungarian children did. -/
theorem all_free :
    allEntries.all (·.boundness == .free) = true := by
  native_decide

/-- The MU particle *is* also serves as an additive particle. -/
theorem mu_is_additive :
    (allEntries.filter (·.role == .mu)).all (·.alsoAdditive) = true := by
  native_decide

end Fragments.Hungarian.Coordination
