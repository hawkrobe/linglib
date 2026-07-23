import Linglib.Syntax.Category.Coordinator

/-!
# Hungarian Coordination Morphemes
[szabolcsi-2015] [bill-etal-2025]

Hungarian is one of two languages in our sample (with Georgian) that attests
all three M&S conjunction strategies: J-only, MU-only, and J-MU.

- *es* — J, free, prepositive: "A es B"
- *is* — MU, free, postpositive: "A is B is"
- *es...is* — J-MU combined: "A is es B is"

The MU particle *is* is also Hungarian's additive/focus particle ("also/too"),
confirming Mitrovic & Sauerland's prediction that MU = additive particle.

[bill-etal-2025] found no significant sentence-type effect on comprehension
in Hungarian children (possibly ceiling effects).

Connection to Typology.lean: `Haspelmath2007.hungarian`
Connection to BillEtAl2025: Hungarian is one of two test languages.

-/

namespace Hungarian.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *es* — primary conjunction, J particle. Free, prepositive.
    "Peter es Mari" = "Peter and Mari". -/
def es : Coordinator :=
  { form := "és", gloss := "and"
  , role := .j, kind := .free }

/-- *is* — MU particle / additive focus particle. Free, postpositive.
    Conjunction: "Peter is Mari is" = "both Peter and Mari".
    Additive: "Peter is alszik" = "Peter also sleeps".
    One of the key pieces of evidence for M&S's MU = additive particle claim. -/
def is_ : Coordinator :=
  { form := "is", gloss := "also, too; and (MU)"
  , role := .mu, kind := .free
  , alsoAdditive := true }

/-- *vagy* — disjunction. Free, prepositive.
    "Peter vagy Mari" = "Peter or Mari". -/
def vagy : Coordinator :=
  { form := "vagy", gloss := "or"
  , role := .disj, kind := .free }

/-- *de* — adversative conjunction.
    "szep de draga" = "beautiful but expensive". -/
def de : Coordinator :=
  { form := "de", gloss := "but"
  , role := .advers, kind := .free }

def allEntries : List Coordinator :=
  [es, is_, vagy, de]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Hungarian coordination morphemes are free (no bound clitics).
    This contrasts with Georgian, where MU (-c) is bound.
    [bill-etal-2025] speculate this difference may explain why
    Georgian children found MU harder than Hungarian children did. -/
theorem all_free :
    allEntries.all (fun e => decide (e.kind = .free)) = true := by
  decide

/-- The MU particle *is* also serves as an additive particle. -/
theorem mu_is_additive :
    (allEntries.filter (·.role == .mu)).all (·.alsoAdditive) = true := by
  decide

end Hungarian.Coordination
