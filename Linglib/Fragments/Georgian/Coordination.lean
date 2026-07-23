import Linglib.Syntax.Category.Coordinator

/-!
# Georgian Coordination Morphemes
[haspelmath-2007] [bill-etal-2025]

Georgian is one of two languages in our sample (with Hungarian) that attests
all three M&S conjunction strategies: J-only, MU-only, and J-MU.

- *da* — J, free, prepositive: "A da B"
- *-c* — MU, bound clitic, postpositive: "A-c B-c"
- *-c da...-c* — J-MU combined

The MU particle *-c* is also Georgian's additive/focus particle, confirming
the M&S prediction. Crucially, *-c* is a **bound clitic**, unlike Hungarian
*is* (free). [bill-etal-2025] speculate this morphological difference may
explain why Georgian children found MU-involving strategies harder.

Connection to Typology.lean: `Haspelmath2007.georgian`
Connection to BillEtAl2025: Georgian children found J-MU hardest (contrary
to the Transparency Principle prediction).

-/

namespace Georgian.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *da* — primary conjunction, J particle. Free, prepositive.
    "nino da giorgi" = "Nino and Giorgi". -/
def da : Coordinator :=
  { form := "da", gloss := "and"
  , role := .j, kind := .free }

/-- *-c* — MU particle / additive focus particle. Bound clitic, postpositive.
    Conjunction: "nino-c giorgi-c" = "both Nino and Giorgi".
    Additive: "nino-c dzinavs" = "Nino also sleeps".
    The bound status of -c contrasts with Hungarian free "is". -/
def c_ : Coordinator :=
  { form := "-c", gloss := "also, too; and (MU)"
  , role := .mu, kind := .bound .after .clitic
  , alsoAdditive := true }

/-- *an* — disjunction. Free, prepositive.
    "nino an giorgi" = "Nino or Giorgi". -/
def an : Coordinator :=
  { form := "an", gloss := "or"
  , role := .disj, kind := .free }

/-- *magram* — adversative conjunction.
    "lamazia magram dzviri" = "beautiful but expensive". -/
def magram : Coordinator :=
  { form := "magram", gloss := "but"
  , role := .advers, kind := .free }

def allEntries : List Coordinator :=
  [da, c_, an, magram]

-- ============================================================================
-- Verification
-- ============================================================================

/-- Georgian has exactly one bound morpheme: the MU clitic -c. -/
theorem one_bound :
    (allEntries.filter (fun e => e.kind matches .bound ..)).length = 1 := by
  decide

/-- The bound morpheme is the MU particle. -/
theorem bound_is_mu :
    (allEntries.filter (fun e => e.kind matches .bound ..)).all (·.role == .mu) = true := by
  decide

/-- The MU particle -c also serves as an additive particle. -/
theorem mu_is_additive :
    (allEntries.filter (·.role == .mu)).all (·.alsoAdditive) = true := by
  decide

end Georgian.Coordination
