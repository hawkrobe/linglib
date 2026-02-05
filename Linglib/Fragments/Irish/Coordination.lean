/-!
# Irish Coordination Morphemes

Irish coordination morphemes. Irish is a J-only language for conjunction:
"agus" is the sole conjunctive coordinator. There is no MU (additive
particle) strategy for conjunction attested.

Connection to Typology.lean: `Phenomena.Coordination.Typology.irish`
encodes the structural pattern (a_co_b only, J-only strategy).

## References

- Stenson (1981). Studies in Irish Syntax. Tübingen: Narr.
- Mac Congáil (2004). Irish Grammar. Cois Life.
- Haspelmath (2007). Coordination. In Shopen (ed.), Language Typology
  and Syntactic Description. Cambridge University Press.
-/

namespace Fragments.Irish.Coordination

/-- Role of a coordination morpheme. -/
inductive CoordRole where
  | j          -- Conjunction
  | disj       -- Disjunction
  | advers     -- Adversative ("but")
  | negDisj    -- Negative disjunction ("nor")
  deriving DecidableEq, BEq, Repr

/-- Morphological boundness. -/
inductive Boundness where
  | free
  | bound
  deriving DecidableEq, BEq, Repr

/-- An Irish coordination entry. -/
structure CoordEntry where
  form : String
  gloss : String
  role : CoordRole
  boundness : Boundness
  /-- Additional functions beyond coordination -/
  note : String := ""
  deriving Repr, BEq

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *agus* — conjunction, J particle. Free, prepositive.
    "Seán agus Máire" = "Seán and Máire". -/
def agus : CoordEntry :=
  { form := "agus", gloss := "and"
  , role := .j, boundness := .free }

/-- *nó* — disjunction. Free, prepositive.
    "Seán nó Máire" = "Seán or Máire". -/
def no_ : CoordEntry :=
  { form := "nó", gloss := "or"
  , role := .disj, boundness := .free }

/-- *ná* — negative disjunction / comparative particle.
    "ní Seán ná Máire" = "neither Seán nor Máire".
    Also used in comparatives: "níos mó ná" = "bigger than". -/
def na_ : CoordEntry :=
  { form := "ná", gloss := "nor, than"
  , role := .negDisj, boundness := .free
  , note := "also comparative particle" }

/-- *ach* — adversative conjunction.
    "Tá sé fuar ach tirim" = "It is cold but dry". -/
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
