/-!
# Dargwa (Tanti) Coordination @cite{sumbatova-2021}

Clause coordination is not typical of Dargwa — subordination via
non-finite verb forms is the primary strategy for combining clauses
(@cite{sumbatova-2021} §4.8.1). When coordination does occur, it uses
the following strategies:

## NP Coordination

- **=ra** (ADD): enclitic additive particle, repeated after each conjunct.
  Also used as a sentence-level additive ('also, too').
  "č'al malla=ra ca qulki=ra" = 'two mullahs and a thief'.

- **ja ... ja** (DISJ ... DISJ): repeated disjunction.
  "ja ... ja" = 'neither ... nor' (with negation).

- **=nu**: contrastive/causal particle.

These patterns connect to the M&S (Mitrovic & Sauerland) typology
formalized in `Phenomena.Coordination.Typology`.

## Connection to Typology

Dargwa's *=ra* is a MU particle (repeated on each conjunct, also
additive), making Dargwa a MU-only conjunction language. The
absence of a J-only strategy (no free "and" between conjuncts)
is predicted by M&S: languages can have MU without J.
-/

namespace Fragments.Dargwa.Coordination

/-- Role of a coordination morpheme in the M&S decomposition. -/
inductive CoordRole where
  | j          -- Set intersection (conjunction)
  | mu         -- Subset/additive
  | disj       -- Disjunction
  | advers     -- Adversative
  deriving DecidableEq, Repr

/-- Morphological boundness. -/
inductive Boundness where
  | free
  | bound   -- clitic or suffix
  deriving DecidableEq, Repr

/-- A Dargwa coordination entry. -/
structure CoordEntry where
  form : String
  gloss : String
  role : CoordRole
  boundness : Boundness
  /-- Does this morpheme also serve as an additive/focus particle? -/
  alsoAdditive : Bool := false
  /-- Notes -/
  note : String := ""
  deriving Repr, BEq

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *=ra* — additive/conjunction particle. Bound enclitic, postpositive.
    Repeated after each conjunct: "A=ra B=ra" = 'A and B'.
    Also sentence-level additive: "nuka=ra" = 'we too'.
    This is a MU particle. -/
def ra : CoordEntry :=
  { form := "=ra", gloss := "and, also, too; ADD"
  , role := .mu, boundness := .bound
  , alsoAdditive := true
  , note := "repeated after each conjunct" }

/-- *ja...ja* — disjunction. Free, repeated before each disjunct.
    "ja A ja B" = 'either A or B'.
    With negation: 'neither A nor B'. -/
def ja : CoordEntry :=
  { form := "ja", gloss := "or; neither...nor (with NEG)"
  , role := .disj, boundness := .free
  , note := "repeated before each disjunct" }

/-- *=nu* — contrastive/causal particle.
    Marks contrast between clauses or causal relation. -/
def nu : CoordEntry :=
  { form := "=nu", gloss := "but; because"
  , role := .advers, boundness := .bound }

def allEntries : List CoordEntry := [ra, ja, nu]

-- ============================================================================
-- Verification
-- ============================================================================

/-- Dargwa has no J-only conjunction particle. Its conjunction
    strategy is MU-only (*=ra* repeated on each conjunct). -/
theorem no_j_particle :
    (allEntries.filter (·.role == .j)).length = 0 := by native_decide

/-- The MU particle *=ra* is also an additive particle,
    as predicted by M&S typology. -/
theorem mu_is_additive :
    (allEntries.filter (·.role == .mu)).all (·.alsoAdditive) = true := by
  native_decide

/-- The MU particle is bound (enclitic). -/
theorem mu_is_bound :
    (allEntries.filter (·.role == .mu)).all (·.boundness == .bound) = true := by
  native_decide

end Fragments.Dargwa.Coordination
