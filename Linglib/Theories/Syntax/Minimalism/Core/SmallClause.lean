import Linglib.Theories.Syntax.Minimalism.Core.Applicative

/-!
# Small Clause Predication

@cite{dendikken-1995} @cite{baker-1988}@cite{dendikken-1995}'s central thesis: all subject-predicate relationships
are incarnated as small clauses `[SC Subject Predicate]`. The predicate
head's category determines the construction type:

| Pred category | Construction | Example |
|---|---|---|
| P | Verb-particle / dative | "lift Hsu up", "give the books to Mary" |
| A | Resultative | "hammer the metal flat" |
| V | Causative | "make the child laugh" |
| N | Copular / ECM | "consider John a fool" |

The SC analysis unifies these constructions structurally: they share
the tree shape `V [SC Subj Pred]` = `node(leaf, node(leaf, leaf))`,
with differences reduced to the category of the predicate head.

## Cross-linguistic extension

Bantu applicative morphemes (*-il-, -el-*) and Japanese causative *-(s)ase*
are analyzed as affixal particles: grammaticalized instances of P-to-V
incorporation. Low applicatives introduce the
same structural configuration as particles — SC predication between
a goal and a theme, mediated by a P head.

-/

namespace Minimalism

/-- Category of the predicate head in a small clause.

    @cite{dendikken-1995}: X ∈ {A, N, P, V} — the four
    LEXICAL categories. The SC family is parameterized by which
    lexical category serves as the predicate head. -/
inductive SCPredCategory where
  | P   -- Preposition/particle (PVC: "lift Hsu up"; dative: "give books to Mary")
  | A   -- Adjective (resultative: "hammer the metal flat")
  | V   -- Verb (causative: "make the child laugh")
  | N   -- Noun (copular/ECM: "consider John a fool")
  deriving DecidableEq, BEq, Repr

/-- Map SC predicate categories to syntactic categories. -/
def SCPredCategory.toCat : SCPredCategory → Cat
  | .P => .P
  | .A => .A
  | .V => .V
  | .N => .N

/-- A small clause: subject-predicate pair where the predicate
    is categorially typed (@cite{dendikken-1995}:27, ex. 44).

    `[SC subject predicate]`

    The `predCat` field determines which member of the SC family
    this instance belongs to. -/
structure SmallClause where
  /-- The subject of predication (typically a DP) -/
  subject : SyntacticObject
  /-- The predicate head -/
  predicate : SyntacticObject
  /-- Category of the predicate (determines construction type) -/
  predCat : SCPredCategory
  deriving Repr

/-- Build the syntactic object for a small clause: `[SC Subj Pred]`. -/
def SmallClause.toSO (sc : SmallClause) : SyntacticObject :=
  merge sc.subject sc.predicate

/-- Embed a small clause under a verb: `V [SC Subj Pred]`. -/
def SmallClause.embedUnderV (v : SyntacticObject) (sc : SmallClause) :
    SyntacticObject :=
  merge v sc.toSO

/-- The construction type name for each SC predicate category. -/
def SCPredCategory.constructionName : SCPredCategory → String
  | .P => "verb-particle / dative"
  | .A => "resultative"
  | .V => "causative"
  | .N => "copular/ECM"

-- ============================================================================
-- Applicative connection (@cite{dendikken-1995}, Ch. 5)
-- ============================================================================

/-- Whether an applicative head is analyzable as an affixal particle.

    Low applicatives introduce a transfer/possession relation between
    goal and theme — structurally, a P head relating two DPs via SC
    predication. This is the same configuration as particles.

    High applicatives relate the applied argument to the event, not
    to the theme — they are NOT affixal particles. -/
def ApplType.isAffixalParticle : ApplType → Bool
  | .lowRecipient => true   -- Low Appl = P head (transfer/possession SC)
  | .lowSource    => true   -- Low Appl = P head (source/possession SC)
  | .high         => false  -- High Appl = event-level, not SC predication

/-- Map low applicatives to SC predicate category P.
    Low Appl mediates the same structural relation as a particle:
    `[SC Goal [XP Theme]]` where the applicative head is the P. -/
def ApplType.toSCPredCategory : ApplType → Option SCPredCategory
  | .lowRecipient => some .P
  | .lowSource    => some .P
  | .high         => none

/-- Low recipient applicatives are affixal particles. -/
theorem low_recipient_appl_is_particle : ApplType.isAffixalParticle .lowRecipient = true := rfl

/-- Low source applicatives are affixal particles. -/
theorem low_source_appl_is_particle : ApplType.isAffixalParticle .lowSource = true := rfl

/-- High applicatives are NOT affixal particles. -/
theorem high_appl_not_particle : ApplType.isAffixalParticle .high = false := rfl

/-- Low recipient applicatives map to SC predicate category P. -/
theorem low_recipient_appl_is_P : ApplType.toSCPredCategory .lowRecipient = some .P := rfl

/-- Low source applicatives map to SC predicate category P. -/
theorem low_source_appl_is_P : ApplType.toSCPredCategory .lowSource = some .P := rfl

/-- High applicatives have no SC predication analog. -/
theorem high_appl_no_SC : ApplType.toSCPredCategory .high = none := rfl

end Minimalism
