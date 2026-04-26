import Linglib.Theories.Syntax.Minimalism.Applicative

/-!
# Small Clause Predication

@cite{dendikken-1995} @cite{baker-1988}

@cite{dendikken-1995}'s central thesis: all subject-predicate relationships
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
  deriving DecidableEq, Repr

/-- Map SC predicate categories to syntactic categories. -/
def SCPredCategory.toCat : SCPredCategory → Cat
  | .P => .P
  | .A => .A
  | .V => .V
  | .N => .N

@[simp] theorem SCPredCategory.toCat_P : SCPredCategory.toCat .P = Cat.P := rfl
@[simp] theorem SCPredCategory.toCat_A : SCPredCategory.toCat .A = Cat.A := rfl
@[simp] theorem SCPredCategory.toCat_V : SCPredCategory.toCat .V = Cat.V := rfl
@[simp] theorem SCPredCategory.toCat_N : SCPredCategory.toCat .N = Cat.N := rfl

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
-- IsSmallClause: companion predicate over `SyntacticObject`
-- ============================================================================

/-! ## Companion predicate

The bundled `structure SmallClause` is the `Submonoid`-style API
object: it carries data + the predicate-category discriminator. The
companion predicate `IsSmallClause : SyntacticObject → Prop` lets us
ask "is this raw SO an SC?" without constructing a `SmallClause`.
Mathlib analogue: `Submonoid` (structure) + `IsSubmonoid` (predicate).

Use this companion to characterize SC encodings written as raw
`merge`-built `SyntacticObject`s (the prevailing style in study files
like `HaddicanEtAl2026`, `Phenomena/ArgumentStructure/Studies/Dendikken1995`)
without forcing them through the `SmallClause` constructor. -/

/-- Head category of a syntactic object: the leftmost terminal's outer
    category. By the Minimalist projection convention used in our
    encodings, the head precedes its complement, so the LEFT child
    of any non-leaf projects. -/
def SyntacticObject.headCat : SyntacticObject → Cat
  | .leaf tok => tok.item.outerCat
  | .node l _ => l.headCat

@[simp] theorem SyntacticObject.headCat_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).headCat = tok.item.outerCat := rfl

@[simp] theorem SyntacticObject.headCat_node (l r : SyntacticObject) :
    (SyntacticObject.node l r).headCat = l.headCat := rfl

/-- A syntactic object qualifies as a small-clause predicate iff its
    head category is one of @cite{dendikken-1995}'s four SC-licensed
    lexical categories (P/A/V/N). -/
def IsSmallClausePredicate (so : SyntacticObject) : Prop :=
  so.headCat = .P ∨ so.headCat = .A ∨ so.headCat = .V ∨ so.headCat = .N

instance : DecidablePred IsSmallClausePredicate :=
  fun so => by unfold IsSmallClausePredicate; exact inferInstance

/-- A syntactic object IS a small clause when it is a binary node
    (subject + predicate) whose right child satisfies
    `IsSmallClausePredicate`. The right child encodes the predicate
    because den Dikken's SC structure has the form `[SC Spec XP]`
    with Spec on the left and the projecting predicate XP on the
    right (book p. 132 ex. 52a).

    Companion to `structure SmallClause`. -/
def IsSmallClause : SyntacticObject → Prop
  | .leaf _ => False
  | .node _ pred => IsSmallClausePredicate pred

instance : DecidablePred IsSmallClause
  | .leaf _ => isFalse id
  | .node _ pred => inferInstanceAs (Decidable (IsSmallClausePredicate pred))

@[simp] theorem isSmallClause_leaf (tok : LIToken) :
    ¬ IsSmallClause (SyntacticObject.leaf tok) := id

@[simp] theorem isSmallClause_node (l r : SyntacticObject) :
    IsSmallClause (SyntacticObject.node l r) ↔ IsSmallClausePredicate r :=
  Iff.rfl

/-- `merge`-form rewrite for `IsSmallClause` — useful since study
    files build SCs with `merge` rather than `.node` patterns. -/
@[simp] theorem isSmallClause_merge (l r : SyntacticObject) :
    IsSmallClause (merge l r) ↔ IsSmallClausePredicate r :=
  Iff.rfl

/-- Round-trip: any `SmallClause` whose stored `predCat` agrees with
    its `predicate`'s actual head category yields a `SyntacticObject`
    satisfying `IsSmallClause`. The hypothesis is the well-formedness
    invariant the free-form `SmallClause` constructor doesn't enforce
    by type — for the standard PVC/Resultative/etc. constructors that
    use `mkLeafPhon` matching `predCat.toCat`, the hypothesis discharges
    by `rfl`. -/
theorem SmallClause.toSO_isSmallClause (sc : SmallClause)
    (h : sc.predicate.headCat = sc.predCat.toCat) :
    IsSmallClause sc.toSO := by
  unfold SmallClause.toSO
  rw [isSmallClause_merge]
  unfold IsSmallClausePredicate
  rw [h]
  cases sc.predCat <;> simp

-- ============================================================================
-- Applicative connection (@cite{dendikken-1995}, Ch. 5)
-- ============================================================================

/-- Whether an applicative head is analyzable as an affixal particle.

    Low applicatives introduce a transfer/possession relation between
    goal and theme — structurally, a P head relating two DPs via SC
    predication. This is the same configuration as particles.

    High applicatives relate the applied argument to the event, not
    to the theme — they are NOT affixal particles. -/
def ApplType.IsAffixalParticle (a : ApplType) : Prop :=
  a = .lowRecipient ∨ a = .lowSource

instance : DecidablePred ApplType.IsAffixalParticle :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Map low applicatives to SC predicate category P.
    Low Appl mediates the same structural relation as a particle:
    `[SC Goal [XP Theme]]` where the applicative head is the P. -/
def ApplType.toSCPredCategory : ApplType → Option SCPredCategory
  | .lowRecipient => some .P
  | .lowSource    => some .P
  | .high         => none

/-- Low recipient applicatives are affixal particles. -/
theorem low_recipient_appl_is_particle : ApplType.IsAffixalParticle .lowRecipient := by decide

/-- Low source applicatives are affixal particles. -/
theorem low_source_appl_is_particle : ApplType.IsAffixalParticle .lowSource := by decide

/-- High applicatives are NOT affixal particles. -/
theorem high_appl_not_particle : ¬ ApplType.IsAffixalParticle .high := by decide

/-- Low recipient applicatives map to SC predicate category P. -/
theorem low_recipient_appl_is_P : ApplType.toSCPredCategory .lowRecipient = some .P := rfl

/-- Low source applicatives map to SC predicate category P. -/
theorem low_source_appl_is_P : ApplType.toSCPredCategory .lowSource = some .P := rfl

/-- High applicatives have no SC predication analog. -/
theorem high_appl_no_SC : ApplType.toSCPredCategory .high = none := rfl

end Minimalism
