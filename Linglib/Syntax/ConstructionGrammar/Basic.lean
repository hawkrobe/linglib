import Linglib.Data.UD.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic

/-!
# Construction Grammar: Core Types
[goldberg-1995] [goldberg-2003] [goldberg-2006] [kay-fillmore-1999] [dunn-2025]

Constructions — learned pairings of form and function — are the basic
units of grammatical knowledge in CxG. The form side is typed: a
`TypedForm` is a sequence of `Slot`s, each fixing a lexeme, opening a
category, or admitting any phrase ([dunn-2025]'s LEX/SYN/SEM+
representation levels, plus [kay-fillmore-1999]'s grammatical functions,
coreference indices, and slot constraints). Abstraction measures and
`Specificity` are *derived* from the slot structure
(`Construction.specificity`), not stipulated.

A slot also records the bar level of its position; a `phrasal` filler in
a `zero`-level position (`Slot.IsPhraseInWordSlot`) is the
phrase-in-word-slot configuration of phrasal compounds and the PAL
construction.

## Main declarations

- `SlotFiller`, `Slot`, `TypedForm`: the typed form side
- `abstractionLevel`, `derivedSpecificity`: abstraction measures on forms
- `Construction`, `Construction.specificity`: form–function pairings
- `InheritanceLink`, `Constructicon`: the network
-/

namespace ConstructionGrammar

/-- How specified a construction's form side is ([goldberg-2003]:220, Table 8).

| Specificity | Example |
|---|---|
| lexicallySpecified | "veggie-wrap", "must-read" |
| partiallyOpen | "N-wrap", "a simple ⟨PAL⟩" |
| fullyAbstract | [N⁰ N⁰ N⁰], [N′ PAL⁰ N] |
-/
inductive Specificity where
  | lexicallySpecified
  | partiallyOpen
  | fullyAbstract
  deriving Repr, DecidableEq

/-- Mode of information transfer in an inheritance link
([goldberg-1995] §3.3.1, p. 73–74).

[goldberg-1995] distinguishes two modes, orthogonal to link type:
- **Normal**: child inherits defaults from parent but may override them.
  Allows subregularities and exceptions. The only mode used in
  [goldberg-1995]'s system.
- **Complete**: all information from dominating nodes is inherited strictly;
  no conflicts allowed. The mode "normally assumed in unification-based
  grammars" (p. 74, citing Kay 1984 and Fillmore & Kay 1993); the
  normal/complete distinction follows Flickinger, Pollard & Wasow (1985).
  Not exploited in [goldberg-1995]'s constructional analysis.

Computational semantics for both modes: `ConstructionGrammar.Inheritance`. -/
inductive InheritanceMode where
  | normal     -- child inherits defaults, may override
  | complete   -- all properties inherited strictly (not used in Goldberg 1995)
  deriving Repr, DecidableEq

/-- Type of semantic relation in an inheritance link
([goldberg-1995] §3.3.2, p. 75).

[goldberg-1995] distinguishes four major link types:
- **I_P (Polysemy)**: relates the central sense of a construction to its
  extensions. Each extension inherits syntax but differs in meaning
  (e.g., the six senses of the ditransitive, pp. 75–77).
- **I_M (Metaphorical extension)**: source and target related by systematic
  metaphor (e.g., caused-motion → resultative via the motion→change
  metaphor, p. 81).
- **I_S (Subpart)**: one construction is a proper subpart of another
  (e.g., intransitive motion is a subpart of caused-motion, p. 78).
- **I_I (Instance)**: one construction is a more fully specified version
  of another (e.g., *drive*-crazy is an instance of the resultative, p. 79). -/
inductive LinkType where
  | polysemy       -- I_P: central sense → extension
  | metaphorical   -- I_M: source → target via metaphor
  | subpart        -- I_S: child is proper subpart of parent
  | instance       -- I_I: child is special case of parent
  deriving Repr, DecidableEq

/-- X-bar level of a syntactic position or constructional output. -/
inductive BarLevel where
  | zero    -- X⁰
  | bar     -- X′
  | phrase  -- XP
  deriving DecidableEq, Repr

/-! ### Typed slots

[dunn-2025] distinguishes three representation levels for slot content —
LEX (a fixed lexeme), SYN (any word of a category), SEM+ (any expression
meeting a semantic constraint) — and [kay-fillmore-1999] add headed
phrases, grammatical functions, coreference indices, and syntactic
constraints. The `phrasal` filler (any phrase, no fixed head) is the
filler type of phrasal compounds and PAL constructions. -/

/-- A slot's filler: the representation level of slot content.

Parameterized over `Lex` (the lexeme type) so the same representation
works for strings, morphemes, or phonological forms. -/
inductive SlotFiller (Lex : Type*) where
  /-- A specific word form (LEX level): `fixed "must"` -/
  | fixed : Lex → SlotFiller Lex
  /-- Any word of a given POS category (SYN level): `open_ .VERB` -/
  | open_ : UD.UPOS → SlotFiller Lex
  /-- A phrase headed by a specific lexeme ([kay-fillmore-1999]):
      `headed "doing" .VERB` is a VP headed by *doing*. LEX-level —
      the head lexeme is fixed even though the phrase is open. -/
  | headed : Lex → UD.UPOS → SlotFiller Lex
  /-- A semantically constrained slot ([dunn-2025], SEM+ level):
      `semantic "animate"` is any expression denoting an animate. -/
  | semantic : String → SlotFiller Lex
  /-- Any phrase, with no fixed head and no category restriction on its
      internal structure — the filler of a phrasal-compound or PAL slot
      (the ⟨phrase⟩ node of [goldberg-shirtz-2025]'s Figure 5). -/
  | phrasal : SlotFiller Lex
  deriving DecidableEq, Repr

/-- Is this slot open (not lexically anchored)?

`open_` (SYN), `semantic` (SEM+), and `phrasal` slots count as open for
abstraction-level computation. `headed` slots do not: they fix the head
lexeme even though the phrase is open. -/
def SlotFiller.isOpen {Lex : Type*} : SlotFiller Lex → Bool
  | .fixed _ => false
  | .open_ _ => true
  | .headed _ _ => false
  | .semantic _ => true
  | .phrasal => true

/-- Grammatical function of a valence member ([kay-fillmore-1999], Figure 12).
    Distinct from semantic role: a subject (gf) can be an agent, theme,
    or experiencer (role). -/
inductive GramFunction where
  | subj   -- subject
  | comp   -- complement (clausal/verbal)
  | obj    -- direct object
  | pred   -- predicative complement / secondary predicate
  deriving DecidableEq, Repr

/-- Referential index for cross-slot coreference constraints. Slots
    sharing a `RefIndex` have unified semantic values
    ([kay-fillmore-1999]'s #1, #2). -/
abbrev RefIndex := Nat

/-- Syntactic constraint on a slot ([kay-fillmore-1999], Figure 12). -/
inductive SlotConstraint where
  | locMinus   -- [loc -]: must occur left-isolated, not VP-internal
  | negMinus   -- [neg -]: cannot be negated
  | refEmpty   -- [ref ∅]: nonreferential (no variable-binding function)
  deriving DecidableEq, Repr

/-- A slot in a construction's form: filler content, semantic role,
headedness, and the bar level of the position itself. Fixed slots (like
"let" in *let alone*) have `role := none` since they carry no independent
semantic role. `level := none` leaves the position's bar level
unspecified. -/
structure Slot (Lex : Type*) where
  /-- What fills this slot -/
  filler : SlotFiller Lex
  /-- Semantic role label (agent, theme, etc.), if any -/
  role : Option String := none
  /-- Whether this slot is the head of the construction -/
  isHead : Bool := false
  /-- Bar level of the position (`some .zero` = a word-level slot) -/
  level : Option BarLevel := none
  /-- Grammatical function (subj, comp, obj, pred) — [kay-fillmore-1999] -/
  gf : Option GramFunction := none
  /-- Coreference index: slots sharing an index have unified semantics -/
  refIdx : Option RefIndex := none
  /-- Syntactic constraints on this slot ([loc -], [neg -], [ref ∅]) -/
  constraints : List SlotConstraint := []
  deriving DecidableEq, Repr

/-- A typed form: the form side of a construction as a sequence of slots. -/
abbrev TypedForm (Lex : Type*) := List (Slot Lex)

/-- A phrase in a word-level slot: phrasal filler, zero-level position.
The defining configuration of phrasal compounds and the PAL construction
([goldberg-shirtz-2025]) — and the cell lexical-integrity hypotheses rule
out. -/
def Slot.IsPhraseInWordSlot {Lex : Type*} (s : Slot Lex) : Prop :=
  s.filler = .phrasal ∧ s.level = some .zero

instance {Lex : Type*} [DecidableEq Lex] (s : Slot Lex) :
    Decidable s.IsPhraseInWordSlot :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Abstraction level and derived specificity -/

section AbstractionLevel
variable {Lex : Type*}

/-- Proportion of open slots: a continuous [0,1] measure of abstraction.

[dunn-2025] defines four discrete abstraction *orders* based on which
representation levels appear; this computes the continuous proportion
underlying those orders, and `derivedSpecificity` maps to the three-way
`Specificity` enum. -/
def abstractionLevel (form : TypedForm Lex) : ℚ :=
  if form.isEmpty then 0
  else
    let openCount := (form.filter (·.filler.isOpen)).length
    (openCount : ℚ) / (form.length : ℚ)

/-- Derive `Specificity` from the slot structure.

| Condition | Result |
|-----------|--------|
| All slots open | `.fullyAbstract` |
| No slots open | `.lexicallySpecified` |
| Mix of fixed and open | `.partiallyOpen` |

Changing a slot from open to fixed automatically changes the
specificity. -/
def derivedSpecificity (form : TypedForm Lex) : Specificity :=
  let openCount := (form.filter (·.filler.isOpen)).length
  if openCount = form.length then .fullyAbstract
  else if openCount = 0 then .lexicallySpecified
  else .partiallyOpen

/-- Does any slot in the form bear a given constraint? -/
def hasConstraint (form : TypedForm Lex) (c : SlotConstraint) : Bool :=
  form.any (·.constraints.any (· == c))

/-- Count of distinct coreference groups in a form. -/
def refGroupCount (form : TypedForm Lex) : Nat :=
  (form.filterMap (·.refIdx)).dedup.length

/-! ### Characterization lemmas -/

@[simp]
theorem abstractionLevel_nil : abstractionLevel ([] : TypedForm Lex) = 0 := rfl

theorem abstractionLevel_nonneg (form : TypedForm Lex) :
    0 ≤ abstractionLevel form := by
  simp only [abstractionLevel]
  split
  · exact le_refl 0
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem abstractionLevel_le_one (form : TypedForm Lex) :
    abstractionLevel form ≤ 1 := by
  simp only [abstractionLevel]
  split
  · exact zero_le_one
  · exact div_le_one_of_le₀ (by exact_mod_cast List.length_filter_le _ _)
      (Nat.cast_nonneg _)

/-- A form is fully abstract exactly when every slot is open (vacuously so
for the empty form). -/
theorem derivedSpecificity_eq_fullyAbstract_iff (form : TypedForm Lex) :
    derivedSpecificity form = .fullyAbstract ↔
      ∀ s ∈ form, s.filler.isOpen = true := by
  refine Iff.trans ?_
    (List.length_filter_eq_length_iff (p := fun s : Slot Lex => s.filler.isOpen)
      (l := form))
  simp only [derivedSpecificity]
  split_ifs with h1 h2 <;> simp [h1]

/-- A form is lexically specified exactly when it is nonempty and no slot
is open. -/
theorem derivedSpecificity_eq_lexicallySpecified_iff (form : TypedForm Lex) :
    derivedSpecificity form = .lexicallySpecified ↔
      form ≠ [] ∧ ∀ s ∈ form, s.filler.isOpen = false := by
  have hzero : (form.filter (·.filler.isOpen)) = [] ↔
      ∀ s ∈ form, s.filler.isOpen = false := by
    rw [List.filter_eq_nil_iff]; simp
  simp only [derivedSpecificity]
  split_ifs with h1 h2
  · constructor
    · intro h; cases h
    · rintro ⟨hnil, hall⟩
      rcases List.exists_mem_of_ne_nil form hnil with ⟨s, hs⟩
      have hopen := List.length_filter_eq_length_iff.mp h1 s hs
      have := hall s hs
      simp_all
  · constructor
    · intro _
      constructor
      · rintro rfl; exact h1 (by simp)
      · rw [List.length_eq_zero_iff] at h2
        exact hzero.mp h2
    · intro _; rfl
  · constructor
    · intro h; cases h
    · rintro ⟨hnil, hall⟩
      exact absurd (by rw [List.length_eq_zero_iff]; exact hzero.mpr hall) h2

end AbstractionLevel

/-! ### Constructions and the network -/

/-- A construction: a learned pairing of form and function. The form is a
`TypedForm`; `name` is a display label; specificity is derived from the
form (`Construction.specificity`), not stipulated. -/
structure Construction where
  name : String
  form : TypedForm String
  meaning : String           -- semantic/pragmatic function description
  pragmaticFunction : Option String := none  -- e.g. "presupposes familiarity"
  deriving DecidableEq, Repr

/-- A construction's specificity, derived from its slot structure. -/
def Construction.specificity (c : Construction) : Specificity :=
  derivedSpecificity c.form

/-- An inheritance link between two constructions in the network.

Each link specifies both how information flows (`mode`, §3.3.1) and
what semantic relation holds (`linkType`, §3.3.2). Links without a
specific semantic relation (e.g., general taxonomic inheritance of
shared morphophonological properties) use `linkType := none`. -/
structure InheritanceLink where
  parent : String
  child : String
  mode : InheritanceMode
  linkType : Option LinkType := none
  sharedProperties : List String
  overriddenProperties : List String := []
  deriving Repr, DecidableEq

/-- A constructicon: a network of constructions connected by inheritance links. -/
structure Constructicon where
  constructions : List Construction
  links : List InheritanceLink
  deriving Repr

end ConstructionGrammar
