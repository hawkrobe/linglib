/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Mathlib.Data.List.Dedup

/-!
# Construction Grammar: Core Types

A construction is a learned pairing of a form and a meaning
([goldberg-2006]), the basic unit of grammatical knowledge in CxG. The
form side is a `TypedForm`: a sequence of `Slot`s, each fixing a lexeme,
opening a category, or admitting any phrase, with a construction's
`Specificity` derived from its slot structure rather than stipulated.

## Main definitions

* `SlotFiller`, `Slot`, `TypedForm`: the typed form side
* `derivedSpecificity`, `HasConstraint`, `refGroupCount`: measures derived
  from forms
* `Construction`, `Construction.specificity`, `Construction.map`: typed
  form–meaning pairings
* `InheritanceLink`, `Constructicon`: the network
-/

namespace ConstructionGrammar

/-- How specified a construction's form side is: [goldberg-2003]'s
degree-of-abstraction continuum, discretized as in
[goldberg-shirtz-2025]'s Table 8. -/
inductive Specificity where
  /-- Every slot lexically filled: *veggie-wrap*, *must-read*. -/
  | lexicallySpecified
  /-- Fixed and open slots mixed: *N-wrap*, *a simple ⟨PAL⟩*. -/
  | partiallyOpen
  /-- Every slot open: [N⁰ N⁰ N⁰], [N′ PAL⁰ N]. -/
  | fullyAbstract
  deriving Repr, DecidableEq

/-- Mode of information transfer in an inheritance link, orthogonal to
the link's semantic relation ([goldberg-1995] §3.3.1, p. 73–74). -/
inductive InheritanceMode where
  /-- The child inherits defaults from its parents but may override
  them — the only mode [goldberg-1995] uses. -/
  | normal
  /-- All information is inherited strictly, with no conflicts allowed —
  the mode "normally assumed in unification-based grammars" (p. 74). -/
  | complete
  deriving Repr, DecidableEq

/-- The semantic relation an inheritance link records: [goldberg-1995]'s
four major link types (§3.3.2, p. 75). -/
inductive LinkType where
  /-- I_P: relates a construction's central sense to an extension, which
  inherits the syntax but differs in meaning (the six senses of the
  ditransitive, pp. 75–77). -/
  | polysemy
  /-- I_M: source and target related by a systematic metaphor
  (caused-motion → resultative via motion→change, p. 81). -/
  | metaphorical
  /-- I_S: the child is a proper subpart of the parent (intransitive
  motion inside caused-motion, p. 78). -/
  | subpart
  /-- I_I: the child is a more fully specified version of the parent
  (*drive*-crazy as an instance of the resultative, p. 79). -/
  | instance
  deriving Repr, DecidableEq

/-- X-bar level of a syntactic position or constructional output. -/
inductive BarLevel where
  /-- X⁰, a word-level position. -/
  | zero
  /-- X′, an intermediate projection. -/
  | bar
  /-- XP, a full phrase. -/
  | phrase
  deriving DecidableEq, Repr

/-! ### Typed slots

Slot content comes at [dunn-2025]'s three representation levels — LEX (a
fixed lexeme), SYN (any word of a category), SEM (a semantic constraint) —
plus [kay-fillmore-1999]'s headed phrases, grammatical functions,
coreference indices, and slot constraints. -/

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
  /-- A semantically constrained slot ([dunn-2025], SEM level):
      `semantic "animate"` is any expression denoting an animate. -/
  | semantic : String → SlotFiller Lex
  /-- Any phrase, with no fixed head and no category restriction on its
      internal structure — the filler of a phrasal-compound or PAL slot
      (the ⟨phrase⟩ node of [goldberg-shirtz-2025]'s Figure 5). -/
  | phrasal : SlotFiller Lex
  deriving DecidableEq, Repr

/-- Whether a slot is open — not lexically anchored: `open_`, `semantic`,
and `phrasal` fillers count as open; `fixed` and `headed` do not, the
latter fixing its head lexeme even though the phrase is open. -/
def SlotFiller.isOpen {Lex : Type*} : SlotFiller Lex → Bool
  | .fixed _ => false
  | .open_ _ => true
  | .headed _ _ => false
  | .semantic _ => true
  | .phrasal => true

/-- Grammatical function of a valence member ([kay-fillmore-1999],
Figure 12), distinct from semantic role: a subject can be an agent, a
theme, or an experiencer. -/
inductive GramFunction where
  /-- Subject. -/
  | subj
  /-- Clausal or verbal complement. -/
  | comp
  /-- Direct object. -/
  | obj
  /-- Predicative complement or secondary predicate. -/
  | pred
  deriving DecidableEq, Repr

/-- Referential index for cross-slot coreference constraints. Slots
    sharing a `RefIndex` have unified semantic values
    ([kay-fillmore-1999]'s #1, #2). -/
abbrev RefIndex := Nat

/-- Syntactic constraint on a slot ([kay-fillmore-1999], Figure 12). -/
inductive SlotConstraint where
  /-- [loc -]: must occur left-isolated, not VP-internal. -/
  | locMinus
  /-- [neg -]: cannot be negated. -/
  | negMinus
  /-- [ref ∅]: nonreferential — no variable-binding function. -/
  | refEmpty
  deriving DecidableEq, Repr

/-- A slot in a construction's form: filler content, headedness, and the
bar level of the position itself. `level := none` leaves the position's
bar level unspecified; slots sharing a `refIdx` are co-indexed, the hook
by which a typed meaning pole refers to slots. -/
structure Slot (Lex : Type*) where
  /-- What fills this slot -/
  filler : SlotFiller Lex
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

/-- A phrase in a word-level slot: phrasal filler, zero-level position —
the defining configuration of phrasal compounds and the PAL construction
([goldberg-shirtz-2025]), and the cell that lexical-integrity hypotheses
rule out. -/
def Slot.IsPhraseInWordSlot {Lex : Type*} (s : Slot Lex) : Prop :=
  s.filler = .phrasal ∧ s.level = some .zero

instance {Lex : Type*} [DecidableEq Lex] (s : Slot Lex) :
    Decidable s.IsPhraseInWordSlot :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Derived specificity -/

section DerivedSpecificity
variable {Lex : Type*}

/-- The specificity of a form: `fullyAbstract` when every slot is open
(vacuously so for the empty form), `lexicallySpecified` when none is,
and `partiallyOpen` otherwise. -/
def derivedSpecificity (form : TypedForm Lex) : Specificity :=
  let openCount := (form.filter (·.filler.isOpen)).length
  if openCount = form.length then .fullyAbstract
  else if openCount = 0 then .lexicallySpecified
  else .partiallyOpen

/-- Some slot in the form bears the constraint `c`. -/
def HasConstraint (form : TypedForm Lex) (c : SlotConstraint) : Prop :=
  ∃ s ∈ form, c ∈ s.constraints

instance (form : TypedForm Lex) (c : SlotConstraint) :
    Decidable (HasConstraint form c) :=
  inferInstanceAs (Decidable (∃ s ∈ form, c ∈ s.constraints))

/-- Count of distinct coreference groups in a form. -/
def refGroupCount (form : TypedForm Lex) : Nat :=
  (form.filterMap (·.refIdx)).dedup.length

/-! ### Characterization lemmas -/

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

end DerivedSpecificity

/-! ### Constructions and the network -/

/-- A construction: a learned pairing of form and meaning. The meaning
pole is typed by the domain that owns the construction — a composition
rule, a `MeaningComponents` contribution, a presupposition — with `Unit`
for a purely formal record or a defective, form-only construction. -/
structure Construction (Sem : Type*) where
  name : String
  form : TypedForm String
  /-- The meaning pole. -/
  meaning : Sem
  /-- Whether the construction carries a conventional pragmatic point
      ([fillmore-kay-oconnor-1988] §1.1.4). -/
  pragmaticPoint : Bool := false
  deriving DecidableEq, Repr

variable {Sem : Type*}

/-- A construction's specificity, derived from its slot structure. -/
def Construction.specificity (c : Construction Sem) : Specificity :=
  derivedSpecificity c.form

/-- Reinterpret the meaning pole along `f`, keeping the form. -/
def Construction.map {Sem' : Type*} (f : Sem → Sem') (c : Construction Sem) :
    Construction Sem' :=
  { name := c.name, form := c.form, meaning := f c.meaning
  , pragmaticPoint := c.pragmaticPoint }

/-- An inheritance link between two constructions in the network,
recording how information flows and what semantic relation holds; purely
taxonomic links use `linkType := none`. -/
structure InheritanceLink where
  /-- Name of the parent construction. -/
  parent : String
  /-- Name of the child construction. -/
  child : String
  /-- How information flows along the link. -/
  mode : InheritanceMode
  /-- The semantic relation the link records, if any. -/
  linkType : Option LinkType := none
  /-- Properties the child inherits from the parent. -/
  sharedProperties : List String
  /-- Inherited properties the child overrides. -/
  overriddenProperties : List String := []
  deriving Repr, DecidableEq

/-- A constructicon: a network of constructions connected by inheritance
links. -/
structure Constructicon (Sem : Type*) where
  /-- The inventory of constructions. -/
  constructions : List (Construction Sem)
  /-- The inheritance links, keyed by construction name. -/
  links : List InheritanceLink
  deriving Repr

end ConstructionGrammar
