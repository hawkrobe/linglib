module

public import Linglib.Syntax.Tree.Cat
public import Linglib.Data.Examples.Ross1967

/-!
# Ross (1967): Constraints on Variables in Syntax

This file formalizes the dissertation's constraints on the variables of reordering
transformations, stated over the positions a moved constituent leaves behind in a
constituent-structure tree: the Complex NP Constraint, that nothing is moved out of a sentence
dominated by a noun phrase with a lexical head noun (`CNPC`); the Coordinate Structure
Constraint, that no conjunct is moved and nothing is moved out of a conjunct (`CSC`); the Left
Branch Condition, that no noun phrase on the left branch of a larger noun phrase is moved out
of it (`LBC`); and the Sentential Subject Constraint, that nothing is moved out of a sentence
in subject position (`SSC`). A movement is a source position and a landing position in a tree,
and a constraint is violated when the positions the movement crosses, the ancestors of the
source that do not dominate the landing site, contain the configuration the constraint names.
The dissertation's examples are rows whose trees and movements are built here, and
`chopping_rows` reads their judgments as the constraints predict, the acceptable ones being
exactly those that violate none; `copying_rows` is the dissertation's other generalization,
that a copying rule such as Left Dislocation, which leaves a pronoun behind, crosses every one
of these islands freely.

## Implementation notes

Trees carry the UD-grounded categories of `Syntax.Cat`, a noun phrase being the projection of
a noun, a coordinate structure the projection of a conjunction with the conjuncts and the
conjunction words as its daughters, and a lexical head noun a noun terminal among an NP's
daughters. The trees are the dissertation's diagrams reduced to the categories the constraints
mention, with the moved constituent in its source position; questions and topicalizations
land at the root and relativizations at the relative clause. Dominance in the Sentential
Subject Constraint is read as immediate, the configuration of a sentence exhaustively
dominated by a subject NP, so that the constraint does not reach a clause inside a relative
clause on a subject. The A-over-A principle, the pied-piping convention, upward boundedness,
and the definition of islands as the domains of chopping rules are not formalized.

## References

* [ross-1967]
-/

@[expose] public section

namespace Ross1967

open Syntax Data.Examples Core.Order

/-! ### Trees and movements -/

/-- The categories the constraints mention. -/
abbrev NP : Cat := .proj .NOUN
abbrev VP : Cat := .proj .VERB
abbrev PP : Cat := .proj .ADP
abbrev AP : Cat := .proj .ADJ
/-- A coordinate structure, the projection of a conjunction. -/
abbrev Coord : Cat := .proj .CCONJ

/-- A word of a part of speech. -/
def w (pos : UD.UPOS) (form : String) : Tree Cat String := .terminal (.head pos) form

/-- A movement in a tree: the position of the moved constituent and the position it lands
at. -/
structure Movement where
  tree : Tree Cat String
  source : List ℕ
  landing : List ℕ

namespace Movement

variable (m : Movement)

/-- The subtree at a position. -/
def at? (p : List ℕ) : Option (Tree Cat String) := Branching.subtreeAt m.tree p

/-- The category at a position. -/
def cat? (p : List ℕ) : Option Cat := (m.at? p).map Tree.cat

/-- The positions the movement crosses: the strict ancestors of the source that do not
dominate the landing site, the constituents the moved element is moved out of. -/
def crossed : List (List ℕ) :=
  m.source.inits.filter λ p => p ≠ m.source ∧ ¬ p <+: m.landing

/-- A noun phrase with a lexical head noun: a noun among its daughters. -/
def LexicalNP (t : Tree Cat String) : Prop :=
  t.cat = NP ∧ ∃ d ∈ Branching.children t, d.cat = .head .NOUN

instance (t : Tree Cat String) : Decidable (LexicalNP t) := inferInstanceAs (Decidable (_ ∧ _))

/-- A conjunct: a daughter of a coordinate structure other than a conjunction word. -/
def IsConjunct (p : List ℕ) : Prop :=
  m.cat? p.dropLast = some Coord ∧ m.cat? p ≠ some (.head .CCONJ)

instance (p : List ℕ) : Decidable (m.IsConjunct p) := inferInstanceAs (Decidable (_ ∧ _))

/-- The Complex NP Constraint: the movement leaves a sentence and the noun phrase with a
lexical head noun immediately dominating it. -/
def CNPC : Prop :=
  ∃ s ∈ m.crossed, m.cat? s = some .S ∧ s.dropLast ∈ m.crossed ∧
    ∃ t ∈ m.at? s.dropLast, LexicalNP t

/-- The Coordinate Structure Constraint: the moved element is a conjunct leaving its
coordinate structure, or the movement leaves a conjunct. -/
def CSC : Prop :=
  (m.IsConjunct m.source ∧ m.source.dropLast ∈ m.crossed) ∨
    ∃ c ∈ m.crossed, m.IsConjunct c

/-- The Sentential Subject Constraint: the movement leaves a sentence immediately dominated
by a noun phrase that is itself immediately dominated by a sentence. -/
def SSC : Prop :=
  ∃ s ∈ m.crossed, m.cat? s = some .S ∧ m.cat? s.dropLast = some NP ∧
    m.cat? s.dropLast.dropLast = some .S

/-- The Left Branch Condition: the moved element is a noun phrase that is the leftmost
daughter of a noun phrase the movement leaves. -/
def LBC : Prop :=
  m.cat? m.source = some NP ∧ m.source.getLast? = some 0 ∧
    m.cat? m.source.dropLast = some NP ∧ m.source.dropLast ∈ m.crossed

instance : Decidable m.CNPC := by unfold CNPC; infer_instance
instance : Decidable m.CSC := by unfold CSC; infer_instance
instance : Decidable m.SSC := by unfold SSC; infer_instance
instance : Decidable m.LBC := by unfold LBC; infer_instance

/-- The movement violates one of the four constraints. -/
def Violates : Prop := m.CNPC ∨ m.CSC ∨ m.SSC ∨ m.LBC

instance : Decidable m.Violates := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

end Movement

/-! ### The dissertation's examples -/

/-- *Who does Phineas know a girl who is jealous of?*: the questioned NP inside the relative
clause on *girl*. -/
def phineas : Tree Cat String :=
  .node .S [.node NP [w .PROPN "Phineas"],
    .node VP [w .VERB "knows",
      .node NP [w .DET "a", w .NOUN "girl",
        .node .S [.node NP [w .PRON "who"],
          .node VP [w .AUX "is",
            .node AP [w .ADJ "jealous", .node PP [w .ADP "of", .node NP [w .PRON "who"]]]]]]]]

/-- The relative clause of *the hat which I believed the claim that Otto was wearing*. -/
def hatClaim : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "hat",
      .node .S [.node NP [w .PRON "I"],
        .node VP [w .VERB "believed",
          .node NP [w .DET "the", w .NOUN "claim",
            .node .S [w .SCONJ "that", .node NP [w .PROPN "Otto"],
              .node VP [w .AUX "was", w .VERB "wearing", .node NP [w .PRON "which"]]]]]]],
    .node VP [w .AUX "is", w .ADJ "red"]]

/-- The relative clause of *the hat which I believed that Otto was wearing*. -/
def hatThat : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "hat",
      .node .S [.node NP [w .PRON "I"],
        .node VP [w .VERB "believed",
          .node .S [w .SCONJ "that", .node NP [w .PROPN "Otto"],
            .node VP [w .AUX "was", w .VERB "wearing", .node NP [w .PRON "which"]]]]]],
    .node VP [w .AUX "is", w .ADJ "red"]]

/-- *What sofa will he put the chair between some table and?*: the questioned NP a conjunct. -/
def sofa : Tree Cat String :=
  .node .S [.node NP [w .PRON "he"],
    .node VP [w .VERB "put", .node NP [w .DET "the", w .NOUN "chair"],
      .node PP [w .ADP "between",
        .node Coord [.node NP [w .DET "some", w .NOUN "table"], w .CCONJ "and",
          .node NP [w .DET "what", w .NOUN "sofa"]]]]]

/-- *The lute which Henry plays and sings madrigals*: relativization out of a conjoined VP. -/
def lute : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "lute",
      .node .S [.node NP [w .PROPN "Henry"],
        .node Coord [.node VP [w .VERB "plays", .node NP [w .PRON "which"]], w .CCONJ "and",
          .node VP [w .VERB "sings", .node NP [w .NOUN "madrigals"]]]]],
    .node VP [w .AUX "is", w .ADJ "warped"]]

/-- *Which trombone did the nurse polish and the plumber computed my tax?*: questioning out
of a conjoined sentence. -/
def trombone : Tree Cat String :=
  .node .S [.node Coord [
    .node .S [.node NP [w .DET "the", w .NOUN "nurse"],
      .node VP [w .VERB "polish", .node NP [w .DET "which", w .NOUN "trombone"]]],
    w .CCONJ "and",
    .node .S [.node NP [w .DET "the", w .NOUN "plumber"],
      .node VP [w .VERB "computed", .node NP [w .PRON "my", w .NOUN "tax"]]]]]

/-- *The boy whose guardian's employer we elected president*: the possessor NPs nested on
left branches. -/
def guardian : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "boy",
      .node .S [.node NP [w .PRON "we"],
        .node VP [w .VERB "elected",
          .node NP [.node NP [.node NP [w .PRON "whose"], w .NOUN "guardian's"],
            w .NOUN "employer"],
          .node NP [w .NOUN "president"]]]],
    .node VP [w .VERB "ratted", .node PP [w .ADP "on", .node NP [w .PRON "us"]]]]

/-- The predicate of the teacher sentences. -/
def battleax : Tree Cat String :=
  .node VP [w .AUX "is",
    .node NP [w .DET "a", w .ADJ "crusty", w .ADJ "old", w .NOUN "battleax"]]

/-- *that the principal would fire who*. -/
def fireClause : Tree Cat String :=
  .node .S [w .SCONJ "that", .node NP [w .DET "the", w .NOUN "principal"],
    .node VP [w .AUX "would", w .VERB "fire", .node NP [w .PRON "who"]]]

/-- *The teacher who the reporters expected that the principal would fire*. -/
def teacherActive : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "teacher",
      .node .S [.node NP [w .DET "the", w .NOUN "reporters"],
        .node VP [w .VERB "expected", fireClause]]],
    battleax]

/-- *The teacher who that the principal would fire was expected by the reporters*: the
that-clause a sentential subject. -/
def teacherPassive : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "teacher",
      .node .S [.node NP [fireClause],
        .node VP [w .AUX "was", w .VERB "expected",
          .node PP [w .ADP "by", .node NP [w .DET "the", w .NOUN "reporters"]]]]],
    battleax]

/-- *The teacher who it was expected by the reporters that the principal would fire*: the
that-clause extraposed. -/
def teacherExtraposed : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "teacher",
      .node .S [.node NP [w .PRON "it"],
        .node VP [w .AUX "was", w .VERB "expected",
          .node PP [w .ADP "by", .node NP [w .DET "the", w .NOUN "reporters"]], fireClause]]],
    battleax]

/-- *Of which cars were the hoods damaged by the explosion?*: a subconstituent of a phrasal
subject. -/
def hoods : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "hoods",
      .node PP [w .ADP "of", .node NP [w .DET "which", w .NOUN "cars"]]],
    .node VP [w .AUX "were", w .VERB "damaged",
      .node PP [w .ADP "by", .node NP [w .DET "the", w .NOUN "explosion"]]]]

/-- *My father, the man he works with in Boston is going to tell the police …*: the
dislocated NP the subject of a relative clause. -/
def father : Tree Cat String :=
  .node .S [.node NP [w .DET "the", w .NOUN "man",
      .node .S [.node NP [w .PRON "my", w .NOUN "father"],
        .node VP [w .VERB "works", .node PP [w .ADP "with", .node NP [w .PRON "who"]],
          .node PP [w .ADP "in", .node NP [w .PROPN "Boston"]]]]],
    .node VP [w .AUX "is", w .VERB "going",
      .node PP [w .ADP "to", .node VP [w .VERB "tell", .node NP [w .DET "the", w .NOUN "police"]]]]]

/-- *This guitar, I've sung folksongs and accompanied myself on it all my life*: the
dislocated NP inside a conjunct. -/
def guitar : Tree Cat String :=
  .node .S [.node NP [w .PRON "I"],
    .node VP [w .AUX "have",
      .node Coord [.node VP [w .VERB "sung", .node NP [w .NOUN "folksongs"]], w .CCONJ "and",
        .node VP [w .VERB "accompanied", .node NP [w .PRON "myself"],
          .node PP [w .ADP "on", .node NP [w .DET "this", w .NOUN "guitar"]]]]]]

/-- *My father, that he's lived here all his life is well-known to the cops*: the dislocated
NP inside a sentential subject. -/
def lived : Tree Cat String :=
  .node .S [.node NP [.node .S [w .SCONJ "that", .node NP [w .PRON "my", w .NOUN "father"],
      .node VP [w .AUX "has", w .VERB "lived", w .ADV "here",
        .node NP [w .DET "all", w .PRON "his", w .NOUN "life"]]]],
    .node VP [w .AUX "is", w .ADJ "well-known",
      .node PP [w .ADP "to", .node NP [w .DET "the", w .NOUN "cops"]]]]

/-- *My wife, somebody stole her handbag last night*: the dislocated NP a possessor on a left
branch. -/
def handbag : Tree Cat String :=
  .node .S [.node NP [w .PRON "somebody"],
    .node VP [w .VERB "stole",
      .node NP [.node NP [w .PRON "my", w .NOUN "wife"], w .NOUN "handbag"],
      .node NP [w .ADJ "last", w .NOUN "night"]]]

/-- The movement of each example, by the dissertation's number: questions and dislocations
land at the root, relativizations at the relative clause. -/
def movement : String → Option Movement
  | "(4.15a)" => some ⟨phineas, [1, 1, 2, 1, 1, 1, 1], []⟩
  | "(4.18a)" => some ⟨hatClaim, [0, 2, 1, 1, 2, 2, 2], [0, 2]⟩
  | "(4.18b)" => some ⟨hatThat, [0, 2, 1, 1, 2, 2], [0, 2]⟩
  | "(2.18)" => some ⟨sofa, [1, 2, 1, 2], []⟩
  | "(4.82a)" => some ⟨lute, [0, 2, 1, 0, 1], [0, 2]⟩
  | "(4.82d)" => some ⟨trombone, [0, 0, 1, 1], []⟩
  | "(4.184a)" => some ⟨guardian, [0, 2, 1, 1], [0, 2]⟩
  | "(4.184b)" => some ⟨guardian, [0, 2, 1, 1, 0], [0, 2]⟩
  | "(4.184c)" => some ⟨guardian, [0, 2, 1, 1, 0, 0], [0, 2]⟩
  | "(4.251a)" => some ⟨teacherActive, [0, 2, 1, 1, 2, 2], [0, 2]⟩
  | "(4.251b)" => some ⟨teacherPassive, [0, 2, 0, 0, 2, 2], [0, 2]⟩
  | "(4.251c)" => some ⟨teacherExtraposed, [0, 2, 1, 3, 2, 2], [0, 2]⟩
  | "(4.252)" => some ⟨hoods, [0, 2], []⟩
  | "(6.128b)" => some ⟨father, [0, 2, 0], []⟩
  | "(6.135b)" => some ⟨guitar, [1, 1, 2, 2, 1], []⟩
  | "(6.136)" => some ⟨lived, [0, 0, 1], []⟩
  | "(6.137)" => some ⟨handbag, [1, 1, 0], []⟩
  | _ => none

/-! ### The rows -/

/-- Whether a reordering rule chops its term, substituting nothing or another term for it, or
copies it, leaving a pronoun in its place. -/
inductive Rule
  | chopping
  | copying
  deriving DecidableEq, Repr

/-- The four constraints. -/
inductive Constraint
  | cnpc
  | csc
  | ssc
  | lbc
  deriving DecidableEq, Repr

/-- The constraint's condition on a movement. -/
def Constraint.Fires : Constraint → Movement → Prop
  | .cnpc, m => m.CNPC
  | .csc, m => m.CSC
  | .ssc, m => m.SSC
  | .lbc, m => m.LBC

instance (c : Constraint) (m : Movement) : Decidable (c.Fires m) := by
  unfold Constraint.Fires; cases c <;> infer_instance

/-- An example: its movement, the kind of rule that moved it, the constraint the dissertation
holds responsible, if any, and its judgment. -/
structure Datum where
  movement : Movement
  rule : Rule
  constraint : Option Constraint
  judgment : Judgment

/-- The row of an example. -/
def datum (r : LinguisticExample) : Option Datum := do
  let m ← movement r.source.paperLabel
  let rule ← r.parse? "rule" [("question", Rule.chopping), ("relativization", .chopping),
    ("topicalization", .chopping), ("leftDislocation", .copying)]
  let c := r.parse? "constraint" [("CNPC", Constraint.cnpc), ("CSC", .csc), ("SSC", .ssc),
    ("LBC", .lbc)]
  pure ⟨m, rule, c, r.judgment⟩

/-- The examples. -/
def data : List Datum := Examples.all.filterMap datum

/-- Every row has its movement. -/
theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- The constraints on chopping rules: a question or relativization is acceptable exactly when
it violates none of the four. -/
theorem chopping_rows :
    ∀ d ∈ data, d.rule = .chopping →
      (d.judgment = .acceptable ↔ ¬ d.movement.Violates) := by
  decide +kernel

/-- The constraint the dissertation names for a starred example, or for a dislocation, is one
its movement violates. -/
theorem attributions : ∀ d ∈ data, ∀ c ∈ d.constraint, c.Fires d.movement := by
  decide +kernel

/-- Copying rules are not subject to the constraints: each Left Dislocation crosses one of the
four islands and is acceptable. -/
theorem copying_rows :
    ∀ d ∈ data, d.rule = .copying → d.judgment = .acceptable ∧ d.movement.Violates := by
  decide +kernel

/-- The Sentential Subject Constraint is not the Complex NP Constraint: the sentential subject
has no lexical head noun, and the noun complement clause is not a subject. -/
theorem ssc_cnpc_independent :
    (∃ d ∈ data, d.movement.SSC ∧ ¬ d.movement.CNPC) ∧
      ∃ d ∈ data, d.movement.CNPC ∧ ¬ d.movement.SSC := by
  decide +kernel

end Ross1967
