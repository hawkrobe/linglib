/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.ConstructionGrammar.Basic

/-!
# Construction Grammar: Idioms

An idiomatic expression is something a language user could fail to know
while knowing everything else in the language ([fillmore-kay-oconnor-1988]
§1). This file defines the paper's classificatory dimensions — decoding
vs. encoding-only, grammatical vs. extragrammatical, substantive vs.
formal — and its §1.2 typology by familiarity of pieces and of
arrangement, with formality derived from the typed form rather than
stipulated.

## Main definitions

- `IdiomInterpretability`: decoding vs. encoding-only idioms
- `IdiomGrammaticality`: grammatical vs. extragrammatical idioms
- `IdiomFormality.ofForm`: substantive vs. formal, read off the slot
  structure
- `Construction.IsFormalIdiom`: constructions whose form is lexically
  open
- `FamiliarityPattern`: the pieces × arrangement typology, its fourth
  cell excluded by `piecesFamiliar_of_arrangementFamiliar`

## Implementation notes

The paper's fourth contrast — idioms with vs. without pragmatic point
(§1.1.4) — is the `Construction.pragmaticPoint` field.
-/

namespace ConstructionGrammar

variable {Lex : Type*}

/-- A decoding idiom cannot be interpreted with confidence without prior
learning; an encoding idiom is one whose conventionality must be learned.
Every decoding idiom is an encoding idiom, so the cases are decoding
("kick the bucket", "pull a fast one") and encoding-only ("answer the
door", "wide awake", "bright red") ([fillmore-kay-oconnor-1988] §1.1.1,
following [makkai-1972]). -/
inductive IdiomInterpretability where
  | decoding
  | encodingOnly
  deriving DecidableEq, Repr

/-- A grammatical idiom has words filling proper and familiar grammatical
structures ("kick the bucket", "spill the beans", "blow one's nose"); an
extragrammatical idiom has structure the rest of the grammar cannot
account for ("first off", "sight unseen", "all of a sudden", "by and
large") ([fillmore-kay-oconnor-1988] §1.1.2). -/
inductive IdiomGrammaticality where
  | grammatical
  | extragrammatical
  deriving DecidableEq, Repr

/-- A substantive (lexically filled) idiom has fixed lexical content
("kick the bucket"); a formal (lexically open) idiom is a syntactic
pattern dedicated to semantic and pragmatic purposes not knowable from
its form alone ("the X-er the Y-er") ([fillmore-kay-oconnor-1988]
§1.1.3). -/
inductive IdiomFormality where
  | substantive
  | formal
  deriving DecidableEq, Repr

/-- The formality of a typed form: substantive iff lexically specified.
The distinction is a cline ([fillmore-kay-oconnor-1988] fn. 3);
`derivedSpecificity` discretizes it. -/
def IdiomFormality.ofForm (form : TypedForm Lex) : IdiomFormality :=
  if derivedSpecificity form = .lexicallySpecified then .substantive else .formal

/-- A form is substantive exactly when it is nonempty and no slot is
open. -/
theorem IdiomFormality.ofForm_eq_substantive_iff (form : TypedForm Lex) :
    ofForm form = .substantive ↔
      form ≠ [] ∧ ∀ s ∈ form, s.filler.isOpen = false := by
  rw [← derivedSpecificity_eq_lexicallySpecified_iff]
  unfold ofForm
  split_ifs with h <;> simp [h]

/-- A formal idiom in the sense of [fillmore-kay-oconnor-1988] §1.1.3: a
construction whose form is lexically open. -/
def Construction.IsFormalIdiom {Sem : Type*} (c : Construction Sem) : Prop :=
  IdiomFormality.ofForm c.form = .formal

instance {Sem : Type*} (c : Construction Sem) : Decidable c.IsFormalIdiom :=
  inferInstanceAs (Decidable (_ = _))

/-- How familiar are an idiom's pieces, and how familiar is their
arrangement ([fillmore-kay-oconnor-1988] §1.2)? Unfamiliar pieces
unfamiliarly arranged: "kith and kin" (§1.2.1); familiar pieces
unfamiliarly arranged: "all of a sudden", bare "home" (§1.2.2); familiar
pieces familiarly arranged: "hang one on", rhetorical questions (§1.2.3).
The fourth cell is excluded by `piecesFamiliar_of_arrangementFamiliar`. -/
inductive FamiliarityPattern where
  | unfamiliarPiecesUnfamiliarlyArranged
  | familiarPiecesUnfamiliarlyArranged
  | familiarPiecesFamiliarlyArranged
  deriving DecidableEq, Repr

namespace FamiliarityPattern

/-- The pieces coordinate: the idiom's pieces occur independently in the
language. Fails only for idioms built on cranberry words ("kith",
"main"). -/
def PiecesFamiliar : FamiliarityPattern → Prop :=
  (· ≠ unfamiliarPiecesUnfamiliarlyArranged)

/-- The arrangement coordinate: the pieces are combined according to
familiar combinatorial principles. -/
def ArrangementFamiliar : FamiliarityPattern → Prop :=
  (· = familiarPiecesFamiliarlyArranged)

instance (p : FamiliarityPattern) : Decidable p.PiecesFamiliar :=
  inferInstanceAs (Decidable ¬_)

instance (p : FamiliarityPattern) : Decidable p.ArrangementFamiliar :=
  inferInstanceAs (Decidable (_ = _))

/-- A familiar arrangement forces familiar pieces: unique pieces admit no
standard principles of arrangement ([fillmore-kay-oconnor-1988] §1.2.1),
so the fourth familiarity cell is uninhabited. -/
theorem piecesFamiliar_of_arrangementFamiliar {p : FamiliarityPattern}
    (h : p.ArrangementFamiliar) : p.PiecesFamiliar := by
  cases p <;> simp_all [PiecesFamiliar, ArrangementFamiliar]

/-- An idiom's §1.1.2 classification, determined by its familiarity
pattern: an arrangement is familiar exactly when the general grammar
accounts for it ([fillmore-kay-oconnor-1988] §1.2.2–1.2.3). -/
def grammaticality : FamiliarityPattern → IdiomGrammaticality
  | familiarPiecesFamiliarlyArranged => .grammatical
  | _ => .extragrammatical

/-- A pattern is grammatical exactly when its arrangement is familiar. -/
theorem grammaticality_eq_grammatical_iff (p : FamiliarityPattern) :
    p.grammaticality = .grammatical ↔ p.ArrangementFamiliar := by
  cases p <;> simp [grammaticality, ArrangementFamiliar]

end FamiliarityPattern

end ConstructionGrammar
