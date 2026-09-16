import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Semantics.Presupposition.Environment
import Linglib.Semantics.Presupposition.Basic
import Linglib.Data.Examples.Karttunen1971b

/-!
# Karttunen (1971): Some observations on factivity

This file formalizes the third of Karttunen's observations: the factive verbs are not one
class. Every factive presupposes its complement under negation, (22), but in a question, (24),
and in the antecedent of a conditional, (25), *regret* still commits the speaker to the
complement while *realize* and *discover* do not. The account is a pair of meaning postulates
per verb: the sentence and its negation each imply the complement, (11), and for a true factive
so does the mere possibility of the sentence, (11'). Since a question or a conditional
antecedent conversationally implies only the possibility of its sentence, (26), the complement
follows there from a true factive and not from a semi-factive (`Projects`). The rows record the
judgments, and the prediction matches them (`projection_rows`). The emphatic denial (23) carries
no commitment: it is the external negation of three-valued logic, which is defined whether or
not the presupposition holds (`negExt_no_inference`).

## Implementation notes

* The postulates (11) and (11') are read off the environment: what an environment makes
  available of its sentence is the sentence, its negation, or only its possibility
  (`Environment.available`), and a class yields the complement from the first two, a true
  factive also from the third (`Factivity.Yields`).
* The quantified complements of section 1 and the subjunctive *poss-ing* complements of
  section 2 are not represented.
* The verbs are the English Fragment's entries, whose factivity classes this paper anchors.

## References

* [karttunen-1971b]
* [kiparsky-kiparsky-1970]
-/

namespace Karttunen1971b

open Presupposition Data.Examples English.Predicates.Verbal

/-! ### The meaning postulates -/

/-- What an environment makes available of its sentence is the sentence itself, its negation,
or only its possibility, which a question and a conditional antecedent conversationally imply
((26), fn. 5). -/
inductive Available where
  | sentence
  | negation
  | possibility
  deriving DecidableEq, Repr

/-- The availability each environment provides. -/
def _root_.Presupposition.Environment.available : Environment → Available
  | .atomic => .sentence
  | .negation => .negation
  | .question => .possibility
  | .conditionalAntecedent => .possibility
  | .epistemicModal => .possibility

/-- The postulates of a class say that the sentence and its negation imply the complement for
every factive, (11), and that its possibility does so for a true factive only, (11'). -/
def _root_.Presupposition.Factivity.Yields : Factivity → Available → Prop
  | _, .sentence => True
  | _, .negation => True
  | .full, .possibility => True
  | .semi, .possibility => False

instance (c : Factivity) (a : Available) : Decidable (c.Yields a) := by
  unfold Factivity.Yields; split <;> infer_instance

/-- The complement follows from a sentence with a factive of class `c` in environment `e`. -/
def Projects (c : Factivity) (e : Environment) : Prop := c.Yields e.available

instance (c : Factivity) (e : Environment) : Decidable (Projects c e) :=
  inferInstanceAs (Decidable (c.Yields e.available))

/-- A true factive's complement follows in every environment. -/
theorem projects_full (e : Environment) : Projects .full e := by
  cases e <;> trivial

/-- A semi-factive's complement follows exactly from the sentence or its negation. -/
theorem projects_semi_iff (e : Environment) :
    Projects .semi e ↔ e = .atomic ∨ e = .negation := by
  cases e <;> decide

/-! ### The rows -/

/-- The three verbs of section 3. -/
def verbs : List Verb := [regret.toVerb, realize.toVerb, discover.toVerb]

/-- The Fragment entry for a row's verb. -/
def verbOf (row : LinguisticExample) : Option Verb :=
  (row.feature? "verb").bind (Verb.find? verbs ·)

/-- The judgments of (2), (22) and (24)–(26) are the postulates' predictions, *regret*'s
complement following everywhere and *realize*'s and *discover*'s under negation only. -/
theorem projection_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "projection" →
      ∀ e ∈ row.environment?, ∀ b ∈ row.projective?, ∀ v ∈ verbOf row, ∀ c ∈ v.factivity,
        (b = true ↔ Projects c e) := by
  decide

/-! ### The emphatic denial, (23) -/

variable {W : Type*}

/-- (11): a factive sentence and its internal negation each imply the complement, which is
their shared presupposition. -/
theorem holds_presup (p : PartialProp W) (w : W) :
    (p.holds w → p.presup w) ∧ ((PartialProp.neg p).holds w → p.presup w) :=
  ⟨fun h ↦ h.1, fun h ↦ h.1⟩

/-- Footnote 7: the emphatic denial 'it is not true that A' is the external negation, which
holds whenever `A` fails to hold, so it yields no inference to the presupposition. -/
theorem negExt_no_inference (p : PartialProp W) (w : W) :
    (PartialProp.negExt p).holds w ↔ ¬ p.holds w :=
  ⟨fun h hp ↦ h.2 ⟨hp.1, hp.2⟩, fun h ↦ ⟨trivial, fun hp ↦ h ⟨hp.1, hp.2⟩⟩⟩

end Karttunen1971b
