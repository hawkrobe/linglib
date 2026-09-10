import Linglib.Syntax.ConstructionGrammar.Resultatives
import Linglib.Syntax.Category.Verb.Argument
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.GoldbergJackendoff2004

/-!
# Goldberg and Jackendoff (2004): The English Resultative as a Family of Constructions

This file formalizes [goldberg-jackendoff-2004]'s resultative family on the paper's own examples:
the four subconstructions of section 2, the for-adverbial telicity diagnostic of section 4.1, and
the semantic coherence principle of section 6.2. The family, its subevent structure, and the
principle live in `ConstructionGrammar.Resultatives`; each example row names its verb in the
English fragment and its subconstruction, and the theorems derive the paper's judgments from them.

A result phrase telicizes the resultative exactly when it is end-bounded, so on a nonrepetitive
reading the for-adverbial is acceptable exactly when the result phrase is not
(`rows_for_adverbial`). A verb role may fuse with the construction's undergoer only when it is
construable as an instance of it (`rows_coherence`): the agent subjects of *yell* and *cry* cannot
be the patient of BECOME, while the subject of *bleed* and the object of *wipe* can. The paper's
roles agree with the fragment: the patient subjects are those whose Levin class predicts
unaccusativity (`rows_verbRole_unaccusative`), and the label the citation frame derives, where it
derives one, is the paper's (`rows_verbRole_thetaLabel`).

## Implementation notes

The paper labels result phrases only as AP or PP; the subconstruction recorded on each row follows
the summary (97), where a PP naming a state (*into pieces*, *to death*) is a property result
phrase. The paper's role for the fusing verb argument is the `verbRole` feature; the fragment
derives a label only where the citation frame carries an entailment profile.

## References

* [goldberg-jackendoff-2004]
* [goldberg-1995]
* [levin-hovav-1995]
* [dowty-1991]
-/

namespace GoldbergJackendoff2004

open ConstructionGrammar.Resultatives ArgumentStructure Features Data.Examples
open English.Predicates.Verbal

/-- An example row: the verb, the subconstruction, how its subevents relate, the object
selection of a transitive, the end-boundedness of the result phrase where the paper tests it,
the paper's role for the verb argument that fuses with the construction's undergoer, and the
judgment. -/
structure Row where
  verb : VerbEntry
  subconstruction : ResultativeSubconstruction
  relation : SubeventRelation
  selection : Option ObjectSelection
  boundedness : Option Boundedness
  verbRole : Option ThetaRole
  judgment : Judgment

/-- The paper's verbs, by citation form. -/
private def verbs : List (String × VerbEntry) :=
  [("hammer", hammer), ("laugh", laugh), ("freeze", freeze), ("roll", roll), ("water", water),
   ("break", break_), ("drink", drink), ("talk", talk), ("yell", yell), ("heat", heat),
   ("weave", weave), ("float", float), ("push", push), ("cry", cry), ("bleed", bleed),
   ("wipe", wipe), ("rumble", rumble)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let verb ← ex.parse? "verb" verbs
  let subconstruction ← ex.parse? "subconstruction"
    [("causative property", .causativeProperty), ("causative path", .causativePath),
     ("noncausative property", .noncausativeProperty), ("noncausative path", .noncausativePath)]
  pure { verb, subconstruction
         relation := (ex.parse? "subeventRelation" [("result", .result)]).getD .means
         selection := ex.parse? "selection"
           [("selected", .selected), ("unselected", .unselected),
            ("fake reflexive", .fakeReflexive)]
         boundedness := ex.parse? "endBounded" [("true", .bounded), ("false", .unbounded)]
         verbRole := ex.parse? "verbRole" [("agent", .agent), ("patient", .patient)]
         judgment := ex.judgment }

/-- The paper's examples (5)–(9), (23)–(24), (45), (97c), and *wipe the table clean*. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

example : rows.length = Examples.all.length := by decide

-- Object selection is a dimension of the transitive, that is causative, subconstructions.
example : ∀ r ∈ rows, r.selection.isSome → r.subconstruction.isCausative = true := by decide

/-- Section 4.1: on a nonrepetitive reading the for-adverbial is acceptable exactly when the
result phrase is not end-bounded, that is, when the resultative is atelic. -/
theorem rows_for_adverbial :
    ∀ r ∈ rows, ∀ b ∈ r.boundedness,
      (r.judgment = .acceptable ↔ (resultativeAspect b).telicity = .atelic) := by
  decide

/-- Section 6.2: the resultative is acceptable exactly when the paper's role for the fusing verb
argument is construable as the construction's undergoer. -/
theorem rows_coherence :
    ∀ r ∈ rows, ∀ ρ ∈ r.verbRole,
      (r.judgment = .acceptable ↔ RolesCoherent ρ r.subconstruction.rpType.undergoer) := by
  decide

/-- The verb argument that fuses with the construction's undergoer: the object of a causative,
the subject of a noncausative. -/
def Row.fusedArgument (r : Row) : Option Verb.Argument :=
  r.verb.arguments[if r.subconstruction.isCausative then 1 else 0]?

/-- The paper's subject roles for the noncausatives are the unaccusativity predictions of the
verbs' Levin classes ([levin-hovav-1995]): *bleed* emits substance, *yell* and *cry* are manner
of speaking. -/
theorem rows_verbRole_unaccusative :
    ∀ r ∈ rows, r.subconstruction.isCausative = false →
      ∀ ρ ∈ r.verbRole, ∀ c ∈ r.verb.levinClass, (ρ = .patient ↔ c.PredictsUnaccusative) := by
  decide

/-- Where the fragment's citation frame derives a role label for the fusing argument, it is the
paper's: the object of *wipe* is construable as a patient. -/
theorem rows_verbRole_thetaLabel :
    ∀ r ∈ rows, ∀ ρ ∈ r.verbRole, ∀ a ∈ r.fusedArgument, ∀ ρ' ∈ a.thetaLabel, ρ' = ρ := by
  decide

end GoldbergJackendoff2004
