import Linglib.Morphology.DistributedMorphology.Fission
import Linglib.Data.Examples.GonzalezPootMcGinnis2006

/-!
# Local versus long-distance Fission in Distributed Morphology

[gonzalez-poot-mcginnis-2006]: the verbal agreement suffixes of Yucatec
Maya come from one node, Agr3, which agrees with both the ergative subject
and the nominative object and is realized by strict scansion of the
Vocabulary (27) with local Fission — an item discharges its features from
one of the node's two matrices and the residue stays available to the
items below. The second- and third-person plural suffixes *-éːʃ* and
*-oʔob* are unspecified for case, so their order is fixed by specificity,
*-éːʃ* before *-oʔob* whatever the grammatical roles ((19)–(22)), and one
scansion never inserts *-oʔob* twice ((23)–(24)); the object–subject
template (18) gets both wrong. Long-distance Fission is rejected: the
split of ergative person onto the auxiliary (Agr1, (43)) and number onto
the verb runs across a word boundary, and first-person number is a person
distinction ((42), on the feature-geometric treatment of first person).

## Main definitions

* `Feature`, `matrix`, `ergMatrix`: the binary features of (26) with case,
  and an argument's matrix.
* `agr3`, `agr1`, `agr2`: the Vocabularies (27), (43), (44).
* `suffixes`: Agr3's exponents for a subject and an object, by `scansion`.
* `templateSuffixes`: the rival template (18), one node per argument.

## Main results

* `suffixes_rows`: every row of the pool is grammatical iff its suffixes are
  `suffixes`' output.
* `template_predicts_starred`, `template_fails_grammatical`: the template
  predicts the starred orders of (21) and (23) and fails (22) and (24).
* `aux_prefix_rows`: (43) and (44) recover the auxiliary suffix and the
  verbal prefix of every row.
* `first_person_no_verbal_number`: a first-person ergative argument takes no
  verbal number suffix ((3)–(4)), since its number is not [+Pl].

## Implementation notes

Agr3's list (27) needs the nominative first-person plural to carry [+PSE]
and the singular not to, the reverse of the assignment (42) gives the
ergative auxiliary; the paper does not reconcile the two, so `matrix` follows
(27) for nominative first person and (42) otherwise. The elsewhere *-Ø* is
inserted but not counted among a row's overt suffixes.

## References

* [H. Harley and E. Ritter, *Person and number in pronouns*][harley-ritter-2002]
-/

namespace GonzalezPootMcGinnis2006

open DistributedMorphology Data.Examples
open scoped DistributedMorphology.VocabularyItem

/-! ### Features and matrices (§3–4) -/

/-- Case of an agreeing argument. -/
inductive Case where
  | nom
  | erg
  deriving DecidableEq, Repr

/-- The binary person features of (26), number as [±Pl], and case. -/
inductive Feature where
  | pse (b : Bool)
  | auth (b : Bool)
  | pl (b : Bool)
  | case (c : Case)
  deriving DecidableEq, Repr

/-- Grammatical person. -/
inductive Person where
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- An ergative argument's matrix ((42)): first-person number is a person
distinction — singular [+PSE, +Auth], plural [+Auth]. -/
def ergMatrix : Person → Bool → List Feature
  | .first, false => [.pse true, .auth true, .case .erg]
  | .first, true => [.auth true, .case .erg]
  | .second, pl => [.pse true, .auth false, .pl pl, .case .erg]
  | .third, pl => [.pse false, .auth false, .pl pl, .case .erg]

/-- An argument's matrix for Agr3: (42) for ergative arguments and for
second and third person; for nominative first person the assignment (27)
presupposes — *-oʔon* 1pl [+PSE, +Auth, NOM], *-en* 1sg [+Auth, NOM]. -/
def matrix : Person → Bool → Case → List Feature
  | .first, false, .nom => [.auth true, .case .nom]
  | .first, true, .nom => [.pse true, .auth true, .case .nom]
  | p, pl, .erg => ergMatrix p pl
  | .second, pl, .nom => [.pse true, .auth false, .pl pl, .case .nom]
  | .third, pl, .nom => [.pse false, .auth false, .pl pl, .case .nom]

/-! ### The Vocabularies (27), (43), (44) -/

/-- The Agr3 Vocabulary Items (27), in scansion order. -/
def agr3 : List (VocabularyItem Feature String) :=
  [[.pse true, .auth true, .case .nom] ⟷ "oʔon", [.pse true, .pl false, .case .nom] ⟷ "etʃ",
    [.auth true, .case .nom] ⟷ "en", [.pse true, .pl true] ⟷ "éːʃ", [.pl true] ⟷ "oʔob",
    [] ⟷ "Ø"]

/-- The Agr1 Vocabulary Items (43): the ergative auxiliary suffix. -/
def agr1 : List (VocabularyItem Feature String) :=
  [[.pse true, .auth true] ⟷ "in", [.auth true] ⟷ "k", [.pse true] ⟷ "a", [] ⟷ "u"]

/-- The Agr2 Vocabulary Items (44): the ergative verbal prefix. -/
def agr2 : List (VocabularyItem Feature String) :=
  [[.pse true] ⟷ "w", [.pse false] ⟷ "j", [] ⟷ ""]

/-- The overt verbal suffixes of a clause: Agr3 bears the subject's matrix
and, in a transitive clause, the object's ((25), (28b)); strict scansion of
(27) realizes them, and the elsewhere *-Ø* is not overt. -/
def suffixes (subj : Person × Bool) (obj : Option (Person × Bool)) : List String :=
  (scansion agr3 ∅ (matrix subj.1 subj.2 .erg :: (obj.map fun o => [matrix o.1 o.2 .nom]).getD []))
    |>.filter (· ≠ "Ø")

/-- The rival template (18): object agreement then subject agreement, each a
node of its own realized by the Subset Principle over (27). -/
def templateSuffixes (subj obj : Person × Bool) : List String :=
  ((subsetPrinciple agr3 (matrix obj.1 obj.2 .nom)).toList ++
    (subsetPrinciple agr3 (matrix subj.1 subj.2 .erg)).toList).filter (· ≠ "Ø")

/-! ### The data pool -/

/-- A row of the pool: the arguments, the auxiliary suffix, the verbal
prefix, the overt verbal suffixes, and the judgment. -/
structure Row where
  subj : Person × Bool
  obj : Option (Person × Bool)
  aux : String
  prefix_ : String
  suffixes : List String
  accepted : Bool
  deriving DecidableEq, Repr

def Person.ofString : String → Option Person
  | "1" => some .first | "2" => some .second | "3" => some .third | _ => none

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let fs := ex.paperFeatures
  let sp ← fs.lookup "subjPerson" >>= Person.ofString
  let sn ← fs.lookup "subjNumber"
  let obj ← match fs.lookup "objPerson", fs.lookup "objNumber" with
    | some p, some n => (Person.ofString p).map fun op => some (op, decide (n = "pl"))
    | _, _ => some none
  let aux ← fs.lookup "aux"
  let prefix_ ← fs.lookup "prefix"
  let s₁ ← fs.lookup "suffix1"
  let s₂ ← fs.lookup "suffix2"
  pure ⟨(sp, sn = "pl"), obj, aux, prefix_, [s₁, s₂].filter (· ≠ ""), ex.judgment = .acceptable⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- **Local Fission** ((19)–(24), (16)): a row is grammatical iff its overt
verbal suffixes are what strict scansion of (27) inserts — *-éːʃ* before
*-oʔob* in both (20) and (22), *-oʔob* once in (24). -/
theorem suffixes_rows : ∀ r ∈ rows, r.accepted = (suffixes r.subj r.obj = r.suffixes) := by
  decide

/-- The template (18) predicts every starred form — *-oʔob-éːʃ* for (21),
*-oʔob-oʔob* for (23). -/
theorem template_predicts_starred :
    ∀ r ∈ rows, ∀ o ∈ r.obj, r.accepted = false → templateSuffixes r.subj o = r.suffixes := by
  decide

/-- The template (18) fails a grammatical row — (22) and (24), whose orders
it reverses or doubles — while fitting (19) and (20). -/
theorem template_fails_grammatical :
    ∃ r ∈ rows, r.accepted ∧ ∃ o ∈ r.obj, templateSuffixes r.subj o ≠ r.suffixes := by
  decide

/-- Agr1 (43) and Agr2 (44) recover the auxiliary suffix and verbal prefix of
every row ((17), (39)). -/
theorem aux_prefix_rows :
    ∀ r ∈ rows, subsetPrinciple agr1 (ergMatrix r.subj.1 r.subj.2) = some r.aux ∧
      subsetPrinciple agr2 (ergMatrix r.subj.1 r.subj.2) = some r.prefix_ := by
  decide

/-- A first-person ergative argument takes no verbal number suffix ((3)–(4)):
its number is a person distinction, so no item of (27) matches beyond the
elsewhere. -/
theorem first_person_no_verbal_number (pl : Bool) :
    suffixes (.first, pl) none = [] := by
  cases pl <;> decide

end GonzalezPootMcGinnis2006
