module

public import Linglib.Data.Examples.Kalin2018
public import Linglib.Syntax.Minimalist.Case.Licensing
public import Mathlib.Data.Finset.Powerset

/-!
# Kalin (2018): Licensing and Differential Object Marking

This file formalizes [kalin-2018], which derives differential object marking from nominal
licensing rather than from object visibility, raising or differentiation. Two parameters
interact: which nominals require licensing, in Senaya only the specific ones, and where the
licensers are, every clause carrying an obligatory licenser that licenses the closest nominal
whatever its needs, and secondary licensers that merge only when the derivation would otherwise
crash, the Licensing Economy Principle, (36). In Senaya the marking is verbal agreement: in the
imperfective, Asp is the obligatory licenser and agrees with the subject as an S-suffix, and T is
a secondary licenser that agrees with a specific object as an L-suffix, (43) and (47); in the
perfective, Asp is no licenser and T is obligatory, so T agrees with the subject and a specific
object cannot be licensed at all, (49) and (50), the ban of (12). The licensing derivation
reproduces the agreement data (8) to (12) and (38) whatever the specificity of the subject
(`rows_agree`), and the toy nominative-accusative language of §3.1 shows differential marking by
a secondary v (`toy_animate_object`, `toy_inanimate_object`). The perfective ban is the paper's
argument against a theory without licensing: the dependent-case rules of [marantz-1991] value the
perfective object accusative, but a specific object there crashes
(`dependentCase_values_banned_object`).

## Implementation notes

* The agreement suffix is read off the licensing head, the S-suffix from Asp and the L-suffix
  from T, the analysis of [kalin-van-urk-2015] that the paper adopts in §4.1.
* In Senaya v is not a phase head (§4.1), so both arguments are in the domain T and Asp probe;
  in the toy language the object is in the domain of v, which the subject is not.
* Word order and the position of agreement within the verbal complex are not modelled.

## References

* [kalin-2018]
* [kalin-van-urk-2015]
* [marantz-1991]
-/

@[expose] public section

namespace Kalin2018

open Data.Examples Minimalist Minimalist.Licensing

/-! ### Senaya's licensers -/

/-- Imperfective Asp, the obligatory licenser of the imperfective, (43). -/
def aspImpf : Licenser := { head := .Asp, kind := .obligatory }

/-- The T selecting imperfective Asp, a secondary licenser, (43). -/
def tImpf : Licenser := { head := .T, kind := .secondary }

/-- The T selecting perfective Asp, the one obligatory licenser of the perfective, (49). -/
def tPfv : Licenser := { head := .T, kind := .obligatory }

/-- The imperfective's licensers in merge order: Asp, then T. -/
def imperfective : List Licenser := [aspImpf, tImpf]

/-- The perfective's licenser: T alone. -/
def perfective : List Licenser := [tPfv]

/-- The one phase domain of a Senaya clause, v being no phase head. -/
def domains : List Cat := [.C]

/-- The agreement suffix a licensing head yields, an S-suffix from Asp and an L-suffix from T. -/
inductive Suffix
  | S
  | L
  deriving DecidableEq, Repr

/-- The suffix agreement with a head yields. -/
def headSuffix : Cat → Option Suffix
  | .Asp => some .S
  | .T => some .L
  | _ => none

/-- The suffix of a nominal's Case value: that of the head that licensed it, if any. -/
def suffixOf : Option CaseValue → Option Suffix
  | some (.licenser l) => headSuffix l.head
  | _ => none

/-- A Senaya nominal, which needs licensing exactly when specific, (40) to (42). -/
def nominal (label : String) (specific : Bool) : LicensedNP :=
  { label, needsLicensing := specific }

/-- A transitive clause's subject and object. -/
def transitive (subject object : Bool) : List LicensedNP :=
  [nominal "subj" subject, nominal "obj" object]

/-! ### The agreement data (Section 2.1) -/

/-- A row carries the aspect's licensers, the object if any, the subject's and the object's
suffix, and the judgment. -/
structure Row where
  clause : List Licenser
  object : Option Bool
  subjectSuffix : Suffix
  objectSuffix : Option Suffix
  grammatical : Bool

/-- A suffix feature value. -/
def suffixFeature : String → Option (Option Suffix)
  | "S" => some (some .S)
  | "L" => some (some .L)
  | "none" => some none
  | _ => none

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let cl ← match e.feature? "aspect" with
    | some "imperfective" => some imperfective
    | some "perfective" => some perfective
    | _ => none
  let obj ← match e.feature? "object" with
    | some "specific" => some (some true)
    | some "nonspecific" => some (some false)
    | some "none" => some none
    | _ => none
  let s ← (e.feature? "subject_suffix").bind suffixFeature
  let s ← s
  let o ← (e.feature? "object_suffix").bind suffixFeature
  some ⟨cl, obj, s, o, e.judgment = .acceptable⟩

/-- The Senaya data, (8) to (12) and (38). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The nominals of a row: a subject of the given specificity, and the row's object if any. -/
def Row.nominals (r : Row) (subject : Bool) : List LicensedNP :=
  nominal "subj" subject :: (r.object.map (nominal "obj")).toList

/-- The suffixes of a row: the subject's, then the object's if there is an object. -/
def Row.suffixes (r : Row) : List (Option Suffix) :=
  some r.subjectSuffix :: (r.object.map fun _ ↦ r.objectSuffix).toList

/-- The suffixes a derivation spells out, nominal by nominal. -/
def suffixes (st : Case.Valuation PhasedNP CaseValue) : List (Option Suffix) :=
  st.map (suffixOf ·.2)

private theorem rows_agree_aux : ∀ r ∈ rows, ∀ subject : Bool,
    (r.grammatical = true ↔ Converges domains r.clause (r.nominals subject)) ∧
    ∀ S ∈ r.clause.toFinset.powerset, Economical domains r.clause (r.nominals subject) S →
      suffixes (license domains (activate r.clause S)
        ((r.nominals subject).map (·.toPhasedNP))) = r.suffixes := by
  decide

/-- Licensing reproduces the data whatever the specificity of the subject: a sentence is
grammatical exactly when some activation of the licensers is economical, so that a specific
object in the perfective crashes, and under every economical activation the subject carries the
suffix of the obligatory licenser and the object the L-suffix exactly when it is specific, the
secondary T having been activated for it. -/
theorem rows_agree : ∀ r ∈ rows, ∀ subject : Bool,
    (r.grammatical = true ↔ ∃ S, Economical domains r.clause (r.nominals subject) S) ∧
    ∀ S, Economical domains r.clause (r.nominals subject) S →
      suffixes (license domains (activate r.clause S)
        ((r.nominals subject).map (·.toPhasedNP))) = r.suffixes := by
  intro r hr subject
  obtain ⟨h₁, h₂⟩ := rows_agree_aux r hr subject
  exact ⟨h₁.trans exists_economical_iff.symm,
    fun S hS ↦ h₂ S (Finset.mem_powerset.2 hS.subset_toFinset) hS⟩

/-- The object agreement is differential marking: a specific object in the imperfective is
licensed by the secondary T, activated for it alone, (47), and a nonspecific object activates
nothing and goes unlicensed, (48). -/
theorem imperfective_object (subject : Bool) :
    Economical domains imperfective (transitive subject true) {tImpf} ∧
      (license domains (activate imperfective {tImpf})
        ((transitive subject true).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser aspImpf), some (.licenser tImpf)] ∧
    Economical domains imperfective (transitive subject false) ∅ ∧
      (license domains (activate imperfective ∅)
        ((transitive subject false).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser aspImpf), none] := by
  cases subject <;> decide

/-! ### The toy language of Section 3.1 -/

/-- Finite T, the obligatory licenser of the toy language. -/
def toyT : Licenser := { head := .T, kind := .obligatory }

/-- v, a secondary licenser probing its own domain. -/
def toyV : Licenser := { head := .v, domain := .v, kind := .secondary }

/-- The toy language's licensers. -/
def toy : List Licenser := [toyV, toyT]

/-- The toy language's phase domains, v's spelling out before C's. -/
def toyDomains : List Cat := [.v, .C]

/-- A transitive clause of the toy language, in which a nominal needs licensing exactly when
animate: the subject above v, the object in its domain. -/
def toyTransitive (subject object : Bool) : List LicensedNP :=
  [{ label := "subj", needsLicensing := subject },
   { label := "obj", phase := .v, needsLicensing := object }]

/-- An animate object activates v, which licenses it: T licenses the subject whatever its
animacy and never the object, so without v the derivation crashes, (24). -/
theorem toy_animate_object (subject : Bool) :
    ¬ Converges toyDomains (activate toy ∅) (toyTransitive subject true) ∧
    Economical toyDomains toy (toyTransitive subject true) {toyV} ∧
      (license toyDomains toy ((toyTransitive subject true).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser toyT), some (.licenser toyV)] := by
  cases subject <;> decide

/-- An inanimate object activates nothing and goes unlicensed and unmarked, (23). -/
theorem toy_inanimate_object (subject : Bool) :
    Economical toyDomains toy (toyTransitive subject false) ∅ ∧
      (license toyDomains (activate toy ∅)
        ((toyTransitive subject false).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser toyT), none] := by
  cases subject <;> decide

/-! ### Licensing against dependent case -/

/-- The perfective ban is an argument for licensing (Section 2.1.3): the dependent-case rules of
an accusative language value a specific perfective object accusative, but licensing leaves it
unvalued, and the derivation crashes whatever the specificity of the subject. -/
theorem dependentCase_values_banned_object (subject : Bool) :
    _root_.Case.getCaseOf "obj"
        (_root_.Case.assignCases .accusative ((transitive subject true).map (·.toNP))) =
      some .acc ∧
    ¬ Converges domains perfective (transitive subject true) := by
  cases subject <;> decide

end Kalin2018
