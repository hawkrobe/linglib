import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Extraction
import Linglib.Fragments.Mayan.Qanjobal.Agreement
import Linglib.Fragments.Mayan.Qanjobal.Extraction
import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Extraction
import Linglib.Fragments.Mayan.Tseltal.Agreement
import Linglib.Fragments.Mayan.Tsotsil.Agreement
import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Mam.Extraction
import Linglib.Fragments.Mayan.Kiche.Agreement
import Linglib.Fragments.Mayan.Kiche.Extraction
import Linglib.Fragments.Mayan.Yukatek.Agreement
import Linglib.Data.Examples.CoonMateoPedroPreminger2014

/-!
# Coon, Mateo Pedro and Preminger 2014: case and extraction asymmetries in Mayan

[coon-mateo-pedro-preminger-2014] argue that the ban on extracting transitive subjects in some
morphologically ergative languages, syntactic ergativity, is not a property of the ergative
subject but a locality problem in licensing the object. Following Legate and Aldridge, every
ergative language licenses the transitive subject from v, but the object is licensed either by
Infl, so that absolutive is nominative, or by v, so that it is a default, and in Mayan the two
settings are read off the position of the absolutive morpheme: high, on the aspect marker, or
low, on the verb stem. Since Infl sits outside the phasal transitive verb phrase, an object it
licenses must raise through the phrase's single escape hatch and so traps the subject generated
below it, while an object licensed by v stays put and the subject is free, which derives Tada's
generalization that high-absolutive languages extract subjects only through a special
construction, and predicts that absolutive objects survive in non-finite clauses of low- but
not high-absolutive languages. The Q'anjob'al Agent Focus suffix -on is a marked Voice that
licenses the object itself, so that v is intransitive, non-phasal and marked with the
intransitive status suffix, and the same suffix licenses the object of a non-finite embedded
transitive, the Crazy Antipassive; both are a last resort, so in a finite extraction clause
Agent Focus fails with reflexive, extended reflexive and bare objects, which are
pseudo-incorporated and need no Case, while those very objects let the subject extract from a
regular transitive.

## Implementation notes

A clause is its case locus, finiteness, verb phrase, extracted argument and, for the Chuj
contrast, whether an adverb separates the verb from its object; convergence asks that the
object and the intransitive subject be licensed, that an extracting subject not be trapped,
that a Case-checking Voice be a last resort and that a pseudo-incorporated object be adjacent.
Of the three factors the conclusion lists, the phasehood of the transitive verb phrase is the
Voice head's, while a subject generated inside it and a single escape hatch are built into
trapping as the paper assumes them. The substrate's single Voice head stands in for the
paper's pair of v, which carries phasehood and the status suffix, and Voice, which introduces
the agent: the regular transitive is agentive Voice, Agent Focus the agentive head with Case
checking and phasehood overridden off, the antipassive its own flavor. The last resort is the
paper's later formulation, that the marked Voice merges only where the object would otherwise
have no source of Case or trap the extracting subject, compared against the derivation with
regular Voice; that is definitional and not derived from a ranking. Rows carry the paper's
high or low classification of their language, checked against the fragments' value where the
language is registered; the absolutive on an intransitive subject needs finite Infl, and the
ergative on one is left to the nominalized non-finite clause without a model of
nominalization. Kaqchikel Agent Focus, the nominal-stem and passive strategies for non-finite
transitives, and the constructions of the section on other extractions from the verb phrase
are recorded as data without a configuration.

## TODO

- The person restriction on Agent Focus (72) is not modelled; a focused 1st person agent is
  recorded as a regular transitive without extraction, the paper's tentative suggestion.
- Agent Focus with reflexive objects in non-finite clauses, which the paper's fn. 31 records
  and leaves unexplained, does not converge here either.
- The extraction of low adverbs and the instrumental voice (§5.3) are not modelled.

## References

* [J. Coon, P. Mateo Pedro and O. Preminger, *The role of Case in A-bar extraction
  asymmetries: Evidence from Mayan* (2014)][coon-mateo-pedro-preminger-2014]
* [J. A. Legate, *Morphological and abstract Case* (2008)][legate-2008]
* [E. Aldridge, *Ergativity and word order in Austronesian languages* (2004)][aldridge-2004]
* [H. Tada, *A/A-bar partition in derivation* (1993)][tada-1993]
* [F. Ordóñez, *The antipassive in Jacaltec: A last resort strategy* (1995)][ordonez-1995]
* [B. Stiebels, *Agent focus in Mayan languages* (2006)][stiebels-2006]
* [H. Harley, *External arguments and the Mirror Principle* (2013)][harley-2013]
* [D. Massam, *Pseudo noun incorporation in Niuean* (2001)][massam-2001]
* [T. W. Larsen and W. M. Norman, *Correlates of ergativity in Mayan grammar*
  (1979)][larsen-norman-1979]
* [J. Aissen, *On the syntax of agent focus in K'ichee'* (2011)][aissen-2011]
* [Y. Imanishi, *Default ergative* (2014)][imanishi-2014]
* [L. Hou, *Agent focus in Chuj reflexive constructions* (2013)][hou-2013]
* [N. Chomsky, *Derivation by phase* (2001)][chomsky-2001]
-/

namespace CoonMateoPedroPreminger2014

open Minimalist Minimalist.Voice Mayan Extraction Data.Examples

/-! ### Clauses -/

/-- What a transitive verb takes as its object. -/
inductive Object where
  /-- A full DP: it needs structural Case and satisfies the EPP of v. -/
  | dp
  /-- A reflexive, extended reflexive or bare NP: pseudo-incorporated, needing neither (§5.2). -/
  | caseless
  /-- An object licensed inside its own oblique phrase: the demoted patient of an antipassive
  (59) or the relational-noun complement of a Mam infinitive (39a). -/
  | oblique
  deriving DecidableEq, Repr

/-- Agent Focus as the marked Voice (66): agentive Voice that also assigns structural Case to
the object, so no ergative is assigned, v is intransitive and non-phasal, and the status suffix
is *-i*. -/
def voiceAF : Head := { agentive with phaseOverride := some false, checksCase := true }

/-- The antipassive Voice (59): the patient is oblique and v intransitive. -/
def voiceAP : Head := { flavor := .antipassive, hasD := true }

/-- The verb phrase of a clause: an intransitive with the marker series of its sole argument,
or a transitive with its Voice and its object. -/
inductive Predicate where
  | intransitive (marking : MarkerSet)
  | transitive (voice : Head) (object : Object)
  deriving DecidableEq

/-- A clause: the locus of the object's Case, finiteness, the verb phrase, the argument
extracted, and whether an adverb separates the verb from its object. -/
structure Clause where
  /-- Which head licenses transitive objects, read off the absolutive's position (24). -/
  locus : CaseLocus
  /-- Whether the clause has finite Infl, the preverbal aspect marker. -/
  finite : Bool
  /-- The verb phrase. -/
  predicate : Predicate
  /-- The argument A-bar extracted, if any. -/
  extracted : Option ArgumentRole := none
  /-- Whether adverbial material separates the verb from its object (81). -/
  separated : Bool := false
  deriving DecidableEq

namespace Predicate

/-- The Voice head of a transitive verb phrase. -/
def voice? : Predicate → Option Head
  | .transitive v _ => some v
  | .intransitive _ => none

/-- The object of a transitive verb phrase. -/
def object? : Predicate → Option Object
  | .transitive _ o => some o
  | .intransitive _ => none

/-- The marker series of an intransitive subject. -/
def marking? : Predicate → Option MarkerSet
  | .intransitive m => some m
  | .transitive _ _ => none

/-- The same verb phrase under regular transitive Voice, the derivation Agent Focus competes
with. -/
def regular : Predicate → Predicate
  | .transitive _ o => .transitive agentive o
  | p => p

/-- The verb phrase is phasal: its Voice head is, standing in for the transitive v whose
phasehood covaries with its ergative assignment and status suffix (55). -/
def IsPhasal (p : Predicate) : Prop := ∃ v ∈ p.voice?, v.IsPhasal

/-- The Voice checks the object's Case: Agent Focus. -/
def ChecksCase (p : Predicate) : Prop := ∃ v ∈ p.voice?, v.ChecksCase

/-- The object raises to the edge of the verb phrase: Case is assigned within the phase and
Infl sits outside it, so a full DP object of a high-abs clause must reach the edge (51), which
the EPP of high-abs eventive v keeps true under Agent Focus (66); a low-abs object stays in
situ (52). -/
def Raises (p : Predicate) (locus : CaseLocus) : Prop := p.object? = some .dp ∧ locus = .absNom

/-- The object's Case is available (27): Voice checks it, v assigns it, or finite Infl does; a
caseless or oblique object needs none. The low-abs non-finite cell takes the embedded clause
to contain v, which the paper's fn. 12 leaves open. -/
def ObjectLicensed (p : Predicate) (locus : CaseLocus) (finite : Bool) : Prop :=
  p.object? = some .dp → p.ChecksCase ∨ locus = .absDef ∨ finite = true

/-- The absolutive on an intransitive subject needs finite Infl ((32), (33)); the
ergative/possessive marking of a non-finite one is the nominalization's. -/
def SubjectLicensed (p : Predicate) (finite : Bool) : Prop :=
  p.marking? = some .setB → finite = true

/-- A pseudo-incorporated object stays adjacent to the verb, the Chuj contrast (81); the paper's
fn. 28 notes that the word-order reflex does not hold of Q'anjob'al extended reflexives. -/
def Adjacent (p : Predicate) (separated : Bool) : Prop :=
  p.object? = some .caseless → separated = false

instance (p : Predicate) : Decidable p.IsPhasal := by unfold IsPhasal; infer_instance
instance (p : Predicate) : Decidable p.ChecksCase := by unfold ChecksCase; infer_instance
instance (p : Predicate) (l : CaseLocus) : Decidable (p.Raises l) := by
  unfold Raises; infer_instance
instance (p : Predicate) (l : CaseLocus) (b : Bool) : Decidable (p.ObjectLicensed l b) := by
  unfold ObjectLicensed; infer_instance
instance (p : Predicate) (b : Bool) : Decidable (p.SubjectLicensed b) := by
  unfold SubjectLicensed; infer_instance
instance (p : Predicate) (b : Bool) : Decidable (p.Adjacent b) := by
  unfold Adjacent; infer_instance

end Predicate

/-! ### Trapping (§3.2, (89)) -/

/-- The subject is trapped (53): the raised object takes the single escape hatch of the phasal
verb phrase, inside which the subject is generated, the three factors of (89). -/
def Trapped (c : Clause) : Prop := c.predicate.IsPhasal ∧ c.predicate.Raises c.locus

instance (c : Clause) : Decidable (Trapped c) := by unfold Trapped; infer_instance

/-- A non-phasal verb phrase traps nothing: the antipassive and Agent Focus. -/
theorem not_trapped_of_not_phasal {c : Clause} (h : ¬ c.predicate.IsPhasal) : ¬ Trapped c :=
  λ ht => h ht.1

/-- A verb phrase whose object does not raise traps nothing: caseless and oblique objects. -/
theorem not_trapped_of_not_raises {c : Clause} (h : ¬ c.predicate.Raises c.locus) :
    ¬ Trapped c :=
  λ ht => h ht.2

/-- In a low-abs language nothing is trapped (52): the object never raises. -/
theorem not_trapped_of_absDef {c : Clause} (h : c.locus = .absDef) : ¬ Trapped c :=
  not_trapped_of_not_raises λ hr => by simp [Predicate.Raises, h] at hr

/-- Syntactic ergativity: the subject of a finite regular transitive with a full DP object is
trapped when extracted (21c). -/
def SyntacticallyErgative (locus : CaseLocus) : Prop :=
  Trapped ⟨locus, true, .transitive agentive .dp, some .A, false⟩

instance (locus : CaseLocus) : Decidable (SyntacticallyErgative locus) :=
  inferInstanceAs (Decidable (Trapped _))

/-- Tada's generalization derived (19), (24): a language bans subject extraction exactly when
Infl licenses the object. -/
theorem syntacticallyErgative_iff (locus : CaseLocus) :
    SyntacticallyErgative locus ↔ locus = .absNom := by
  cases locus <;> decide

/-! ### Case configurations (their (3), (10)) -/

/-- The heads that assign structural Case (5). -/
inductive Licenser where
  | infl
  | v
  deriving DecidableEq, Repr

/-- A clausal Case configuration (3): the licenser of the transitive subject and of the
object, where Infl licenses at most one of them. -/
structure Configuration where
  /-- The head licensing the transitive subject. -/
  subject : Licenser
  /-- The head licensing the transitive object. -/
  object : Licenser
  /-- Infl licenses at most one argument. -/
  infl_once : subject = .infl → object = .v

/-- Morphological ergativity: v licenses the transitive subject. -/
def Configuration.MorphologicallyErgative (k : Configuration) : Prop := k.subject = .v

/-- The object's Case locus, by the head licensing the object. -/
def Licenser.locus : Licenser → CaseLocus
  | .infl => .absNom
  | .v => .absDef

/-- Table (10): syntactic ergativity entails morphological ergativity, since Infl licensing the
object leaves the subject to v. -/
theorem morphologicallyErgative_of_syntacticallyErgative (k : Configuration)
    (h : SyntacticallyErgative k.object.locus) : k.MorphologicallyErgative := by
  rw [syntacticallyErgative_iff] at h
  cases hs : k.subject
  · simp [k.infl_once hs, Licenser.locus] at h
  · exact hs

/-- The converse fails (10): the default-absolutive configuration is morphologically but not
syntactically ergative. -/
theorem absDef_not_syntacticallyErgative :
    (⟨.v, .v, nofun⟩ : Configuration).MorphologicallyErgative ∧
      ¬ SyntacticallyErgative Licenser.v.locus :=
  ⟨rfl, by decide⟩

/-! ### Convergence: licensing, extraction and the last resort (§4, §5) -/

/-- The same clause under regular transitive Voice. -/
def Clause.regular (c : Clause) : Clause := { c with predicate := c.predicate.regular }

/-- The regular derivation crashes: its object is unlicensed, or its extracting subject is
trapped. -/
def RegularCrashes (c : Clause) : Prop :=
  ¬ c.regular.predicate.ObjectLicensed c.locus c.finite ∨
    (c.extracted = some .A ∧ Trapped c.regular)

instance (c : Clause) : Decidable (RegularCrashes c) := by unfold RegularCrashes; infer_instance

/-- Agent Focus is a last resort ([ordonez-1995]; §4.2, §5.1): the Case-checking Voice merges
only where the object would otherwise lack a source of Case or trap the extracting subject. -/
def LastResort (c : Clause) : Prop := c.predicate.ChecksCase → RegularCrashes c

instance (c : Clause) : Decidable (LastResort c) := inferInstanceAs (Decidable (_ → _))

/-- A clause converges: its object and intransitive subject are licensed, an extracted subject
is not trapped, a Case-checking Voice is a last resort, and a pseudo-incorporated object is
adjacent to the verb. -/
def Converges (c : Clause) : Prop :=
  c.predicate.ObjectLicensed c.locus c.finite ∧ c.predicate.SubjectLicensed c.finite ∧
    (c.extracted = some .A → ¬ Trapped c) ∧ LastResort c ∧ c.predicate.Adjacent c.separated

instance (c : Clause) : Decidable (Converges c) := by unfold Converges; infer_instance

/-- Non-finite licensing (27): a regular transitive object survives without Infl exactly in a
low-abs language, and an absolutive intransitive subject only under finite Infl. -/
theorem nonfinite_licensing (locus : CaseLocus) :
    ((Predicate.transitive agentive .dp).ObjectLicensed locus false ↔ locus = .absDef) ∧
      ¬ (Predicate.intransitive .setB).SubjectLicensed false := by
  cases locus <;> decide

/-- Agent Focus in a high-abs language: it frees the extracting subject (67) and licenses the
object of a non-finite transitive (70), and the regular derivation crashes in both, so it is
a last resort in both; the same object under regular Voice is trapped or unlicensed. -/
theorem agent_focus :
    Converges ⟨.absNom, true, .transitive voiceAF .dp, some .A, false⟩ ∧
    ¬ Converges ⟨.absNom, true, .transitive agentive .dp, some .A, false⟩ ∧
    Converges ⟨.absNom, false, .transitive voiceAF .dp, none, false⟩ ∧
    ¬ Converges ⟨.absNom, false, .transitive agentive .dp, none, false⟩ := by
  decide

/-- The last resort bars Agent Focus where nothing crashes: in a finite clause without subject
extraction, in a low-abs language, and with a caseless object (75b), which instead lets the
subject extract from a regular transitive (75a). -/
theorem last_resort :
    ¬ Converges ⟨.absNom, true, .transitive voiceAF .dp, none, false⟩ ∧
    ¬ Converges ⟨.absDef, true, .transitive voiceAF .dp, some .A, false⟩ ∧
    ¬ Converges ⟨.absNom, true, .transitive voiceAF .caseless, some .A, false⟩ ∧
    Converges ⟨.absNom, true, .transitive agentive .caseless, some .A, false⟩ := by
  decide

/-- The antipassive frees the subject (60), on either count: its verb phrase is intransitive,
and its oblique patient never raises to the edge. -/
theorem antipassive_frees (locus : CaseLocus) :
    ¬ (Predicate.transitive voiceAP .oblique).IsPhasal ∧
      ¬ (Predicate.transitive voiceAP .oblique).Raises locus ∧
        ¬ Trapped ⟨locus, true, .transitive voiceAP .oblique, some .A, false⟩ := by
  cases locus <;> decide

/-! ### The Mayan fragments (§2.1, §2.2) -/

/-- The absolutive's position in each registered language, routed to its fragment. -/
def absPositionOf : Mayan → ABSPosition
  | .Chol => Chol.absPosition
  | .Qanjobal => Qanjobal.absPosition
  | .Kaqchikel => Kaqchikel.absPosition
  | .Tseltal => Tseltal.absPosition
  | .Tsotsil => Tsotsil.absPosition
  | .Mam => Mam.absPosition
  | .Kiche => Kiche.absPosition
  | .Yukatek => Yukatek.absPosition

/-- The fragments' classification agrees with the verb template (16): high iff Set B precedes
the stem. -/
theorem absPosition_matches_template (lang : Mayan) :
    absPositionOf lang = templateABSPosition lang := by
  cases lang <;> rfl

/-- Whether a registered fragment marks transitive-subject extraction on the verb; the Yukatek
fragment records no extraction reflexes. -/
def MarksSubjectExtraction : Mayan → Prop
  | .Chol => Marked Chol.Extraction.realize .subject
  | .Qanjobal => Marked Qanjobal.Extraction.realize .subject
  | .Kaqchikel => Marked Kaqchikel.Extraction.realize .subject
  | .Tseltal => Marked Tseltal.Extraction.realize .subject
  | .Tsotsil => Marked Tsotsil.Extraction.realize .subject
  | .Mam => Marked Mam.Extraction.realize .subject
  | .Kiche => Marked Kiche.Extraction.realize .subject
  | .Yukatek => False

instance : ∀ lang : Mayan, Decidable (MarksSubjectExtraction lang)
  | .Chol | .Qanjobal | .Kaqchikel | .Tseltal | .Tsotsil | .Mam | .Kiche =>
      inferInstanceAs (Decidable (Marked _ _))
  | .Yukatek => inferInstanceAs (Decidable False)

/-- Tada's generalization over the fragments (19): a registered language marks subject
extraction exactly when its absolutive is high, as the trapping derivation predicts. Table
(19) omits Tsotsil, whose two absolutive series resist the classification (fn. 8), and lists
Yucatec as an outlier whose Agent Focus fn. 9 reanalyses; the Yukatek fragment records no
extraction reflexes, so both stay outside the theorem. -/
theorem mayan_tada : ∀ lang ∈ Mayan.all, lang ≠ .Tsotsil → lang ≠ .Yukatek →
    (MarksSubjectExtraction lang ↔ SyntacticallyErgative (toCaseLocus (absPositionOf lang))) := by
  decide

/-- Set B exponents in each registered language, routed to its fragment. -/
def setBExponentOf : Mayan → ExponentTable
  | .Chol => Chol.setBExponent
  | .Qanjobal => Qanjobal.setBExponent
  | .Kaqchikel => Kaqchikel.setBExponent
  | .Tseltal => Tseltal.setBExponent
  | .Tsotsil => Tsotsil.setBExponent
  | .Mam => Mam.setBExponent
  | .Kiche => Kiche.setBExponent
  | .Yukatek => Yukatek.setBExponent

/-- Every registered language with the standard ergative-absolutive base assigns case
ergatively in the perfective (§2.1); San Juan Atitán Mam, tripartite, is the exception
recorded at `Mayan.isStandard`. -/
theorem mayan_perfective_ergative (lang : Mayan) (h : lang.isStandard = true) (r : ArgumentRole) :
    caseAt lang .Perf r = Alignment.ergative.assignCase r := by
  cases lang <;> first | rfl | nomatch h

/-- Third person singular absolutive is null across the standard branches (13); Mam's default
Set B surfaces there. -/
theorem mayan_p3sg_abs_null (lang : Mayan) (h : lang.isStandard = true) :
    (setBExponentOf lang).IsThirdSgZero := by
  cases lang <;> first | decide | nomatch h

/-! ### The paper's examples -/

private def absPositions : List (String × ABSPosition) := [("high", .high), ("low", .low)]

private def objects : List (String × Object) :=
  [("dp", .dp), ("caseless", .caseless), ("oblique", .oblique)]

/-- The verb phrase a row describes. -/
private def Predicate.ofRow (row : LinguisticExample) : Option Predicate := do
  match ← row.feature? "predicate" with
  | "intransitive" =>
      Predicate.intransitive <$> row.parse? "marking" [("abs", MarkerSet.setB), ("erg", .setA)]
  | "transitive" => Predicate.transitive agentive <$> row.parse? "object" objects
  | "agentFocus" => Predicate.transitive voiceAF <$> row.parse? "object" objects
  | "antipassive" => Predicate.transitive voiceAP <$> row.parse? "object" objects
  | _ => none

/-- The clause a row describes, its locus read off the paper's classification of its
language. -/
def Clause.ofRow (row : LinguisticExample) : Option Clause := do
  let pos ← row.parse? "absPosition" absPositions
  let finite ← row.parse? "finite" [("yes", true), ("no", false)]
  let predicate ← Predicate.ofRow row
  return ⟨toCaseLocus pos, finite, predicate,
    row.parse? "extracted" [("S", ArgumentRole.S), ("A", .A), ("P", .P)],
    decide (row.feature? "separated" = some "yes")⟩

/-- Every analysed example is grammatical exactly when its clause converges. -/
theorem analysed_rows : ∀ row ∈ Examples.all, (row.feature? "predicate").isSome = true →
    ∃ c ∈ Clause.ofRow row, (row.judgment = .acceptable ↔ Converges c) := by
  decide

/-- The rows' classification of a registered language agrees with its fragment. -/
theorem rows_match_fragments : ∀ row ∈ Examples.all, ∀ lang ∈ Mayan.all,
    lang.glottocode = row.language →
      row.parse? "absPosition" absPositions = some (absPositionOf lang) := by
  decide

end CoonMateoPedroPreminger2014
