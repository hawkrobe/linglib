import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Minimalist.Verbal.Voice
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

A clause is the head licensing its object, its finiteness, verb phrase, extracted argument and,
for the Chuj contrast, whether an adverb separates the verb from its object; convergence asks
that the object and the intransitive subject be licensed, that an extracting subject not be
trapped, that a Case-checking Voice be a last resort and that a pseudo-incorporated object be
adjacent. Of the three factors the conclusion lists, the phasehood of the transitive verb
phrase is the Voice head's, while a subject generated inside it and a single escape hatch are
built into trapping as the paper assumes them. The substrate's single Voice head stands in for
the paper's pair of v, which carries phasehood and the status suffix, and Voice, which
introduces the agent: the regular transitive is agentive Voice, Agent Focus the agentive head
with Case checking and phasehood overridden off, the antipassive its own flavor. The last
resort is the paper's later formulation, that the marked Voice merges only where the object
would otherwise have no source of Case or trap the extracting subject, compared against the
derivation with regular Voice; that is definitional and not derived from a ranking. The
registered languages are the fragments' verbal complexes, from which the absolutive's position
is read, and rows carry the paper's high or low classification of their language, checked
against that reading; the absolutive on an intransitive subject needs finite Infl, and the
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

open Minimalist Minimalist.Voice Mayan Data.Examples

/-! ### Clauses -/

/-- The heads that assign structural Case (5). -/
inductive Licenser where
  | infl
  | v
  deriving DecidableEq, Repr

/-- The head licensing transitive objects, read off the absolutive's position (24): Infl when
the absolutive is high, so that it is nominative ([legate-2008]'s ABS=NOM), and v when it is
low, so that it is a default (ABS=DEF). -/
def Licenser.ofPosition : ABSPosition → Licenser
  | .high => .infl
  | .low => .v

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
def voiceAP : Head := antipassive

/-- The verb phrase of a clause: an intransitive with the marker series of its sole argument,
or a transitive with its Voice and its object. -/
inductive Predicate where
  | intransitive (marking : MarkerSet)
  | transitive (voice : Head) (object : Object)
  deriving DecidableEq

/-- A clause: the head licensing its object, finiteness, the verb phrase, the argument
extracted, and whether an adverb separates the verb from its object. -/
structure Clause where
  /-- The head licensing transitive objects. -/
  licenser : Licenser
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
Infl sits outside it, so a full DP object licensed by Infl must reach the edge (51), which the
EPP of high-abs eventive v keeps true under Agent Focus (66); an object licensed by v stays in
situ (52). -/
def Raises (p : Predicate) (l : Licenser) : Prop := p.object? = some .dp ∧ l = .infl

/-- The object's Case is available (27): Voice checks it, v assigns it, or finite Infl does; a
caseless or oblique object needs none. The low-abs non-finite cell takes the embedded clause
to contain v, which the paper's fn. 12 leaves open. -/
def ObjectLicensed (p : Predicate) (l : Licenser) (finite : Bool) : Prop :=
  p.object? = some .dp → p.ChecksCase ∨ l = .v ∨ finite = true

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
instance (p : Predicate) (l : Licenser) : Decidable (p.Raises l) := by
  unfold Raises; infer_instance
instance (p : Predicate) (l : Licenser) (b : Bool) : Decidable (p.ObjectLicensed l b) := by
  unfold ObjectLicensed; infer_instance
instance (p : Predicate) (b : Bool) : Decidable (p.SubjectLicensed b) := by
  unfold SubjectLicensed; infer_instance
instance (p : Predicate) (b : Bool) : Decidable (p.Adjacent b) := by
  unfold Adjacent; infer_instance

end Predicate

/-! ### Trapping (§3.2, (89)) -/

/-- The subject is trapped (53): the raised object takes the single escape hatch of the phasal
verb phrase, inside which the subject is generated, the three factors of (89). -/
def Trapped (c : Clause) : Prop := c.predicate.IsPhasal ∧ c.predicate.Raises c.licenser

instance (c : Clause) : Decidable (Trapped c) := by unfold Trapped; infer_instance

/-- A non-phasal verb phrase traps nothing: the antipassive and Agent Focus. -/
theorem not_trapped_of_not_phasal {c : Clause} (h : ¬ c.predicate.IsPhasal) : ¬ Trapped c :=
  fun ht ↦ h ht.1

/-- A verb phrase whose object does not raise traps nothing: caseless and oblique objects. -/
theorem not_trapped_of_not_raises {c : Clause} (h : ¬ c.predicate.Raises c.licenser) :
    ¬ Trapped c :=
  fun ht ↦ h ht.2

/-- Where v licenses the object nothing is trapped (52): the object never raises. -/
theorem not_trapped_of_v {c : Clause} (h : c.licenser = .v) : ¬ Trapped c :=
  not_trapped_of_not_raises fun hr ↦ by simp [Predicate.Raises, h] at hr

/-- Syntactic ergativity: the subject of a finite regular transitive with a full DP object is
trapped when extracted (21c). -/
def SyntacticallyErgative (l : Licenser) : Prop :=
  Trapped ⟨l, true, .transitive agentive .dp, some .A, false⟩

instance (l : Licenser) : Decidable (SyntacticallyErgative l) :=
  inferInstanceAs (Decidable (Trapped _))

/-- Tada's generalization derived (19), (24): a language bans subject extraction exactly when
Infl licenses the object. -/
theorem syntacticallyErgative_iff (l : Licenser) : SyntacticallyErgative l ↔ l = .infl := by
  cases l <;> decide

/-! ### Case configurations (3), (10) -/

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

/-- Table (10): syntactic ergativity entails morphological ergativity, since Infl licensing the
object leaves the subject to v. -/
theorem morphologicallyErgative_of_syntacticallyErgative (k : Configuration)
    (h : SyntacticallyErgative k.object) : k.MorphologicallyErgative := by
  rw [syntacticallyErgative_iff] at h
  cases hs : k.subject
  · exact absurd (k.infl_once hs) (by simp [h])
  · exact hs

/-- The converse fails (10): the default-absolutive configuration is morphologically but not
syntactically ergative. -/
theorem v_not_syntacticallyErgative :
    (⟨.v, .v, nofun⟩ : Configuration).MorphologicallyErgative ∧ ¬ SyntacticallyErgative .v :=
  ⟨rfl, by decide⟩

/-! ### Convergence: licensing, extraction and the last resort (§4, §5) -/

/-- The same clause under regular transitive Voice. -/
def Clause.regular (c : Clause) : Clause := { c with predicate := c.predicate.regular }

/-- The regular derivation crashes: its object is unlicensed, or its extracting subject is
trapped. -/
def RegularCrashes (c : Clause) : Prop :=
  ¬ c.regular.predicate.ObjectLicensed c.licenser c.finite ∨
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
  c.predicate.ObjectLicensed c.licenser c.finite ∧ c.predicate.SubjectLicensed c.finite ∧
    (c.extracted = some .A → ¬ Trapped c) ∧ LastResort c ∧ c.predicate.Adjacent c.separated

instance (c : Clause) : Decidable (Converges c) := by unfold Converges; infer_instance

/-- Non-finite licensing (27): a regular transitive object survives without Infl exactly where
v licenses it, and an absolutive intransitive subject only under finite Infl. -/
theorem nonfinite_licensing (l : Licenser) :
    ((Predicate.transitive agentive .dp).ObjectLicensed l false ↔ l = .v) ∧
      ¬ (Predicate.intransitive .setB).SubjectLicensed false := by
  cases l <;> decide

/-- Agent Focus in a high-abs language: it frees the extracting subject (67) and licenses the
object of a non-finite transitive (70), and the regular derivation crashes in both, so it is
a last resort in both; the same object under regular Voice is trapped or unlicensed. -/
theorem agent_focus :
    Converges ⟨.infl, true, .transitive voiceAF .dp, some .A, false⟩ ∧
    ¬ Converges ⟨.infl, true, .transitive agentive .dp, some .A, false⟩ ∧
    Converges ⟨.infl, false, .transitive voiceAF .dp, none, false⟩ ∧
    ¬ Converges ⟨.infl, false, .transitive agentive .dp, none, false⟩ := by
  decide

/-- The last resort bars Agent Focus where nothing crashes: in a finite clause without subject
extraction, in a low-abs language, and with a caseless object (75b), which instead lets the
subject extract from a regular transitive (75a). -/
theorem last_resort :
    ¬ Converges ⟨.infl, true, .transitive voiceAF .dp, none, false⟩ ∧
    ¬ Converges ⟨.v, true, .transitive voiceAF .dp, some .A, false⟩ ∧
    ¬ Converges ⟨.infl, true, .transitive voiceAF .caseless, some .A, false⟩ ∧
    Converges ⟨.infl, true, .transitive agentive .caseless, some .A, false⟩ := by
  decide

/-- The antipassive frees the subject (60), on either count: its verb phrase is intransitive,
and its oblique patient never raises to the edge. -/
theorem antipassive_frees (l : Licenser) :
    ¬ (Predicate.transitive voiceAP .oblique).IsPhasal ∧
      ¬ (Predicate.transitive voiceAP .oblique).Raises l ∧
        ¬ Trapped ⟨l, true, .transitive voiceAP .oblique, some .A, false⟩ := by
  cases l <;> decide

/-! ### The Mayan fragments (§2.1, §2.2) -/

/-- The Mayan languages with registered fragments. -/
inductive Language where
  | chol | qanjobal | kaqchikel | tseltal | tsotsil | mam | kiche | yukatek
  deriving DecidableEq, Repr, Fintype

namespace Language

/-- The Glottolog code of a language, the key the rows carry. -/
def glottocode : Language → String
  | .chol => "chol1282"
  | .qanjobal => "qanj1241"
  | .kaqchikel => "kaqc1270"
  | .tseltal => "tzel1254"
  | .tsotsil => "tzot1259"
  | .mam => "mamm1241"
  | .kiche => "kich1262"
  | .yukatek => "yuca1254"

/-- The verbal complex of a language, from its fragment. -/
def template : Language → Morphology.AffixTemplate VerbSlot
  | .chol => Chol.template
  | .qanjobal => Qanjobal.template
  | .kaqchikel => Kaqchikel.template
  | .tseltal => Tseltal.template
  | .tsotsil => Tsotsil.template
  | .mam => Mam.template
  | .kiche => Kiche.template
  | .yukatek => Yukatek.template

/-- The absolutive's position in a language, read off its verbal complex (16): high when Set B
precedes the stem. -/
def absPosition (L : Language) : ABSPosition := Mayan.absPosition L.template

/-- The Set B exponents of a language, from its fragment. -/
def setB : Language → ExponentTable
  | .chol => Chol.setBExponent
  | .qanjobal => Qanjobal.setBExponent
  | .kaqchikel => Kaqchikel.setBExponent
  | .tseltal => Tseltal.setBExponent
  | .tsotsil => Tsotsil.setBExponent
  | .mam => Mam.setBExponent
  | .kiche => Kiche.setBExponent
  | .yukatek => Yukatek.setBExponent

/-- Case assignment by aspect in a language, from its fragment. -/
def assignCase : Language → UD.Aspect → ArgumentRole → Case
  | .chol => Chol.assignCase
  | .qanjobal => Qanjobal.assignCase
  | .kaqchikel => Kaqchikel.assignCase
  | .tseltal => Tseltal.assignCase
  | .tsotsil => Tsotsil.assignCase
  | .mam => Mam.assignCase
  | .kiche => Kiche.assignCase
  | .yukatek => Yukatek.assignCase

/-- The language is ergatively aligned in the perfective (§2.1). -/
def IsErgativePerfective (L : Language) : Prop := Alignment.IsErgative (L.assignCase .Perf)

instance (L : Language) : Decidable L.IsErgativePerfective :=
  inferInstanceAs (Decidable (Alignment.IsErgative _))

/-- The fragment marks transitive-subject extraction on the verb; the Yukatek fragment records
no extraction reflexes. -/
def MarksSubjectExtraction : Language → Prop
  | .chol => (Chol.Extraction.realize .A).Nonempty
  | .qanjobal => ∃ p, (Qanjobal.Extraction.realize p .A).Nonempty
  | .kaqchikel => ∀ c, (Kaqchikel.Extraction.realize c (.core .A)).Nonempty
  | .tseltal => (Tseltal.Extraction.realize .A).Nonempty
  | .tsotsil => (Tsotsil.Extraction.realize .A).Nonempty
  | .mam => (Mam.Extraction.realize (.core .A)).Nonempty
  | .kiche => ∀ c, (Kiche.Extraction.realize c (.core .A)).Nonempty
  | .yukatek => False

instance : ∀ L : Language, Decidable L.MarksSubjectExtraction
  | .chol | .tseltal | .tsotsil | .mam => Finset.decidableNonempty
  | .qanjobal => Fintype.decidableExistsFintype
  | .kaqchikel | .kiche => Fintype.decidableForallFintype
  | .yukatek => inferInstanceAs (Decidable False)

end Language

/-- Every registered language but San Juan Atitán Mam, which is tripartite, assigns case
ergatively in the perfective (§2.1). -/
theorem isErgativePerfective_iff (L : Language) : L.IsErgativePerfective ↔ L ≠ .mam := by
  cases L <;> decide

/-- Third person singular absolutive is null in every registered language ergative in the
perfective (13); Mam's default Set B surfaces there. -/
theorem thirdSgZero_of_isErgativePerfective {L : Language} (h : L.IsErgativePerfective) :
    L.setB.IsThirdSgZero := by
  cases L <;> first | decide | exact absurd h (by decide)

/-- Tada's generalization over the fragments (19): a registered language marks subject
extraction exactly when its absolutive is high, as the trapping derivation predicts. Table
(19) omits Tsotsil, whose two absolutive series resist the classification (fn. 8), and lists
Yucatec as an outlier whose Agent Focus fn. 9 reanalyses; the Yukatek fragment records no
extraction reflexes, so both stay outside the theorem. -/
theorem tada (L : Language) (h₁ : L ≠ .tsotsil) (h₂ : L ≠ .yukatek) :
    L.MarksSubjectExtraction ↔ SyntacticallyErgative (.ofPosition L.absPosition) := by
  cases L <;> first | exact (h₁ rfl).elim | exact (h₂ rfl).elim | decide

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

/-- The clause a row describes, its object's licenser read off the paper's classification of
its language. -/
def Clause.ofRow (row : LinguisticExample) : Option Clause := do
  let pos ← row.parse? "absPosition" absPositions
  let finite ← row.parse? "finite" [("yes", true), ("no", false)]
  let predicate ← Predicate.ofRow row
  return ⟨.ofPosition pos, finite, predicate,
    row.parse? "extracted" [("S", ArgumentRole.S), ("A", .A), ("P", .P)],
    decide (row.feature? "separated" = some "yes")⟩

/-- Every analysed example is grammatical exactly when its clause converges. -/
theorem analysed_rows : ∀ row ∈ Examples.all, (row.feature? "predicate").isSome = true →
    ∃ c ∈ Clause.ofRow row, (row.judgment = .acceptable ↔ Converges c) := by
  decide

/-- The rows' classification of a registered language agrees with its verbal complex. -/
theorem rows_match_fragments : ∀ row ∈ Examples.all, ∀ L : Language,
    L.glottocode = row.language →
      row.parse? "absPosition" absPositions = some L.absPosition := by
  decide

end CoonMateoPedroPreminger2014
