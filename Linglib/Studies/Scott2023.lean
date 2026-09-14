import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Morphology.DistributedMorphology.Impoverishment
import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Data.Examples.Scott2023

/-!
# Scott (2023): Pronouns and Agreement in San Juan Atitán Mam

This file formalizes the dissertation's account of agreement and pronoun form in San Juan
Atitán Mam. Agreement is copying under the interaction and satisfaction theory of Agree (54): a
probe copies the features of its interaction condition from the first goal that satisfies it. The
probe on Infl (73) interacts with author and number and is satisfied by φ or by transitive Voice
(`inflProbe`), so in a transitive clause it halts at transitive Voice before reaching either
argument and copies nothing (`inflProbe_transitive`), while in an intransitive clause it reaches
the subject (`inflProbe_intransitive`); the agreeing-object grammar of standard Mam differs in the
one disjunct (`standardInflProbe_transitive`). Which head agrees with which argument is read off
the probes (`agreedBy`).

Vocabulary Insertion realizes the copied features by the Extended Subset Principle (53) over the
Vocabulary of Tables 4.7, 4.8 and 4.10 and of (59), (65) and (66) (`vocabulary`), which derives
the Fragment's Set A and Set B paradigms (`setA_realize`, `setB_realize`) and the default Set B
of a transitive clause, where Infl carries no φ (`setB_transitive`). A pronoun hosts every item
its features license, so first-person pronouns are bimorphemic (§4.4.1, `insertAll`). A probe
that copies a goal's features flags the goal with its category (§4.4.3.2, `Feat.flag`), and the
impoverishment rule (84) deletes number from a flagged first-person pronoun (`rule84`), bleeding
the bases *qin* and *qo*: the reduced subject and possessor series and the full independent series
of Table 4.25 are both derived from one Vocabulary (`form_flagged`, `form_unflagged`), and the
optional rule (93) reduces second-person plural in Set A contexts alone (`form_rule93`). The
dissertation's judgments (`Data/Examples/Scott2023`) instantiate the derivation
(`pronoun_rows`).

## Implementation notes

* Features are Harbour's bivalent person and number features (Table 4.4) with the head a Set A
  or Set B terminal sits on and the flag a copying probe leaves; the Fragment's `Mam.ScottFeatures`
  supplies the cells. Contextual specifications of Vocabulary Items are features of the same
  terminal, so the Extended Subset Principle is the substrate's `subsetPrinciple` over sites.
* Multiple insertion (§4.4.1) is read with the Extended Subset Principle: every applicable item
  is inserted unless a more specific applicable item realizes what it realizes, which is what
  keeps the generic plural *qa* out of the second-person plural *q=i*.
* The object is licensed by Voice under pure satisfaction (§4.4.4.1), a probe that copies
  nothing and so flags nothing; only the φ-copying probes are modeled, so the object is unflagged.
* Search domains are the clause spines of (56), (60) and (64): in a transitive clause Infl
  encounters transitive Voice first, then the object, which has moved above the subject (§3.4.1).
* The default Set A of super-extended ergative clauses (§2.6.3, §3.4.3.3) is data here; the
  dissertation leaves its derivation open.

## References

* [scott-2023]
* [deal-2024]
* [harbour-2016]
* [noyer-1992]
-/

open Mam DistributedMorphology Minimalist Morphology Data.Examples

namespace Scott2023

/-! ### Features and Vocabulary -/

/-- The loci of agreement: Infl, the Set B locus, and v/n, Voice or Poss, the Set A locus
(Tables 4.7, 4.8). -/
inductive Locus
  | infl | vn
  deriving DecidableEq, Repr

/-- A feature of a terminal: Harbour's bivalent person and number features (Table 4.4), the
locus a Set A or Set B terminal sits on, and the flag a probe leaves on a goal whose features it
has copied (§4.4.3.2, Table 4.26). -/
inductive Feat
  | author (b : Bool)
  | participant (b : Bool)
  | singular (b : Bool)
  | head (l : Locus)
  | flag (l : Locus)
  deriving DecidableEq, Repr

/-- The features of a pronoun in a paradigm cell (Table 4.4). -/
def cellFeats (c : PronCell) : List Feat :=
  [.author c.features.author, .participant c.features.participant, .singular c.features.singular]

/-- A Vocabulary Item as the dissertation writes them: the features it realizes, its contextual
specification, and its exponent. -/
structure Item where
  realized : List Feat
  context : List Feat := []
  exponent : Morph
  deriving DecidableEq, Repr

/-- Everything an item requires of its terminal. -/
def Item.site (i : Item) : List Feat := i.realized ++ i.context

/-- The item for the substrate's Subset Principle: its site and exponent. -/
def Item.toVI (i : Item) : VocabularyItem Feat Morph := ⟨↑i.site, i.exponent⟩

/-- The Vocabulary: Set A (Table 4.7), Set B with its context-free first-person plural and its
Elsewhere item (Table 4.8), the pronominal base *qin* (Table 4.10), the plurals *q* and *qa*
((65), (66)), and the disagreement enclitic at its two disagreeing values (59), listed last as
the items are linearized in Vocabulary order. -/
def vocabulary : List Item :=
  [ ⟨[.author true, .singular true], [.head .vn], .pref "n"⟩,
    ⟨[.author false, .singular true], [.head .vn], .pref "t"⟩,
    ⟨[.author true, .singular false], [.head .vn], .pref "q"⟩,
    ⟨[.author false, .singular false], [.head .vn], .pref "ky"⟩,
    ⟨[.author true, .singular true], [.head .infl], .free "chin"⟩,
    ⟨[], [.head .infl], .procl "tz'"⟩,
    ⟨[.author true, .singular false], [], .free "qo"⟩,
    ⟨[.author false, .singular false], [.head .infl], .free "chi"⟩,
    ⟨[.author true, .singular true], [], .free "qin"⟩,
    ⟨[.singular false], [.author false, .participant true], .free "q"⟩,
    ⟨[.singular false], [], .free "qa"⟩,
    ⟨[.author true, .participant false], [], .encl "i"⟩,
    ⟨[.author false, .participant true], [], .encl "i"⟩ ]

/-- Single insertion at an agreement terminal: the Extended Subset Principle (53), the most
specific applicable item. -/
def insert1 (t : List Feat) : Option Morph := subsetPrinciple (vocabulary.map Item.toVI) t

/-- Multiple insertion at a pronoun (§4.4.1): every applicable item, unless a more specific
applicable item realizes what it realizes. -/
def insertAll (t : List Feat) : List Morph :=
  let app := vocabulary.filter λ i => i.site.all (· ∈ t)
  (app.filter λ i => !app.any λ j =>
      j != i && i.realized.all (· ∈ j.realized) && i.site.all (· ∈ j.site)).map Item.exponent

/-! ### Agreement (§3.4.2, §4.4.2) -/

/-- What a probe meets on its search: an argument bearing φ, or the transitive Voice head. -/
structure Encounter where
  role : Option ArgumentRole
  phi : Bool
  voiceTR : Bool
  deriving DecidableEq, Repr

/-- The transitive Voice head. -/
def voiceTR : Encounter := ⟨none, false, true⟩

/-- An argument bearing φ. -/
def dp (r : ArgumentRole) : Encounter := ⟨some r, true, false⟩

/-- The probe on Infl (73): it interacts with φ and is satisfied by φ or by transitive Voice, so
either halts it, and it agrees with a goal only if the goal bears φ. -/
def inflProbe : Probe Encounter := { vis := λ e => e.phi || e.voiceTR, act := λ e => e.phi }

/-- The probe on Infl of the agreeing-object grammar (56), satisfied by φ alone. -/
def standardInflProbe : Probe Encounter := Probe.ofVis (·.phi)

/-- The probe on Voice or Poss, satisfied by the φ of its specifier. -/
def vnProbe : Probe Encounter := Probe.ofVis (·.phi)

/-- Infl's search domain in the clause of an argument (60), (64): transitive Voice, then the
object, which has moved above the subject, then the subject; or the intransitive subject. -/
def inflDomain : ArgumentRole → List Encounter
  | .A | .P => [voiceTR, dp .P, dp .A]
  | .S => [dp .S]
  | .R | .T => []

/-- Voice's or Poss's search domain: its specifier, the transitive subject. -/
def vnDomain : ArgumentRole → List Encounter
  | .A => [dp .A]
  | _ => []

/-- In a transitive clause Infl's probe halts at transitive Voice and agrees with nothing,
whatever lies below (60), (61). -/
theorem inflProbe_transitive (rest : List Encounter) :
    inflProbe.agree (voiceTR :: rest) = none := rfl

/-- In an intransitive clause Infl's probe agrees with the subject (64). -/
theorem inflProbe_intransitive : inflProbe.agree [dp .S] = some (dp .S) := rfl

/-- Under the agreeing-object grammar Infl's probe passes transitive Voice and agrees with the
object (56), (57). -/
theorem standardInflProbe_transitive (rest : List Encounter) :
    standardInflProbe.agree (voiceTR :: dp .P :: rest) = some (dp .P) := rfl

/-- The locus of the probe that copies an argument's features: Infl for the intransitive
subject, Voice or Poss for the transitive subject, none for the object. -/
def agreedBy (r : ArgumentRole) : Option Locus :=
  if (inflProbe.agree (inflDomain r)).bind (·.role) = some r then some .infl
  else if (vnProbe.agree (vnDomain r)).bind (·.role) = some r then some .vn
  else none

theorem agreedBy_S : agreedBy .S = some .infl := rfl
theorem agreedBy_A : agreedBy .A = some .vn := rfl
theorem agreedBy_P : agreedBy .P = none := rfl

/-- The features a probe copies (73a): author and number. -/
def copied (c : PronCell) : List Feat := [.author c.features.author, .singular c.features.singular]

/-- The Set B terminal on Infl in the clause of an argument in a cell: the copied features if
Infl agreed with the argument, at the Infl locus. -/
def inflTerminal (r : ArgumentRole) (c : PronCell) : List Feat :=
  (if agreedBy r = some .infl then copied c else []) ++ [.head .infl]

/-- The Set A terminal on Voice or Poss agreeing with a cell. -/
def vnTerminal (c : PronCell) : List Feat := copied c ++ [.head .vn]

/-- The Fragment's Set B paradigm (Table 4.6) is the Vocabulary's spell-out of what Infl copies
from an intransitive subject; 2SG and 3SG fall to the Elsewhere item. -/
theorem setB_realize (c : PronCell) :
    setBExponent.realize (.pn c.person c.number) = (insert1 (inflTerminal .S c)).map ([·]) := by
  cases c <;> decide

/-- Default Set B (61): with no features copied, the Elsewhere item *tz'=* is inserted, whatever
the object's cell. -/
theorem setB_transitive (c : PronCell) : insert1 (inflTerminal .P c) = some (.procl "tz'") := by
  cases c <;> decide

/-- The Fragment's Set A paradigm (Table 4.5, pre-consonantal) is the Vocabulary's spell-out of
what Voice or Poss copies. -/
theorem setA_realize (c : PronCell) :
    (setAExponent .consonant).realize (.pn c.person c.number)
      = (insert1 (vnTerminal c)).map ([·]) := by
  cases c <;> decide

/-- The competition of *chin* and *qin* (Table 4.10): both realize first-person singular; the
Infl-specified item wins on Infl and only the context-free base is available off it. -/
theorem chin_beats_qin :
    insert1 (copied .firstSg ++ [.head .infl]) = some (.free "chin") ∧
      insert1 (copied .firstSg) = some (.free "qin") := by
  decide

/-! ### Pronoun form (§4.4) -/

/-- The dimension an impoverishment rule deletes. -/
inductive Dim
  | author | participant | singular
  deriving DecidableEq, Repr

/-- Delete a dimension from a terminal. -/
def delete (t : List Feat) (d : Dim) : List Feat :=
  t.filter λ f => match f, d with
    | .author _, .author | .participant _, .participant | .singular _, .singular => false
    | _, _ => true

/-- Whether a terminal carries the flag of some probe. -/
def flagged (t : List Feat) : Bool := t.any λ f => match f with | .flag _ => true | _ => false

/-- The impoverishment rule (84): number is deleted from a first-person pronoun a probe has
flagged. -/
def rule84 : ImpoverishmentRule (List Feat) Dim :=
  .paradigmatic (λ t => (Feat.author true ∈ t) && flagged t) .singular

/-- The optional rule (93): number is deleted from a second-person pronoun flagged by Voice or
Poss. -/
def rule93 : ImpoverishmentRule (List Feat) Dim :=
  .paradigmatic (λ t => (Feat.participant true ∈ t) && (Feat.flag .vn ∈ t)) .singular

theorem rule84_paradigmatic : rule84.Paradigmatic :=
  ImpoverishmentRule.paradigmatic_isParadigmatic _ _

/-- A pronoun terminal in a cell, flagged by the probe that copied its features, if any. -/
def pronounTerminal (l : Option Locus) (c : PronCell) : List Feat :=
  cellFeats c ++ (l.map λ l => [Feat.flag l]).getD []

/-- The form of a pronoun in a cell under a grammar with impoverishment rules `rules`, flagged
by `l`: the rules apply and every licensed item is inserted. -/
def formWith (rules : List (ImpoverishmentRule (List Feat) Dim)) (l : Option Locus) (c : PronCell) :
    List Morph :=
  insertAll (runChain (ImpoverishmentRule.apply delete) rules ↑(pronounTerminal l c))

/-- The form of a pronoun under the grammar of (84). -/
def form (l : Option Locus) (c : PronCell) : List Morph := formWith [rule84] l c

/-- The morphemes of the Fragment's pronoun entries (Table 4.9): *qin=i*, *qo'=y*, *qo*, *=i*,
*q=i*, *qa*, and the null third-person singular. -/
def morphemes : Option PersonalPronoun → List Morph
  | some p =>
    if p = qini then [.free "qin", .encl "i"]
    else if p = qoy then [.free "qo", .encl "i"]
    else if p = qo then [.free "qo"]
    else if p = iDisagr then [.encl "i"]
    else if p = qi then [.free "q", .encl "i"]
    else if p = qa then [.free "qa"]
    else []
  | none => []

/-- The independent series (Table 4.25): an unflagged pronoun, an object or the subject of a
non-verbal predicate, hosts every item its features license. -/
theorem form_unflagged (c : PronCell) : form none c = morphemes (independent c) := by
  cases c <;> decide

/-- The subject and possessor series (Table 4.25): a pronoun flagged by either locus loses its
number if first person, so the bases *qin* and *qo* are bled and the enclitic remains. -/
theorem form_flagged (l : Locus) (c : PronCell) : form (some l) c = morphemes (subjPoss c) := by
  cases l <;> cases c <;> decide

/-- With the optional rule (93), second-person plural reduces to the enclitic in a Set A context
but not in a Set B context ((89)–(91)). -/
theorem form_rule93 :
    formWith [rule84, rule93] (some .vn) .secondPl = [.encl "i"] ∧
      formWith [rule84, rule93] (some .infl) .secondPl = morphemes (subjPoss .secondPl) := by
  decide

/-- The form of an argument in a cell: flagged by the probe that agreed with it. -/
def formAt (r : ArgumentRole) (c : PronCell) : List Morph := form (agreedBy r) c

/-- The nominative alignment of reduction ((3), (8)): subjects take the reduced series and the
object the independent series. -/
theorem formAt_eq (c : PronCell) :
    formAt .S c = morphemes (subjPoss c) ∧ formAt .A c = morphemes (subjPoss c) ∧
      formAt .P c = morphemes (independent c) :=
  ⟨form_flagged .infl c, form_flagged .vn c, form_unflagged c⟩

/-! ### The judgments -/

/-- A pronoun's spelling: its morphemes with clitic boundaries. -/
def spell (ms : List Morph) : String :=
  String.join (ms.map λ m => match m.kind with
    | .bound .after .clitic => "=" ++ m.form
    | _ => m.form)

/-- A judgment of the pool: the position's flag, the cell, the pronoun, whether the optional
rule (93) is in force, and the judgment. -/
structure Row where
  flag : Option Locus
  cell : PronCell
  pronoun : String
  optional : Bool
  accepted : Bool
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let fs := ex.paperFeatures
  let flag ← match fs.lookup "position" with
    | some "S" => some (some Locus.infl)
    | some "A" | some "possessor" => some (some Locus.vn)
    | some "object" | some "unagreed" => some none
    | _ => none
  let cell ← match fs.lookup "cell" with
    | some "1sg" => some PronCell.firstSg | some "1plExcl" => some PronCell.firstPlExcl
    | some "1plIncl" => some PronCell.firstPlIncl | some "2sg" => some PronCell.secondSg
    | some "2pl" => some PronCell.secondPl | some "3sg" => some PronCell.thirdSg
    | some "3pl" => some PronCell.thirdPl | _ => none
  let pronoun ← fs.lookup "morphemes"
  pure ⟨flag, cell, pronoun, fs.lookup "optionalReduction" = some "yes",
    ex.judgment = .acceptable⟩

/-- The pronoun judgments of §4.4. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- A pronoun is accepted exactly when it is the derived form, under (84) or, where the row
invokes it, the optional (93). -/
theorem pronoun_rows :
    ∀ r ∈ rows, (r.accepted = true ↔
      spell (form r.flag r.cell) = r.pronoun ∨
        (r.optional = true ∧ spell (formWith [rule84, rule93] r.flag r.cell) = r.pronoun)) := by
  decide

end Scott2023
