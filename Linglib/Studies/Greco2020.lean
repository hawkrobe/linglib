import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Semantics.Polarity.ExpletiveNegation
import Linglib.Data.Examples.Greco2020

/-!
# Greco (2020): On the Syntax of Surprise Negation Sentences

This file formalizes [greco-2020]'s analysis of Italian surprise negation sentences (Snegs) such
as *E non mi è scesa dal treno Maria?!* 'Mary got off the train!', affirmative sentences carrying
the negative marker *non*. The paper places Snegs in the strong class of expletive negation, the
class licensing no polarity-sensitive element (Tables 1 and 2), separates them from negative
rhetorical questions and expletive negative exclamatives by wh-elements, answerhood, *dopo
tutto*, and factive embedding (`sneg_not_nrq`, `sneg_not_ene`), and derives their properties from
one representation, (59) and (65): *non* is a head externally merged in the CP field after the
CP-phase head has closed the v*P phase, selecting the focus phrase whose specifier hosts the
whole TP. Merged after the phase head, *non* cannot bind into the v*P (`Closed`, the Phase
Impenetrability Condition read off the spine (68)), which excludes n-words, NPIs, not-also
conjunctions, NEG-raising, and Aux-to-Comp while admitting positive polarity items; the occupied
focus position excludes further foci, wh-elements, quantifier raising, and answers to entity
questions while licensing expletive *e* and answers to propositional questions; and whole-TP
focalization, impossible in embedded clauses and in structures without TP, makes Snegs a root
phenomenon. `rows_sneg` checks every judgment of the pool against the requirement its
construction places on the structure, and `phase_heads` is the paper's (68): Fin°, Top°, or
Foc° as CP-phase head gives the derivation, Force° does not.

## Implementation notes

The spine (68) is a planar syntactic object over `Minimalist.LIToken`s, and `Closed p` reads
the Phase Impenetrability Condition off it: *non* is outside the interior of the phase headed by
`p` exactly when `p` merged first. The representation (73) carries the raised TP in the
specifier of the focus phrase, and the focus-side requirements read `areSistersIn` off it. The
requirement a construction places on the clause is a feature of its example row, so the
predictions are stated once over `Requirement` and checked against the rows; the section 3 rows
carry the diagnostic they test instead, and the embedded-focus rows (83) to (85) the focalized
constituent.

## References

* [greco-2020]
* [rizzi-1997]
* [chomsky-2001]
-/

namespace Greco2020

open Minimalist Negation Data.Examples Features

/-! ### Tables 1 and 2: the Italian expletive negation environments -/

/-- The eleven Italian EN environments of [greco-2020] Tables 1 and 2. -/
inductive ENEnvironment where
  | untilClauses
  | whoKnowsClauses
  | unlessClauses
  | indirectInterrogatives
  | comparativeClauses
  | negativeExclamatives
  | rhetoricalQuestions
  | notThatClauses
  | ratherThanClauses
  | beforeClauses
  | snegs
  deriving DecidableEq, Repr

/-- The weak or strong class of each environment ([greco-2020] Tables 1 and 2). -/
def ENEnvironment.strength : ENEnvironment → ENStrength
  | .untilClauses | .whoKnowsClauses | .unlessClauses | .indirectInterrogatives
  | .comparativeClauses => .weak
  | .negativeExclamatives | .rhetoricalQuestions | .notThatClauses | .ratherThanClauses
  | .beforeClauses | .snegs => .strong

/-! ### The judged sentences -/

/-- The construction a row instantiates. -/
inductive Construction where
  | sneg
  /-- A negative rhetorical question, section 3.1. -/
  | nrq
  /-- An expletive negative exclamative, section 3.2. -/
  | ene
  /-- Focalization inside an embedded clause, (83) to (85). -/
  | embeddedFocus
  deriving DecidableEq, Repr

/-- What the construction tested in a row needs of the clause it occurs in. -/
inductive Requirement where
  /-- Negation binding into the v*P: negative-scope elements, NEG-raising, Aux-to-Comp. -/
  | negScope
  /-- The v*P outside the negation's scope: positive polarity items. -/
  | noNegScope
  /-- An empty focus position: foci, wh-elements, quantifier raising, entity answers. -/
  | freeFocP
  /-- A filled focus position: expletive *e*, answers to propositional questions. -/
  | activeFocP
  /-- Embedding, which admits the focalization of a part of TP only, (83) to (85). -/
  | embedded
  /-- A structure without TP: past participle clauses and Absolute Constructions. -/
  | noTP
  /-- A negator with maximal-projection status, *no*. -/
  | phrasalNegator
  /-- Nothing: topics of every kind, presuppositional *mica*, either subject position. -/
  | any
  deriving DecidableEq, Repr, Fintype

/-- The diagnostics of section 3 separating Snegs from the other strong EN clauses. -/
inductive Diagnostic where
  | wh
  | answerhood
  | dopoTutto
  | factiveEmbedding
  deriving DecidableEq, Repr

/-- A judged sentence with the features the analysis reads off it. -/
structure Row where
  construction : Construction
  requirement : Option Requirement
  polarity : Option PolarityClass
  diagnostic : Option Diagnostic
  /-- The focalized constituent of an embedded-focus row. -/
  focus : Option Cat
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let construction ← ex.parse? "construction"
    [("Sneg", Construction.sneg), ("NRQ", .nrq), ("ENE", .ene), ("embedded focus", .embeddedFocus)]
  pure ⟨construction,
    ex.parse? "requirement"
      [("negScope", Requirement.negScope), ("noNegScope", .noNegScope), ("freeFocP", .freeFocP),
        ("activeFocP", .activeFocP), ("embedded", .embedded), ("noTP", .noTP),
        ("phrasalNegator", .phrasalNegator), ("any", .any)],
    ex.parse? "polarity"
      [("weak NPI", PolarityClass.weakNPI), ("strong NPI", .strongNPI),
        ("not-also conjunction", .notAlsoConj), ("n-word", .nWord)],
    ex.parse? "diagnostic"
      [("wh", Diagnostic.wh), ("answerhood", .answerhood), ("dopo tutto", .dopoTutto),
        ("factive embedding", .factiveEmbedding)],
    ex.parse? "focus" [("DP", Cat.D), ("TP", .T)], ex.judgment⟩

/-- The judged sentences of sections 2 to 4. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-! ### Section 3: Snegs are neither rhetorical questions nor exclamatives -/

/-- Constructions `c₁` and `c₂` receive opposite judgments on diagnostic `d` in the pool. -/
def Differ (c₁ c₂ : Construction) (d : Diagnostic) : Prop :=
  ∃ r₁ ∈ rows, ∃ r₂ ∈ rows, r₁.construction = c₁ ∧ r₂.construction = c₂ ∧
    r₁.diagnostic = some d ∧ r₂.diagnostic = some d ∧ r₁.judgment ≠ r₂.judgment

instance (c₁ c₂ : Construction) (d : Diagnostic) : Decidable (Differ c₁ c₂ d) := by
  unfold Differ; infer_instance

/-- Section 3.1: unlike negative rhetorical questions, Snegs reject wh-elements and *dopo tutto*
and serve as answers, (31), (34), (35). -/
theorem sneg_not_nrq :
    Differ .sneg .nrq .wh ∧ Differ .sneg .nrq .answerhood ∧ Differ .sneg .nrq .dopoTutto := by
  decide

/-- Section 3.2: unlike expletive negative exclamatives, Snegs reject wh-elements and factive
embedding and serve as answers, (40) to (42). -/
theorem sneg_not_ene :
    Differ .sneg .ene .wh ∧ Differ .sneg .ene .answerhood ∧
      Differ .sneg .ene .factiveEmbedding := by
  decide

/-! ### The representation: (59), (65), (68), and (73) -/

/-- The negative marker *non* of (59): a head selecting the focus phrase. -/
def non : LIToken := ⟨.simple .Neg [.Foc] "non", 0⟩

/-- Force°, the highest head of the CP field in (68). -/
def force : LIToken := ⟨.simple .Force [.Neg], 1⟩

/-- Foc°, whose specifier hosts the raised TP. -/
def foc : LIToken := ⟨.simple .Foc [.Top], 2⟩

/-- The lower Top° of (68), between Foc° and Fin°. -/
def top : LIToken := ⟨.simple .Top [.Fin], 3⟩

/-- Fin°, the lowest head of the CP field. -/
def fin : LIToken := ⟨.simple .Fin [.T], 4⟩

/-- T°. -/
def t : LIToken := ⟨.simple .T [.v], 5⟩

/-- v*, the phase head of the verbal domain. -/
def v : LIToken := ⟨.simple .v [.D], 6⟩

/-- An argument inside the v*P, the site of a negative-scope element. -/
def arg : LIToken := ⟨.simple .D [], 7⟩

/-- The v*P. -/
def vP : PlanarSyntacticObject := v * arg

/-- The spine (68) with *non* in place: Force° over Neg° over Foc° over Top° over Fin° over TP. -/
def spine : PlanarSyntacticObject := force * (non * (foc * (top * (fin * (t * vP)))))

/-- The v*P is closed to *non* under the CP-phase head `p`: the v*P lies in the interior of the
phase `p` heads and *non* does not, so `p` merged first and transferred the v*P before *non*
could bind into it ([chomsky-2001]'s Phase Impenetrability Condition). -/
def Closed (p : LIToken) : Prop :=
  (spine : SyntacticObject).Impenetrable p vP ∧ ¬ (spine : SyntacticObject).Impenetrable p non

instance (p : LIToken) : Decidable (Closed p) := inferInstanceAs (Decidable (_ ∧ _))

/-- (68): with Fin°, Top°, or Foc° as CP-phase head the v*P is closed when *non* merges; with
Force°, merged after *non*, it is not. -/
theorem phase_heads : Closed fin ∧ Closed top ∧ Closed foc ∧ ¬ Closed force := by decide

/-- The raised TP of (73). -/
def tp : PlanarSyntacticObject := t * vP

/-- Foc° over the trace of the raised TP. -/
def focBar : PlanarSyntacticObject := foc * PlanarSyntacticObject.traceOf t

/-- The representation (73): *non* selects the focus phrase whose specifier hosts the TP. -/
def sneg : PlanarSyntacticObject := non * (tp * focBar)

/-- Some constituent occupies the specifier of the unique focus phrase ([rizzi-1997]). -/
def FocOccupied : Prop :=
  ∃ x ∈ (sneg : SyntacticObject).Acc, (sneg : SyntacticObject).areSistersIn x focBar

instance : Decidable FocOccupied := Multiset.decidableExistsMultiset

/-- The whole TP is focalized. -/
def WholeTPFocused : Prop := (sneg : SyntacticObject).areSistersIn tp focBar

instance : Decidable WholeTPFocused :=
  inferInstanceAs (Decidable ((sneg : SyntacticObject).areSistersIn _ _))

/-- Whether the representation meets a requirement, under CP-phase head `p`. A phrasal negator
is excluded because the negator of (59) selects the focus phrase, which only a head does. -/
def Allows (p : LIToken) : Requirement → Prop
  | .negScope => ¬ Closed p
  | .noNegScope => Closed p
  | .freeFocP => ¬ FocOccupied
  | .activeFocP => FocOccupied
  | .embedded | .noTP => ¬ WholeTPFocused
  | .phrasalNegator => non.item.outerSel = []
  | .any => True

instance (p : LIToken) (q : Requirement) : Decidable (Allows p q) := by
  unfold Allows; cases q <;> infer_instance

/-- The predictions depend on the phase head only through `Closed`. -/
theorem allows_of_closed {p p' : LIToken} (hp : Closed p) (hp' : Closed p') (q : Requirement) :
    Allows p q ↔ Allows p' q := by
  cases q <;> simp [Allows, hp, hp']

private theorem rows_sneg_fin :
    ∀ r ∈ rows, r.construction = .sneg → ∀ q, r.requirement = some q →
      (r.judgment = .acceptable ↔ Allows fin q) := by
  decide

/-- Sections 2 and 4: under any admissible CP-phase head, a Sneg row is acceptable exactly when
the representation meets the requirement of the construction it tests. -/
theorem rows_sneg {p : LIToken} (hp : Closed p) :
    ∀ r ∈ rows, r.construction = .sneg → ∀ q, r.requirement = some q →
      (r.judgment = .acceptable ↔ Allows p q) :=
  λ r hr hc q hq => (rows_sneg_fin r hr hc q hq).trans (allows_of_closed phase_heads.1 hp q)

/-- Section 4.2.5's premise, (83) to (85): an embedded clause admits the focalization of a
constituent of TP, never of the whole TP. -/
theorem embedded_focus :
    ∀ r ∈ rows, r.construction = .embeddedFocus →
      (r.judgment = .acceptable ↔ r.focus ≠ some .T) := by
  decide

/-- Table 2's Sneg row from the derivation: the strong class licenses no polarity class, the
closed v*P excludes negative-scope elements, and (9a) to (9d) witness the rejection of each
class. -/
theorem table2_snegs {p : LIToken} (hp : Closed p) (c : PolarityClass) :
    c ∉ ENEnvironment.snegs.strength.licensed ∧ ¬ Allows p .negScope ∧
      ∃ r ∈ rows, r.polarity = some c ∧ r.requirement = some .negScope ∧
        r.judgment = .ungrammatical := by
  refine ⟨by simp [ENEnvironment.strength, ENStrength.licensed], by simp [Allows, hp], ?_⟩
  revert c; decide

end Greco2020
