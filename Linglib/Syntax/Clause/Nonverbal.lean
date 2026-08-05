/-!
# Nonverbal clause constructions

[haspelmath-2025-nonverbal]

The construction-function typology of clauses lacking a typical verb:
[haspelmath-2025-nonverbal]'s eight central types (Table 1). The type
is structured by block rather than flat, because the taxonomy has
internal algebra the paper itself exhibits: the four locopossessional
types are the product of domain × pivot definiteness (his (22)), and
the duonominal pair splits on the referentiality of the second nominal
(§2). Classifications are equations on the coordinate projections, so
the super-types of Table 2 (ascriptive, locational, possessional,
locopossessional), the predicational bifurcation of §6, and the
copula's domain restriction (§7) are proved fibers rather than lists.

Within [aikhenvald-2015-art]'s three-way classification of clauses
(ch. 11: internal structure, syntactic function, pragmatic function),
this file is the predicate-type dimension of internal structure;
`Clause.EmbeddingContext` and `Clause.SentenceType` are the other two
axes, and `Clause.Size` is internal structure's height dimension. Her
*have* vs *belong* definiteness contrast (§11.1.3) independently
motivates the pivot-definiteness coordinate.

Construction-functions only: form-based strategies (transpossessive,
existive-copula, prolocative, copula vs verbless clause, …;
[haspelmath-2025-nonverbal] §§5, 11; [aikhenvald-2015-art] §11.1.2) are
deliberately kept apart per the Croft-Haspelmath function/strategy
discipline and enter with the per-language fragments that instantiate
them. Equational subtypes (characterizational, specificational,
deictic-identificational, §§9–10) and the temporary/permanent
existential split (§12) are Table 1 subdivisions awaiting consumers.
-/

namespace Clause

/-- The two locopossessional domains ([haspelmath-2025-nonverbal] (22)):
    clauses about location vs about possession. -/
inductive LocPossDomain where
  | locational
  | possessional
  deriving DecidableEq, Repr

/-- A nonverbal clause construction-function
    ([haspelmath-2025-nonverbal] Table 1), by block:

    - `duonominal`: two nominal expressions (§2); the second nominal's
      definiteness splits classificational (indefinite, nonreferential
      classificatory nominal — *Lee is a baker*) from equational (both
      definite — *Kim is my mother*).
    - `attributional`: property attribution (§3) — *The bird is small*.
    - `locopossessional`: the (22) grid — domain × pivot (locatum or
      possessum) definiteness. *The bird is on the roof* / *There is a
      bird on the roof* / *The boat belongs to me* / *I have a boat*.
    - `hypartic`: pure existence (§12) — *God exists*; not a special
      case of any other type. -/
inductive NonverbalConstruction where
  | duonominal (secondDefinite : Bool)
  | attributional
  | locopossessional (domain : LocPossDomain) (pivotDefinite : Bool)
  | hypartic
  deriving DecidableEq, Repr

namespace NonverbalConstruction

/-! ### The eight named types (Table 1) -/

/-- *Lee is a baker* — definite subject, indefinite classificatory
    nominal (§2). -/
def classificational : NonverbalConstruction := duonominal false

/-- *Kim is my mother* — two definite nominals (§2, §9). -/
def equational : NonverbalConstruction := duonominal true

/-- *The bird is on the roof* — definite locatum (§4). -/
def predlocative : NonverbalConstruction :=
  locopossessional .locational true

/-- *There is a bird on the roof* — indefinite existent (§4, §12). -/
def existential : NonverbalConstruction :=
  locopossessional .locational false

/-- *The boat belongs to me* — definite possessum (§5). -/
def appertentive : NonverbalConstruction :=
  locopossessional .possessional true

/-- *I have a boat* — indefinite possessum (§5). -/
def predpossessive : NonverbalConstruction :=
  locopossessional .possessional false

/-! ### Coordinate projections -/

/-- The second nominal's definiteness, for duonominal constructions. -/
def secondDefinite? : NonverbalConstruction → Option Bool
  | duonominal b => some b
  | _ => none

/-- The (22) domain, for locopossessional constructions. -/
def domain? : NonverbalConstruction → Option LocPossDomain
  | locopossessional d _ => some d
  | _ => none

/-- The pivot's (locatum's or possessum's) definiteness, for
    locopossessional constructions. -/
def pivotDefinite? : NonverbalConstruction → Option Bool
  | locopossessional _ b => some b
  | _ => none

/-! ### Super-types (Table 2), as fibers -/

/-- Two nominal expressions in correspondence (§2): the
    classificational + equational block. -/
def Duonominal (t : NonverbalConstruction) : Prop :=
  t.secondDefinite? ≠ none

/-- Ascribes a concept to the subject referent (§3): classificational +
    attributional. -/
def Ascriptive (t : NonverbalConstruction) : Prop :=
  t.secondDefinite? = some false ∨ t = attributional

/-- The locational column of (22): predlocative + existential. -/
def Locational (t : NonverbalConstruction) : Prop :=
  t.domain? = some .locational

/-- The possessional column of (22): predpossessive + appertentive. -/
def Possessional (t : NonverbalConstruction) : Prop :=
  t.domain? = some .possessional

/-- The whole (22) grid: [clark-1978]'s "locationals". -/
def Locopossessional (t : NonverbalConstruction) : Prop :=
  t.domain? ≠ none

instance : DecidablePred Duonominal := fun _ =>
  inferInstanceAs (Decidable (_ ≠ _))

instance : DecidablePred Ascriptive := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

instance : DecidablePred Locational := fun _ =>
  inferInstanceAs (Decidable (_ = _))

instance : DecidablePred Possessional := fun _ =>
  inferInstanceAs (Decidable (_ = _))

instance : DecidablePred Locopossessional := fun _ =>
  inferInstanceAs (Decidable (_ ≠ _))

/-- Table 2's locational super-type is exactly its two rows. -/
theorem locational_iff :
    ∀ t, Locational t ↔ t = predlocative ∨ t = existential
  | duonominal b => by cases b <;> decide
  | attributional => by decide
  | locopossessional d b => by cases d <;> cases b <;> decide
  | hypartic => by decide

/-- Table 2's possessional super-type is exactly its two rows. -/
theorem possessional_iff :
    ∀ t, Possessional t ↔ t = appertentive ∨ t = predpossessive
  | duonominal b => by cases b <;> decide
  | attributional => by decide
  | locopossessional d b => by cases d <;> cases b <;> decide
  | hypartic => by decide

/-- Table 2's ascriptive super-type is exactly its two rows. -/
theorem ascriptive_iff :
    ∀ t, Ascriptive t ↔ t = classificational ∨ t = attributional
  | duonominal b => by cases b <;> decide
  | attributional => by decide
  | locopossessional d b => by cases d <;> cases b <;> decide
  | hypartic => by decide

/-- The (22) grid is the union of its two columns. -/
theorem locopossessional_iff :
    ∀ t, Locopossessional t ↔ Locational t ∨ Possessional t
  | duonominal b => by cases b <;> decide
  | attributional => by decide
  | locopossessional d b => by cases d <;> cases b <;> decide
  | hypartic => by decide

/-! ### The predicational bifurcation (§6, Table 1) -/

/-- The clause has a topic-comment (subject-predicate) division (§6):
    an element that is a predicate rather than a referring expression.
    A duonominal predicates iff its second nominal is a nonreferential
    classificatory nominal; attributionals predicate; a locopossessional
    predicates iff its pivot is definite (the locative or appertentive
    phrase is then the predicate); hypartics do not predicate. -/
def Predicational (t : NonverbalConstruction) : Prop :=
  t.secondDefinite? = some false ∨ t = attributional ∨
    t.pivotDefinite? = some true

instance : DecidablePred Predicational := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- Table 1's predicational rows, derived: appertentive, predlocative,
    attributional, classificational. -/
theorem predicational_iff :
    ∀ t, Predicational t ↔
      t = appertentive ∨ t = predlocative ∨ t = attributional ∨
        t = classificational
  | duonominal b => by cases b <;> decide
  | attributional => by decide
  | locopossessional d b => by cases d <;> cases b <;> decide
  | hypartic => by decide

/-- Inside the (22) grid, predicationality is pivot definiteness. -/
theorem locopossessional_predicational_iff (d : LocPossDomain)
    (b : Bool) :
    Predicational (locopossessional d b) ↔ b = true := by
  cases d <;> cases b <;> decide

/-! ### The copula's domain (§7)

A copula is a form marking a stative link between the two argument
positions of an equational, ascriptive or locational clause; existives
(Spanish *hay*) are copulas restricted to existential and
predpossessive clauses (§7, §11). -/

/-- The clause types whose linking form counts as a copula (§7):
    equational, ascriptive, or locational. -/
def CopulaDomain (t : NonverbalConstruction) : Prop :=
  Duonominal t ∨ t = attributional ∨ Locational t

instance : DecidablePred CopulaDomain := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The copula domain is exactly the five types §7 names — in
    particular, 'have' in a predpossessive and 'belong' in an
    appertentive are not copulas. -/
theorem copulaDomain_iff :
    ∀ t, CopulaDomain t ↔
      t = equational ∨ t = classificational ∨ t = attributional ∨
        t = predlocative ∨ t = existential
  | duonominal b => by cases b <;> decide
  | attributional => by decide
  | locopossessional d b => by cases d <;> cases b <;> decide
  | hypartic => by decide

end NonverbalConstruction

end Clause
