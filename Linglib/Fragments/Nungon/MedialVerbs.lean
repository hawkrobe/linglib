import Linglib.Data.UD.Basic
import Linglib.Syntax.Number.Capabilities
import Linglib.Syntax.Person.Capabilities
import Linglib.Syntax.Clause.Chaining

/-!
# Nungon Medial Verb Morphology [sarvasy-2017]
[sarvasy-2015] [sarvasy-aikhenvald-2025]

Medial verb morphology in Nungon (Trans-New Guinea, Finisterre-Huon family;
Morobe Province, Papua New Guinea). Nungon has the most extensively described
clause chaining system in the recent literature.

## Key properties

Nungon medial verbs are maximally reduced: they carry no tense, no aspect,
and no independent mood marking. The single final verb in each chain supplies
tense and mood for the entire chain. The only morphology on a medial verb is:
1. The verb stem
2. A switch-reference suffix encoding subject continuity (SS vs. DS) and
   temporal relation (sequential vs. simultaneous)

## Switch-reference

The SR system is four-way, crossing two binary dimensions:
- **Subject continuity**: same subject (SS) vs. different subject (DS)
- **Temporal relation**: sequential (SEQ) vs. simultaneous (SIM)

SS forms are invariant (no person/number indexing). DS forms obligatorily
index the person and number of the medial clause's subject argument — the
participant whose identity *differs* from the following clause's subject.

## DS person/number paradigm ([sarvasy-aikhenvald-2025]: Table 2)

| Person | Singular | Dual | Plural |
|--------|----------|------|--------|
| 1 | -wa-ya | -ra-ya | -na-ya |
| 2 | -i-ya | -uny-a | -u-ya |
| 3 | -un-a | -uny-a | -u-ya |

Note: 2du and 3du are syncretic (-uny-a); 2pl and 3pl are syncretic (-u-ya).

The language's clause-chaining system (`chaining`) is read off this inventory where it can be:
the switch-reference type from the relations the SS suffixes distinguish, the agreement profile
from the DS paradigm, and the marked relations from the SS categories.
-/

namespace Nungon.MedialVerbs

-- ============================================================================
-- § SR suffix types
-- ============================================================================

/-- Switch-reference category combining subject continuity and temporal relation.
    Nungon has a four-way system: SS-SEQ, SS-SIM, DS-SEQ, DS-SIM. -/
inductive SRCategory where
  | ssSEQ  -- same subject, sequential events
  | ssSIM  -- same subject, simultaneous events
  | dsSEQ  -- different subject, sequential events
  | dsSIM  -- different subject, simultaneous events
  deriving DecidableEq, Repr, Inhabited

/-- Whether this SR category indicates same subject. -/
def SRCategory.isSS : SRCategory → Bool
  | .ssSEQ | .ssSIM => true
  | .dsSEQ | .dsSIM => false

/-- Whether this SR category indicates sequential temporal relation. -/
def SRCategory.isSequential : SRCategory → Bool
  | .ssSEQ | .dsSEQ => true
  | .ssSIM | .dsSIM => false

-- ============================================================================
-- § DS person/number paradigm ([sarvasy-aikhenvald-2025]: Table 2)
-- ============================================================================

/-- Person/number combination for DS medial verb agreement. -/
structure PersonNumber where
  person : UD.Person
  number : UD.Number
  deriving DecidableEq, Repr

/-- A person/number index bears its number slot (`HasNumber`). -/
instance : HasNumber PersonNumber := ⟨fun pn => Number.fromUD pn.number⟩

instance : HasPerson PersonNumber := ⟨fun pn => some (Person.fromUD pn.person)⟩

/-- A DS suffix entry: form + person/number it indexes. -/
structure DSSuffix where
  form : String
  personNumber : PersonNumber
  deriving Repr, BEq

/-- 1sg DS suffix. -/
def ds1sg : DSSuffix := { form := "-wa-ya", personNumber := ⟨.first, .Sing⟩ }
/-- 2sg DS suffix. -/
def ds2sg : DSSuffix := { form := "-i-ya", personNumber := ⟨.second, .Sing⟩ }
/-- 3sg DS suffix. -/
def ds3sg : DSSuffix := { form := "-un-a", personNumber := ⟨.third, .Sing⟩ }
/-- 1du DS suffix. -/
def ds1du : DSSuffix := { form := "-ra-ya", personNumber := ⟨.first, .Dual⟩ }
/-- 2du DS suffix (syncretic with 3du). -/
def ds2du : DSSuffix := { form := "-uny-a", personNumber := ⟨.second, .Dual⟩ }
/-- 3du DS suffix (syncretic with 2du). -/
def ds3du : DSSuffix := { form := "-uny-a", personNumber := ⟨.third, .Dual⟩ }
/-- 1pl DS suffix. -/
def ds1pl : DSSuffix := { form := "-na-ya", personNumber := ⟨.first, .Plur⟩ }
/-- 2pl DS suffix (syncretic with 3pl). -/
def ds2pl : DSSuffix := { form := "-u-ya", personNumber := ⟨.second, .Plur⟩ }
/-- 3pl DS suffix (syncretic with 2pl). -/
def ds3pl : DSSuffix := { form := "-u-ya", personNumber := ⟨.third, .Plur⟩ }

/-- Full DS paradigm. -/
def dsParadigm : List DSSuffix :=
  [ds1sg, ds2sg, ds3sg, ds1du, ds2du, ds3du, ds1pl, ds2pl, ds3pl]

-- ============================================================================
-- § SS suffixes
-- ============================================================================

/-- SS suffixes are invariant (no person/number indexing). -/
structure SSSuffix where
  form : String
  category : SRCategory
  deriving Repr, BEq

/-- SS sequential suffix. -/
def ssSEQ : SSSuffix := { form := "-se", category := .ssSEQ }

/-- SS simultaneous suffix. -/
def ssSIM : SSSuffix := { form := "-ma", category := .ssSIM }

/-- All SS suffixes. -/
def ssSuffixes : List SSSuffix := [ssSEQ, ssSIM]

/-! ### The clause-chaining system -/

/-- The interclausal relation an SR category encodes. -/
def SRCategory.relation : SRCategory → Clause.Chaining.InterclauseRelation
  | .ssSEQ | .dsSEQ => .sequential
  | .ssSIM | .dsSIM => .simultaneous

/-- The relations the SS suffixes distinguish. -/
def ssRelations : List Clause.Chaining.InterclauseRelation :=
  (ssSuffixes.map (·.category.relation)).eraseDups

/-- Nungon's clause-chaining system: medial-final chains whose medial verbs carry only a
switch-reference suffix, the same-subject forms distinguishing the temporal relations and the
different-subject forms indexing the medial subject; tense, mood and aspect come from the
final verb, clauses are negated individually, recapitulative and summary linkage both occur,
and medial clauses are used on their own ([sarvasy-aikhenvald-2025] Ch. 7, [sarvasy-2017]). -/
def chaining : Clause.Chaining.System where
  direction := .medialFinal
  srSystem := if 1 < ssRelations.length then .ssDsTemporal else .ssDs
  srTarget := some .subjectOnly
  srObligatory := true
  srMarkedness := some .ssUnmarked
  medialMorph := {
    tense := .absent
    agreement := if dsParadigm.isEmpty then .absent else .restricted
    mood := .absent
    polarity := .full
    aspect := .absent }
  relationsMarked := ssRelations
  hasRecapLinkage := true
  hasSummaryLinkage := true
  medialCanStandAlone := true

end Nungon.MedialVerbs
