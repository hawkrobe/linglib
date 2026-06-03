import Linglib.Data.WALS.Features.F46A
import Linglib.Features.Indefinite
import Linglib.Syntax.Pronoun.Indefinite

/-!
# Indefinite-pronoun typology — cross-linguistic generalizations
[haspelmath-1997] [wals-2013]

Typological generalizations *over* indefinite pronouns. The lexical object itself —
`IndefinitePronoun` and its [haspelmath-1997] feature taxonomy (`HaspelmathFunction`,
`OntologicalCategory`, `MorphologicalBasis`) — is an *object*, and lives in the pronoun layer at
`Syntax/Pronoun/Indefinite.lean`; this file imports it and adds the cross-linguistic apparatus a
typological reference grammar records: a language's full paradigm, the WALS F46A bridge, and the
SK/SU/NS syncretism typology.

Theory-specific apparatus (Degano & Aloni's 7-type team-semantic typology, choice-function
denotations, Hamblin alternatives) lives as projections in theory files (e.g.,
`Studies/DeganoAloni2025.lean`), not in this substrate.

## Schema

- `MorphologicalBasis.toWALS46A`: each single basis → its [wals-2013] F46A cell
- `IndefiniteParadigm`: a language's full paradigm + ISO 639-3 code, with F46A derivation,
  contiguity / coverage / disjointness predicates
- `SyncretismPattern`: the SK/SU/NS triangle patterns, `.ABA` banned by the adjacency universal

## WALS bridge

`IndefiniteParadigm.toWALS46A` derives the paradigm-level F46A classification (including the
`.mixed` cell when forms use multiple bases) from the per-form basis distribution. Cross-linguistic
bridge theorems anchored on a paper live in that paper's `Studies/AuthorYear.lean`.
-/

set_option autoImplicit false

namespace Indefinite

open Data.WALS

/-! ### Morphological basis → WALS F46A -/

/-- Forward map to the [wals-2013] F46A category for a single basis.
    F46A's fifth cell `.mixed` is reserved for paradigms with multiple bases. -/
def MorphologicalBasis.toWALS46A : MorphologicalBasis → F46A.IndefinitePronouns
  | .interrogative           => .interrogativeBased
  | .genericNoun             => .genericNounBased
  | .special                 => .special
  | .existentialConstruction => .existentialConstruction

/-! ### The paradigm -/

/-- A language's full indefinite-pronoun paradigm. `isoCode` is ISO 639-3,
    the join key for [wals-2013] `Datapoint.iso`. -/
structure IndefiniteParadigm where
  language : String
  isoCode : String
  forms : List IndefinitePronoun
  deriving DecidableEq, Repr -- inherits manual Repr IndefinitePronoun

namespace IndefiniteParadigm

variable (p : IndefiniteParadigm)

/-- Forms in `p` whose distribution covers function `f`. -/
def formsFor (f : HaspelmathFunction) : List IndefinitePronoun :=
  p.forms.filter (·.covers f)

/-- The first form (in declaration order) covering `f`, if any. Used to
    compute the syncretism pattern over the SK/SU/NS triangle. -/
def formAt (f : HaspelmathFunction) : Option String :=
  (p.forms.find? (·.covers f)).map (·.form)

/-- The list of distinct morphological bases used in this paradigm. -/
def basisList : List MorphologicalBasis :=
  (p.forms.map (·.basis)).dedup

/-- Derive the [wals-2013] F46A classification from the paradigm's
    morphological-basis distribution: a single basis maps via
    `MorphologicalBasis.toWALS46A`; multiple distinct bases project to
    F46A's `.mixed` cell; an empty paradigm yields `none`. -/
def toWALS46A : Option F46A.IndefinitePronouns :=
  match p.basisList with
  | []          => none
  | [b]         => some b.toWALS46A
  | _ :: _ :: _ => some .mixed

/-- WALS F46A classification by `lookupISO p.isoCode` — independent of
    the paradigm's `basis` annotations. Use `toWALS46A` for the
    Fragment-derived classification; use `wals46A` for the WALS-stated
    classification. The two should agree (a bridge theorem typically
    asserts this), but for paradigms encoding multiple bases the two can
    diverge if the WALS encoding picks one strategy. -/
def wals46A : Option F46A.IndefinitePronouns :=
  (Datapoint.lookupISO F46A.allData p.isoCode).map (·.value)

/-- Number of distinct forms in the paradigm. -/
def formCount : Nat := p.forms.length

/-- All distinct functions covered across all forms in the paradigm,
    in `HaspelmathFunction.all` order. -/
def allFunctions : List HaspelmathFunction :=
  HaspelmathFunction.all.filter (fun f => p.forms.any (·.covers f))

/-- Every form covers a contiguous region on the [haspelmath-1997] map. -/
def AllContiguous : Prop :=
  ∀ e ∈ p.forms,
    HaspelmathFunction.isContiguous
      (HaspelmathFunction.all.filter (e.covers ·)) = true

instance : Decidable p.AllContiguous := List.decidableBAll _ _

/-- The paradigm covers all nine functions on the implicational map. -/
def CoversAllFunctions : Prop :=
  ∀ f ∈ HaspelmathFunction.all, p.forms.any (·.covers f) = true

instance : Decidable p.CoversAllFunctions := List.decidableBAll _ _

/-- The forms have disjoint function sets (no function in two forms). -/
def FormsDisjoint : Prop :=
  ∀ f ∈ HaspelmathFunction.all, (p.forms.filter (·.covers f)).length ≤ 1

instance : Decidable p.FormsDisjoint := List.decidableBAll _ _

end IndefiniteParadigm

/-! ### Syncretism patterns on the SK/SU/NS triangle -/

/-- Syncretism pattern on [haspelmath-1997]'s SK/SU/NS triple.
    `IsAttested` excludes `.ABA` (banned by the implicational map's
    contiguity universal — NS and SK are not adjacent). -/
inductive SyncretismPattern where
  /-- All three coexpressed by a single form (English-style `some-`). -/
  | AAA
  /-- SU+SK coexpressed, NS distinct (Yakut: `ere` vs `eme`). -/
  | ABB
  /-- NS+SU coexpressed, SK distinct (Latin: `ali-` vs `-dam`). -/
  | AAB
  /-- All three distinct (Russian: `nibud'` vs `to` vs `koe-`). -/
  | ABC
  /-- NS+SK coexpressed but not SU — *unattested* (banned by adjacency). -/
  | ABA
  deriving DecidableEq, Repr, BEq

/-- Classify a triple of forms (NS, SU, SK) into a syncretism pattern. -/
def classifyTriple (nsForm suForm skForm : String) : SyncretismPattern :=
  if nsForm == suForm && suForm == skForm then .AAA
  else if nsForm == suForm then .AAB
  else if suForm == skForm then .ABB
  else if nsForm == skForm then .ABA
  else .ABC

/-- The paradigm's syncretism pattern, derived from forms covering SK/SU/NS.
    Returns `none` if any of the three functions has no covering form
    (the paradigm has gaps in the SK/SU/NS region). -/
def IndefiniteParadigm.syncretism (p : IndefiniteParadigm) :
    Option SyncretismPattern := do
  let ns ← p.formAt .irrealis
  let su ← p.formAt .specificUnknown
  let sk ← p.formAt .specificKnown
  return classifyTriple ns su sk

/-- [haspelmath-1997]'s adjacency universal: ABA is unattested
    cross-linguistically because NS and SK are non-adjacent on the map. -/
def SyncretismPattern.IsAttested (s : SyncretismPattern) : Prop := s ≠ .ABA

instance : DecidablePred SyncretismPattern.IsAttested :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

theorem aba_unattested : ¬ SyncretismPattern.IsAttested .ABA := by decide

/-! ### Verification -/

theorem classify_aaa : classifyTriple "A" "A" "A" = .AAA := rfl
theorem classify_aab : classifyTriple "A" "A" "B" = .AAB := rfl
theorem classify_abb : classifyTriple "A" "B" "B" = .ABB := rfl
theorem classify_abc : classifyTriple "A" "B" "C" = .ABC := rfl
theorem classify_aba : classifyTriple "A" "B" "A" = .ABA := rfl

end Indefinite
