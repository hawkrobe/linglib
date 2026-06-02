import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Data.WALS.Features.F46A
import Linglib.Syntax.Pronoun.Basic

/-!
# Indefinite-pronoun typology — consensus substrate
[haspelmath-1997] [wals-2013]

Theory-neutral types for cross-linguistic indefinite-pronoun data, following
the same `Typology/{Domain}.lean` pattern as `WordOrder.lean`,
`Adposition.lean`, `MorphProfile.lean`. The lexical object `IndefinitePronoun`
`extends` the general `Pronoun` (`Syntax/Pronoun/Basic.lean`), so an
indefinite pronoun is a single object that flows through the Pronoun API and
carries its own implicational-map distribution.

Theory-specific apparatus (Degano & Aloni's 7-type team-semantic typology,
choice-function denotations, Hamblin alternatives, …) lives as projections
in theory files (e.g., `Semantics/Quantification/DeganoAloni2025.lean`),
not in this substrate. This follows the consensus-only Fragment-schema
discipline: the substrate carries only what a typological reference
grammar would record.

## Schema

- `HaspelmathFunction`: 9 functions on [haspelmath-1997]'s implicational map
- `OntologicalCategory`: 7 core categories (+ determiner, reason) of §3.1.3
- `MorphologicalBasis`: 4 morphological strategies (= 4 of WALS F46A's 5 cells)
- `IndefinitePronoun`: `extends Pronoun` with ontology + basis + function-coverage
- `IndefiniteParadigm`: a language's full paradigm + ISO 639-3 code

## WALS bridge

`MorphologicalBasis.toWALS46A` maps each basis to its WALS F46A cell;
`IndefiniteParadigm.toWALS46A` derives the paradigm-level F46A classification
(including the `.mixed` cell when forms use multiple bases) from the per-form
basis distribution. Cross-linguistic bridge theorems anchored on a paper live
in that paper's `Studies/AuthorYear.lean`.
-/

set_option autoImplicit false

namespace Typology.Indefinite

open Data.WALS

-- ============================================================================
-- §1. Haspelmath 1997 function map
-- ============================================================================

/-- The 9 indefinite-pronoun functions on [haspelmath-1997]'s
    implicational map. A single form covers a contiguous region of the map. -/
inductive HaspelmathFunction where
  /-- Function 1: Specific known. Speaker has a referent in mind. -/
  | specificKnown
  /-- Function 2: Specific unknown. Speaker presupposes a referent
      but cannot identify it. -/
  | specificUnknown
  /-- Function 3: Irrealis non-specific. No specific referent intended. -/
  | irrealis
  /-- Function 4: Polar / content question. -/
  | question
  /-- Function 5: Conditional protasis. -/
  | conditional
  /-- Function 6: Standard of comparison. -/
  | comparative
  /-- Function 7: Indirect (clause-mate) negation. -/
  | indirectNeg
  /-- Function 8: Direct negation. -/
  | directNeg
  /-- Function 9: Free choice. -/
  | freeChoice
  deriving DecidableEq, Repr, BEq

/-- All nine functions, listed in map order. -/
def HaspelmathFunction.all : List HaspelmathFunction :=
  [ .specificKnown, .specificUnknown, .irrealis, .question
  , .conditional, .indirectNeg, .directNeg, .comparative, .freeChoice ]

/-- Adjacency on [haspelmath-1997]'s implicational map.

    ```
    specKnown — specUnknown — irrealis — question — conditional — indNeg — dirNeg
                                                                              |
                                                    freeChoice — comparative —+
    ```

    Crucial typological claim: any pronoun series covers a *contiguous* region. -/
def HaspelmathFunction.adjacent : HaspelmathFunction → List HaspelmathFunction
  | .specificKnown   => [.specificUnknown]
  | .specificUnknown => [.specificKnown, .irrealis]
  | .irrealis        => [.specificUnknown, .question]
  | .question        => [.irrealis, .conditional]
  | .conditional     => [.question, .indirectNeg]
  | .indirectNeg     => [.conditional, .directNeg]
  | .directNeg       => [.indirectNeg, .comparative]
  | .comparative     => [.directNeg, .freeChoice]
  | .freeChoice      => [.comparative]

/-- Is `f` a downward-entailing / nonveridical context (the classical
    NPI-licensing region: question, conditional, indirect/direct negation)?
    Used by [chierchia-2006]-style polarity-item typologies to predict
    NPI distribution. -/
def HaspelmathFunction.isDE : HaspelmathFunction → Bool
  | .question | .conditional | .indirectNeg | .directNeg => true
  | _ => false

/-- Is `f` a free-choice context (comparative + freeChoice)? Comparative
    standards are universal-flavored and pattern with FC cross-linguistically
    ([haspelmath-1997]). -/
def HaspelmathFunction.isFC : HaspelmathFunction → Bool
  | .comparative | .freeChoice => true
  | _ => false

/-- BFS on the implicational map restricted to a given set of functions.
    Returns the set of nodes reachable from `start` through edges whose
    endpoints both lie in `funcs`. -/
def HaspelmathFunction.bfsReachable
    (funcs : List HaspelmathFunction) (start : HaspelmathFunction)
    (fuel : Nat := 10) : List HaspelmathFunction :=
  let rec go (queue visited : List HaspelmathFunction) (fuel : Nat) :
      List HaspelmathFunction :=
    match fuel, queue with
    | 0,         _       => visited
    | _,         []      => visited
    | fuel + 1, f :: rest =>
      let neighbors := f.adjacent.filter (fun g =>
        funcs.contains g && !visited.contains g)
      go (rest ++ neighbors) (visited ++ neighbors) fuel
  go [start] [start] fuel

/-- A list of functions is *contiguous* on the implicational map iff BFS
    from any element reaches all others. [haspelmath-1997]'s key
    constraint: every pronoun series must cover a contiguous region. -/
def HaspelmathFunction.isContiguous (funcs : List HaspelmathFunction) : Bool :=
  match funcs with
  | []     => true
  | f :: _ => funcs.all (HaspelmathFunction.bfsReachable funcs f 15).contains

-- ============================================================================
-- §1b. Ontological categories ([haspelmath-1997] §3.1.3)
-- ============================================================================

/-- The ontological categories of indefinite pronouns
    ([haspelmath-1997] §3.1.3, Table 3.1). The seven core categories —
    person, thing, property, place, time, manner, amount — are the categories
    "most often expressed by simple means in the languages of the world"; the
    human/non-human cut (person vs thing, *somebody* vs *something*) is made
    practically everywhere. `determiner` ('which', distinct from substantival
    'who'/'what') and `reason` ('why') are common but non-universal (English
    and German have no indefinite *somewhy*). -/
inductive OntologicalCategory where
  /-- Person: *somebody/someone* (interrogative *who?*). -/
  | person
  /-- Thing: *something* (interrogative *what?*). -/
  | thing
  /-- Property / kind: *some kind of* (interrogative *what kind?*). -/
  | property
  /-- Place: *somewhere* (interrogative *where?*). -/
  | place
  /-- Time: *sometime* (interrogative *when?*). -/
  | time
  /-- Manner: *somehow* (interrogative *how?*). -/
  | manner
  /-- Amount: *some amount* (interrogative *how much?*). -/
  | amount
  /-- Determiner: *some N* / 'which' — non-universal, distinct from the
      substantival 'who'/'what'. -/
  | determiner
  /-- Reason / cause: 'for some reason' (interrogative *why?*) — non-universal. -/
  | reason
  deriving DecidableEq, Repr, BEq

/-- The seven core ontological categories realized "practically everywhere"
    ([haspelmath-1997] §3.1.3); excludes the non-universal `determiner`
    and `reason`. -/
def OntologicalCategory.core : List OntologicalCategory :=
  [.person, .thing, .property, .place, .time, .manner, .amount]

/-- All nine ontological categories (the seven core plus `determiner`, `reason`). -/
def OntologicalCategory.all : List OntologicalCategory :=
  OntologicalCategory.core ++ [.determiner, .reason]

-- ============================================================================
-- §2. Morphological basis (= WALS F46A categories)
-- ============================================================================

/-- [haspelmath-1997]'s four morphological strategies for deriving
    indefinite pronouns. Aligns with the four single-strategy values of
    [wals-2013] F46A; F46A's `.mixed` cell arises only at the
    paradigm level (see `IndefiniteParadigm.toWALS46A`). -/
inductive MorphologicalBasis where
  /-- Built from interrogative pronouns (`who-`, `what-`, …). -/
  | interrogative
  /-- Built from generic nouns ('person', 'thing', 'place'). -/
  | genericNoun
  /-- A dedicated indefinite morpheme. -/
  | special
  /-- An existential predication construction. -/
  | existentialConstruction
  deriving DecidableEq, Repr, BEq

/-- Forward map to the [wals-2013] F46A category for a single basis.
    F46A's fifth cell `.mixed` is reserved for paradigms with multiple bases. -/
def MorphologicalBasis.toWALS46A : MorphologicalBasis → F46A.IndefinitePronouns
  | .interrogative           => .interrogativeBased
  | .genericNoun             => .genericNounBased
  | .special                 => .special
  | .existentialConstruction => .existentialConstruction

-- ============================================================================
-- §3. Entry + paradigm
-- ============================================================================

/-- A single indefinite pronoun — the canonical lexical object, `extends`ing the
    general `Pronoun` (surface `form` + φ-features) with the indefinite-specific
    structure: its `ontology`-cal category ([haspelmath-1997] §3.1.3), its
    morphological `basis`, and the `functions` it covers on the implicational map.

    This is the single source of truth for an indefinite pronoun: it *is* a
    `Pronoun`, so it flows through the Pronoun API, and it carries its own
    distribution. `functions` is the realized cross-linguistic distribution
    (textbook-consensus data); theory-specific predictions about which functions
    a form *should* cover (Degano & Aloni 7-type team-semantics, choice-function
    denotation, Hamblin alternatives) are projections into theory-side types,
    not fields here. -/
structure IndefinitePronoun extends Pronoun where
  /-- The [haspelmath-1997] §3.1.3 ontological category (person, thing, …). -/
  ontology : OntologicalCategory
  /-- The morphological derivation strategy (interrogative-based, etc.). -/
  basis : MorphologicalBasis
  /-- The functions on [haspelmath-1997]'s implicational map this form
      covers (a contiguous region; see `IndefiniteParadigm.AllContiguous`). -/
  functions : Finset HaspelmathFunction
  deriving DecidableEq

/-- Manual `Repr` showing just the surface `form` to avoid the `unsafe`
    `Repr (Finset α)` instance from `Mathlib.Data.Finset.Sort`, which
    would propagate unsafety into every consumer of `IndefinitePronoun`. -/
instance : Repr IndefinitePronoun where
  reprPrec e _ := s!"{e.form}"

/-- Does this entry cover function `f`? -/
def IndefinitePronoun.covers (e : IndefinitePronoun) (f : HaspelmathFunction) : Bool :=
  decide (f ∈ e.functions)

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

/-- For each form, the list of functions it covers, in `HaspelmathFunction.all`
    order. -/
def IndefinitePronoun.functionList (e : IndefinitePronoun) : List HaspelmathFunction :=
  HaspelmathFunction.all.filter (e.covers ·)

/-- Coverage of a single form: number of functions it spans. -/
def IndefinitePronoun.coverage (e : IndefinitePronoun) : Nat :=
  e.functionList.length

-- ============================================================================
-- §4. Syncretism patterns on the SK/SU/NS triangle
-- ============================================================================

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

-- ============================================================================
-- §5. Verification
-- ============================================================================

theorem classify_aaa : classifyTriple "A" "A" "A" = .AAA := rfl
theorem classify_aab : classifyTriple "A" "A" "B" = .AAB := rfl
theorem classify_abb : classifyTriple "A" "B" "B" = .ABB := rfl
theorem classify_abc : classifyTriple "A" "B" "C" = .ABC := rfl
theorem classify_aba : classifyTriple "A" "B" "A" = .ABA := rfl

end Typology.Indefinite
