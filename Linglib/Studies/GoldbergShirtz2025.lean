import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Syntax.ConstructionGrammar.Licensing
import Linglib.Semantics.Presupposition.Basic
import Linglib.Data.Examples.GoldbergShirtz2025

/-!
# Goldberg and Shirtz (2025): The English Phrase-as-Lemma Construction

This file formalizes [goldberg-shirtz-2025]'s phrase-as-lemma (PAL) construction: a phrase used in
a slot reserved for a word ("a trickle-down policy", "the 'both sides do it' argument"), whose
lemma-like construal presents the situation type as familiar to speaker and addressee, with wit and
sarcasm as rhetorical effects of discussing the presumed familiar. Five preregistered forced-choice
surveys found PAL sentences judged to imply more common knowledge than close paraphrases, and to be
wittier and more sarcastic, robustly to PAL frequency, and found four narrowly defined subtypes
(*must-V*, *a simple ⟨PAL⟩*, *Don't ⟨PAL⟩ me*, *the old ⟨PAL⟩ N*) judged more natural than
minimally different foils.

The paper's Figure 5 network is a `Constructicon`: the prenominal PAL construction inherits in
normal mode from both the NN compound and adjectival modification, which conflict on bar level and
stress (`nn_adjN_incompatible`), so the network is well-formed only because PAL's own specification
legislates exactly those fields and inherits the rest (`palSpec_eq`); the four subtypes inherit the
familiarity presupposition through the links (`subtypes_inherit_familiarity`), and removing PAL
leaves a phrase in a word slot unlicensed. The attested tokens of example (1) and Tables 2–3 and the
comparable constructions of section 7 are rows: PALs occupy every word-class slot and take that
slot's inflection (`rows_inflection`), and the host frame of a comparable construction need not be
a compound (`hostFrames_complete`).

## Implementation notes

Inheritance links name constructions by string, the substrate's convention; the experimental
statistics stay in the paper. The lemma-like familiarity is recorded as a presupposition, although
the paper treats it as an invited construal that speakers exploit precisely for situation types
that are not antecedently familiar.

## References

* [goldberg-shirtz-2025]
* [goldberg-1995]
* [meibauer-2007]
* [trips-kornfilt-2015]
* [sag-2012]
-/

namespace GoldbergShirtz2025

open ConstructionGrammar
open Presupposition Data.Examples

/-! ### The Figure 5 constructicon -/

/-- The prenominal PAL construction: a zero-level PAL whose internal syntax
is phrasal modifies a head N, forming an N′ (the paper's structure (7),
`[N′ PAL⁰ N]`, vs. the NN compound's `[N⁰ N⁰ N⁰]`). The head N's bar level
is left underspecified since PALs may modify nouns with complements
("a 'don't mess with me' type of driver"). -/
def palConstruction : Construction Unit :=
  { name := "PAL"
  , form :=
      [ { filler := .phrasal, level := some .zero }
      , { filler := .open_ .NOUN, isHead := true } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The semiproductive must-V subtype, frequently instantiated by
*must-read*, *must-see*, *must-have*. Study 5 tested only rare tokens
(≤ 10 COCA hits) against *should-V* foils. -/
def mustVerbConstruction : Construction Unit :=
  { name := "must-V"
  , form :=
      [ { filler := .fixed "must" }
      , { filler := .open_ .VERB }
      , { filler := .open_ .NOUN, isHead := true } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The *a simple ⟨PAL⟩* subtype: the PAL is itself the head noun, with
*simple* marking the situation type as routine ("Could've tried a simple
'I'm sorry.'"). Study 5's foils used *a short*. -/
def aSimplePALConstruction : Construction Unit :=
  { name := "a simple [PAL⁰]"
  , form :=
      [ { filler := .fixed "a" }
      , { filler := .fixed "simple" }
      , { filler := .phrasal, level := some .zero
        , isHead := true } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The *Don't ⟨PAL⟩ me* subtype: the PAL fills a V slot, must quote the
immediately preceding discourse, and occurs in an interdiction context
("A: you're welcome. B: No, don't 'you're welcome' me."). Study 5's foils
broke exactly the quote-from-context or interdiction condition. -/
def dontPALmeConstruction : Construction Unit :=
  { name := "Don't [PAL⁰ x y z] me"
  , form :=
      [ { filler := .fixed "Don't" }
      , { filler := .phrasal, level := some .zero
        , isHead := true }
      , { filler := .fixed "me" } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The *the old ⟨PAL⟩ (N)* subtype, with optional head N and *old*
marking the situation type as conventional ("my dad pulled the old 'I'm
going to the store for smokes, be back in five'"). Study 5's foils used
*the tired*. -/
def theOldPALConstruction : Construction Unit :=
  { name := "the old [PAL⁰] (N)"
  , form :=
      [ { filler := .fixed "the" }
      , { filler := .fixed "old" }
      , { filler := .phrasal, level := some .zero
        , isHead := true }
      , { filler := .open_ .NOUN } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- NN compound construction (parent: PAL-internal stress, tight unit). -/
def nnCompound : Construction Unit :=
  { name := "NN compound"
  , form :=
      [ { filler := .open_ .NOUN, level := some .zero }
      , { filler := .open_ .NOUN, isHead := true
        , level := some .zero } ]
  , meaning := () }

/-- Adjectival modification construction (parent: prenominal slot). -/
def adjNModification : Construction Unit :=
  { name := "Adj+N modification"
  , form :=
      [ { filler := .open_ .ADJ, level := some .zero }
      , { filler := .open_ .NOUN, isHead := true
        , level := some .bar } ]
  , meaning := () }

/-! ### Degrees of abstraction (Table 8) -/

/-- *Veggie-wrap*: a fully lexically specified noun compound (the top row
of Table 8). -/
def veggieWrapForm : TypedForm String :=
  [ { filler := .fixed "veggie" }
  , { filler := .fixed "wrap", isHead := true } ]

/-- Table 8's degree-of-abstraction grid, witnessed by the constructicon:
*veggie-wrap* is lexically specified, *a simple ⟨PAL⟩* partially open, and
the NN-compound and prenominal-PAL schemas fully open and abstract. -/
theorem table8_specificity :
    derivedSpecificity veggieWrapForm = .lexicallySpecified ∧
    aSimplePALConstruction.specificity = .partiallyOpen ∧
    nnCompound.specificity = .fullyAbstract ∧
    palConstruction.specificity = .fullyAbstract := by decide

/-- The PAL constructicon (the paper's Figure 5): the prenominal PAL
construction partially inherits, in normal mode, from both the NN compound
and adjectival modification constructions; the four conventional subtypes
confirmed by study 5 inherit from it. The figure's caption labels all
arrows "motivation and (normal mode) inheritance links", so no
Goldberg-1995 link type is assigned. -/
def palConstructicon : Constructicon Unit :=
  { constructions :=
      [ palConstruction
      , mustVerbConstruction
      , aSimplePALConstruction
      , dontPALmeConstruction
      , theOldPALConstruction
      , nnCompound
      , adjNModification ]
  , links :=
      [ { parent := "NN compound"
        , child := "PAL"
        , mode := .normal
        , sharedProperties := ["prenominal slot for the modifier"
                              , "tight semantic and phonological unit: stress falls within the PAL"]
        , overriddenProperties := ["modifier is internally phrasal; PAL N is an N′, not an N⁰"] }
      , { parent := "Adj+N modification"
        , child := "PAL"
        , mode := .normal
        , sharedProperties := ["prenominal slot for the modifier"
                              , "no recursive embedding within another PAL N construction"]
        , overriddenProperties := ["modifier is a zero-level PAL, not an Adj"] }
      , { parent := "PAL"
        , child := "must-V"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["'must' lexically fixed; V slot open"] }
      , { parent := "PAL"
        , child := "a simple [PAL⁰]"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["PAL is the head noun, not a prenominal modifier"] }
      , { parent := "PAL"
        , child := "Don't [PAL⁰ x y z] me"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties :=
            ["PAL fills a V slot; quote-from-context and interdiction required"] }
      , { parent := "PAL"
        , child := "the old [PAL⁰] (N)"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["head N optional; PAL may serve as head"] } ] }

/-! ### Form-side specifications (§6)

The inheritable form-side properties at issue in the Figure 5 network, as
`Flat` feature slots (`⊥` = the construction does not legislate), with
the componentwise lifts of the `ConstructionGrammar.Inheritance` slot
algebra. -/

/-- Locus of primary stress in a modification construction: compound
stress falls within the modifier (*BLACKbird*), phrasal modification
stresses the head (*black BIRD*). -/
inductive StressLocus where
  | modifier
  | head
  deriving DecidableEq, Repr

/-- Position of the modifier slot relative to the head. -/
inductive ModPosition where
  | prenominal
  | postnominal
  deriving DecidableEq, Repr

/-- Whether a construction's output can recur inside the construction's
own open slot. -/
inductive SelfEmbedding where
  | allowed
  | banned
  deriving DecidableEq, Repr

/-- A partial constructional specification: the inheritable form-side
properties of a nominal-modification construction ([goldberg-1995] §3.3;
[goldberg-shirtz-2025] §6). -/
structure CxnSpec where
  /-- X-bar level of the construction's output -/
  level : Flat BarLevel := ⊥
  /-- Position of the modifier slot -/
  modPosition : Flat ModPosition := ⊥
  /-- Locus of primary stress -/
  stress : Flat StressLocus := ⊥
  /-- Whether the construction self-embeds -/
  selfEmbedding : Flat SelfEmbedding := ⊥
  deriving DecidableEq, Repr

namespace CxnSpec

/-- Componentwise compatibility: complete-mode inheritance
([goldberg-1995]'s complete mode; the regime of [sag-2012]'s type
hierarchy) is defined exactly on compatible specifications. -/
def IsCompatible (p q : CxnSpec) : Prop :=
  Compat p.level q.level ∧ Compat p.modPosition q.modPosition ∧
    Compat p.stress q.stress ∧ Compat p.selfEmbedding q.selfEmbedding

instance (p q : CxnSpec) : Decidable (p.IsCompatible q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Normal-mode inheritance from a family of parent specifications,
componentwise. -/
def inherit (own : CxnSpec) (parents : List CxnSpec) : CxnSpec where
  level := inheritField own.level (parents.map (·.level))
  modPosition := inheritField own.modPosition (parents.map (·.modPosition))
  stress := inheritField own.stress (parents.map (·.stress))
  selfEmbedding := inheritField own.selfEmbedding (parents.map (·.selfEmbedding))

/-- The child's own specification legislates every field its parents
conflict on — well-formedness of a normal-mode multi-mother node. -/
def Resolves (own : CxnSpec) (parents : List CxnSpec) : Prop :=
  ResolvesField own.level (parents.map (·.level)) ∧
    ResolvesField own.modPosition (parents.map (·.modPosition)) ∧
    ResolvesField own.stress (parents.map (·.stress)) ∧
    ResolvesField own.selfEmbedding (parents.map (·.selfEmbedding))

instance (own : CxnSpec) (parents : List CxnSpec) :
    Decidable (own.Resolves parents) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end CxnSpec

/-! ### Two mothers force normal-mode inheritance (§6)

The paper's argument for normal-mode over complete inheritance: PAL's
two mothers conflict — the NN compound construction yields an N⁰ with
modifier-internal stress, adjectival modification an N′ with head stress —
so strict unification of the parents is impossible
(`nn_adjN_incompatible`), and the network is well-formed only because the
PAL construction's own specification legislates exactly the conflicting
fields (`pal_resolves`). The rest is genuinely inherited: the prenominal
modifier slot from both mothers, non-self-embedding from Adj+N
(`palSpec_eq`). -/

/-- NN compound specification: zero-level output, prenominal modifier,
compound stress within the modifier. -/
def nnCompoundSpec : CxnSpec :=
  { level := .some .zero
  , modPosition := .some .prenominal
  , stress := .some .modifier }

/-- Adj+N modification specification: N′ output, prenominal modifier,
phrasal (head) stress; per §6, "like Adj + N combinations, the PAL N
construction cannot be recursively embedded within another PAL N
construction", so Adj+N carries the non-self-embedding value PAL
inherits. -/
def adjNSpec : CxnSpec :=
  { level := .some .bar
  , modPosition := .some .prenominal
  , stress := .some .head
  , selfEmbedding := .some .banned }

/-- The PAL construction's own specification: exactly the two fields its
mothers conflict on, resolved as the paper describes — N′ output (with
Adj+N, against the compound) and PAL-internal stress (with the compound,
against Adj+N). -/
def palOwnSpec : CxnSpec :=
  { level := .some .bar
  , stress := .some .modifier }

/-- Own-specification assignment for the Figure 5 network: the two
mothers carry their specifications, PAL legislates exactly its mothers'
conflicts, and the conventional subtypes add no form-side constraints of
their own. -/
def figure5Spec (c : Construction Unit) : CxnSpec :=
  if c.name == "NN compound" then nnCompoundSpec
  else if c.name == "Adj+N modification" then adjNSpec
  else if c.name == "PAL" then palOwnSpec
  else {}

/-- PAL's full specification, computed through the network's links by
normal-mode inheritance. -/
def palSpec : CxnSpec :=
  palConstructicon.derivedSpec CxnSpec.inherit figure5Spec palConstruction

/-- No dangling links: every Figure 5 link endpoint names a construction
of the network. -/
theorem palConstructicon_wellFormed : palConstructicon.WellFormed := by
  decide

/-- The links, not a hand-written list, determine PAL's mothers. -/
theorem pal_parents :
    palConstructicon.parentsOf "PAL" = [nnCompound, adjNModification] := by
  decide

/-- The whole network is normal-mode well-formed: every construction
legislates every field its parents conflict on. -/
theorem palConstructicon_resolvesAll :
    palConstructicon.ResolvesAll CxnSpec.Resolves figure5Spec := by decide

/-- The two mothers conflict (bar level and stress), so complete-mode
inheritance cannot relate PAL to both parents — the formal content of §6's
observation that complete inheritance "is unsuitable whenever a node is
allowed more than a single mother, since specifications in two mother
nodes may conflict with one another". -/
theorem nn_adjN_incompatible :
    ¬ CxnSpec.IsCompatible nnCompoundSpec adjNSpec := by decide

/-- The Figure 5 network is normal-mode well-formed: PAL's own
specification legislates every field its mothers conflict on. Delete
either field of `palOwnSpec` and this fails. -/
theorem pal_resolves :
    CxnSpec.Resolves palOwnSpec [nnCompoundSpec, adjNSpec] := by decide

/-- The derived PAL specification, computed rather than stipulated: the
prenominal slot is inherited from both mothers (they agree),
non-self-embedding is inherited from Adj+N alone, and N′-hood and
PAL-internal stress come from PAL's own conflict resolutions. -/
theorem palSpec_eq :
    palSpec =
      { level := .some .bar
      , modPosition := .some .prenominal
      , stress := .some .modifier
      , selfEmbedding := .some .banned } := by decide

/-! ### Licensing: PAL is load-bearing

A minimal demonstration with the network's licensing relation
(`Constructicon.Licenses`): the attested "a must-do task" (the paper's
ex. (1b), determiner elided) parses as a phrase-daughter in the modifier
slot plus a head noun. The network licenses it through the PAL
construction, and rejects it when PAL is removed — the
phrase-in-word-slot configuration has no other license. -/

/-- Toy POS lexicon for the licensing demonstration. -/
def demoLexicon : String → Option UD.UPOS
  | "do" => some .VERB
  | "task" => some .NOUN
  | _ => none

/-- The internal syntax of the *must-do* PAL: must-V
(cf. `mustVerbConstruction`, which is the full prenominal construction). -/
def mustVCore : Construction Unit :=
  { name := "must-V core"
  , form :=
      [ { filler := .fixed "must" }
      , { filler := .open_ .VERB, isHead := true } ]
  , meaning := () }

/-- The Figure 5 network plus the must-V-internal construction. -/
def demoNetwork : Constructicon Unit :=
  { constructions := mustVCore :: palConstructicon.constructions
  , links := palConstructicon.links }

/-- "must-do task" (ex. (1b), determiner elided): the PAL phrase as a
constituent daughter in the word-level modifier slot. -/
def mustDoTask : Token :=
  .node [.node [.word "must", .word "do"], .word "task"]

/-- The network licenses the PAL token. -/
theorem demo_licenses_mustDoTask :
    demoNetwork.Licenses demoLexicon mustDoTask := by decide

/-- Remove the PAL construction and the token is rejected: nothing else
licenses a phrase in a word-level modifier slot. PAL is load-bearing. -/
theorem pal_load_bearing :
    ¬ ({ demoNetwork with
         constructions :=
           demoNetwork.constructions.filter (·.name != "PAL") }
        : Constructicon Unit).Licenses demoLexicon mustDoTask := by decide

/-! ### Lemma-like meaning -/

/-- A PAL utterance's two-part meaning: the head noun's denotation is
at-issue (an instance of the situation type); the lemma-like construal
contributes that the situation type itself is presumed familiar.

The paper treats the familiarity as an invited *as-if* construal rather
than a hard definedness condition: speakers exploit the construction
precisely for situation types that are not antecedently familiar
(observational humor, sniglets), so common-ground satisfaction is typically
reached by accommodation or pretense, not antecedent entailment. -/
def palMeaning (W : Type*) (situationType headNoun : W → Prop) : PartialProp W :=
  { presup := situationType, assertion := headNoun }

/-! ### Typed pragmatics: familiarity inherits through the network

The four subtype links' shared property — "lemma-like construal: presumed
familiarity" — as a computed fact rather than a string: only PAL itself
carries a pragmatic contribution (`palMeaning`); the conventional subtypes
carry none of their own, and the network derives theirs by normal-mode
inheritance through the links. Their at-issue increments ('simple' marks
routine-ness, the interdiction of *Don't ⟨PAL⟩ me*, etc.) are not modeled;
the presupposition component is the inherited content. -/

/-- The links determine PAL's conventional subtypes. -/
theorem pal_children :
    palConstructicon.childrenOf "PAL" =
      [ mustVerbConstruction, aSimplePALConstruction
      , dontPALmeConstruction, theOldPALConstruction ] := by decide

/-- Own pragmatic contributions for the Figure 5 network: only PAL itself
carries one — the familiarity-presupposing meaning. -/
def figure5Pragmatics (W : Type*) (situationType headNoun : W → Prop) :
    Construction Unit → Option (PartialProp W) :=
  λ c => if c.name == "PAL" then some (palMeaning W situationType headNoun)
         else none

/-- Every conventional subtype inherits the familiarity presupposition
through the network: each child of PAL has a derived pragmatic
contribution whose presupposition is the situation type. -/
theorem subtypes_inherit_familiarity (W : Type*)
    (situationType headNoun : W → Prop) :
    ∀ c ∈ palConstructicon.childrenOf "PAL",
      (palConstructicon.derivedField
          (figure5Pragmatics W situationType headNoun) c).map (·.presup)
        = some situationType := by
  intro c hc
  rw [pal_children] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

/-! ### Irreducibility -/

/-- The PAL construction is not fully compositional: pairing
phrase-in-a-word-slot form with a presumed-familiarity function is a
construction-specific pragmatic function, so PAL cannot be decomposed into
the three universal combination schemata (see `isFullyCompositional`). -/
theorem pal_irreducible :
    isFullyCompositional palConstruction = false := rfl

/-- The PAL modifier slot is a phrase in a word-level position — the typed
content of "phrase-as-lemma". The NN compound's modifier slot is the
minimal contrast: same zero-level position, word filler. -/
theorem pal_form_phrase_in_word_slot :
    ∃ s ∈ palConstruction.form, s.IsPhraseInWordSlot := by decide

/-! ### Attested tokens

PALs prototypically modify nouns but occur as head nouns, predicative adjectives, and verbs
(Table 2), and take the word-level inflection of the slot they fill (Table 3). -/

/-- The word-class slot a PAL fills. -/
inductive PALPosition where
  | prenominalModifier
  | headNoun
  | predicativeAdjective
  | verb
  deriving DecidableEq, Fintype

/-- Word-level inflection attested on a PAL. -/
inductive Inflection where
  | plural
  | agentivePlural
  | gerund
  deriving DecidableEq

/-- The slot whose inflection an affix is: nominal plural and agentive *-er*, verbal *-ing*. -/
def Inflection.position : Inflection → PALPosition
  | .plural | .agentivePlural => .headNoun
  | .gerund => .verb

/-- An attested English PAL: its slot and any inflection it carries. -/
structure Row where
  position : PALPosition
  inflection : Option Inflection
  deriving DecidableEq

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let position ← ex.parse? "position"
    [("prenominal modifier", .prenominalModifier), ("head noun", .headNoun),
     ("predicative adjective", .predicativeAdjective), ("verb", .verb)]
  pure ⟨position, ex.parse? "inflection"
    [("plural", .plural), ("agentive -er + plural", .agentivePlural), ("gerund", .gerund)]⟩

/-- The English tokens of (1a)–(1c), Table 2, and Table 3. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Table 2: PALs are attested in every word-class slot. -/
theorem rows_position : ∀ p : PALPosition, ∃ r ∈ rows, r.position = p := by decide

/-- Table 3: a PAL takes the inflection of the slot it fills. -/
theorem rows_inflection : ∀ r ∈ rows, ∀ i ∈ r.inflection, i.position = r.position := by decide

/-! ### Comparable constructions in other languages (section 7) -/

/-- The frame hosting a comparable construction: a compound(-like) frame in West Germanic and
Turkish, where the compound marker sits on the head noun, or the complement of a preposition in
Hebrew and Brazilian Portuguese. -/
inductive PALHostFrame where
  | compound
  | prepositionComplement
  deriving DecidableEq, Fintype

/-- The host frames of the German, Dutch, Afrikaans, Turkish, Hebrew, and Brazilian Portuguese
PALs of (8) and (15)–(18). -/
def hostFrames : List PALHostFrame :=
  Examples.all.filterMap λ ex => ex.parse? "hostFrame"
    [("compound", .compound), ("preposition complement", .prepositionComplement)]

example : rows.length + hostFrames.length = Examples.all.length := by decide

/-- A PAL need not resemble a compound; it need only fill a slot typical of single words, so both
host frames are attested. -/
theorem hostFrames_complete : ∀ f : PALHostFrame, f ∈ hostFrames := by decide

end GoldbergShirtz2025
