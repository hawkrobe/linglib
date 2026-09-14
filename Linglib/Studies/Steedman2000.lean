import Linglib.Data.Examples.Steedman2000
import Linglib.Fragments.English.Toy
import Linglib.Fragments.English.Coordination
import Linglib.Syntax.CCG.Derivation
import Linglib.Syntax.CCG.Grammar
import Linglib.Syntax.CCG.Interface
import Linglib.Syntax.CCG.Intonation
import Linglib.Studies.BeckmanPierrehumbert1986
import Linglib.Semantics.Composition.Scope

/-!
# Steedman (2000): The Syntactic Process

This file formalizes the analyses of [steedman-2000] over the library's combinatory
categorial grammar. Slash direction in lexical categories fixes word order and the
combinatory rules project it, so an English transitive clause is derived by application
alone (`mary_eats_pizza`). Type-raising and composition make a subject and a transitive verb
a constituent of category `S/NP`, so that non-constituent coordination is ordinary
coordination of like categories with the interpretation generalized conjunction gives, the
same truth conditions as the spelled-out paraphrase (`nonConstituentCoord_eq_spelledOut`),
and the coordinator's role rather than a rule of the grammar fixes the Boolean operation
(`coord_role_load_bearing`).

Gapping is argument-cluster coordination. The arguments of a transitive verb raise
order-preservingly over the functions that seek them and compose by the harmonic rules into
a cluster only when the verb seeks both in one direction (`cluster`): the cluster looks
rightward over a verb-final verb and leftward over a verb-initial one (`cluster_sov`,
`cluster_vso`), so verb-final languages gap backward and verb-initial ones forward, the
generalization of [ross-1970]. A verb-medial verb has no cluster (`cluster_svo`); English
gaps forward because the virtual-conjunct revealing rule decomposes the left conjunct into
a rightward function into `S` and a leftward residue, which is the cluster over a virtual
verb-initial verb (`RightwardInto`, `reveal`, `english_gap`), and Dutch, whose main-clause
verbs take their arguments rightward and subordinate-clause verbs leftward, gaps in both
directions (`dutch_main_cluster`, `dutch_sub_cluster`). Gapping and stripping are
syntactically mediated; VP ellipsis and sluicing are anaphoric (`SyntacticallyMediated`).

Dutch cross-serial dependencies follow from subordinate-clause verbs taking their NP
arguments leftward and their infinitival complements rightward, the cluster formed by
forward crossed composition (`three_np_sub_derives`), and word order in a verb cluster
decides quantifier scope: a cluster formed by composition is scope-ambiguous and an applied
one surface-only, matching the judgments of the book's examples
(`predictedAvailability_eq_observed`). Intonation disambiguates derivations: pitch accents
project theme and rheme through the categories they mark, and a theme accent and a rheme
accent do not unify, so the tune forces the phrasing "(ANNA married)(MANNY)"
(`theme_rheme_clash`, `annaMannyUtterance_infoStructure`). Derivations are interpreted
compositionally over the toy English model, with a true and a false sentence
(`ccg_predicts_john_sleeps`, `ccg_predicts_mary_sleeps`).

## Implementation notes

Type-raising is lexical in the substrate, so the book's syntactic raising rule appears as
raised lexical entries, and the order-preserving raising of an argument is computed at the
plain modality. The toy `Cat` drops the book's features (subordination, antecedent
government, agreement), so the Dutch fragment carries only the categories its derivations
use and the restriction of forward crossed composition to bare infinitival complements is
not encoded. The book's tunes follow Pierrehumbert's decomposition of an intonation phrase
into pitch accent, phrase accent and boundary tone, which [beckman-pierrehumbert-1986]
supplies (`ipToTune`).

## References

* [steedman-2000]
* [ross-1970]
* [bresnan-etal-1982]
* [bayer-1996]
* [kayne-1998]
* [haegeman-van-riemsdijk-1986]
* [haegeman-1992]
* [selkirk-1984]
* [partee-rooth-1983]
* [beckman-pierrehumbert-1986]
-/

namespace Steedman2000

open CCG

/-! ### Word order

Slash direction encodes word order: `TV = (S\NP)/NP` looks right for the object and the
resulting `S\NP` left for the subject, which enforces SVO. -/

def mary_eats_pizza : Derivation Atom S :=
  .bapp (.lex "Mary" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))

def john_sleeps : Derivation Atom S :=
  .bapp (.lex "John" NP) (.lex "sleeps" IV)

def john_sees_mary : Derivation Atom S :=
  .bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "Mary" NP))

/-! ### Non-constituent coordination -/

section Coordination

open Semantics.Montague Combinator

/-- The type-raised subject "John", `S/(S\NP)`, a lexical leaf. -/
def john_tr : Derivation Atom (S / (S \ NP)) := .lex "John" (S / (S \ NP))

def mary_tr : Derivation Atom (S / (S \ NP)) := .lex "Mary" (S / (S \ NP))

/-- "John sees": the type-raised subject composed with the transitive verb, a constituent of
category `S/NP`. -/
def john_sees : Derivation Atom (S / NP) := .fcomp (by decide) john_tr (.lex "sees" TV)

def mary_eats : Derivation Atom (S / NP) := .fcomp (by decide) mary_tr (.lex "eats" TV)

/-- The lexical conjunction coordinating constituents of category `c`: `(X \⋆ X) /⋆ X`, whose
`star` slashes confine it to application. -/
def conj (c : Cat Atom) : Cat Atom := (c \⋆ c) /⋆ c

/-- "John sees and Mary eats": coordination of two `S/NP` constituents through the lexical
conjunction, the book's "Anna married, and I detest". -/
def john_sees_and_mary_eats : Derivation Atom (S / NP) :=
  .bapp john_sees (.fapp (.lex "and" (conj (S / NP))) mary_eats)

def john_sees_and_mary_eats_pizza : Derivation Atom S :=
  .fapp john_sees_and_mary_eats (.lex "pizza" NP)

/-- The derivation spells out the full surface string, coordinator included. -/
theorem john_sees_and_mary_eats_pizza_yield :
    john_sees_and_mary_eats_pizza.yield = ["John", "sees", "and", "Mary", "eats", "pizza"] :=
  rfl

/-- The semantic lexicon over the toy English fragment: names, raised names, verbs, and the
lexical conjunctions at `S` and, by generalized conjunction ([partee-rooth-1983]), at `S/NP`. -/
def semLexicon : SemLexicon ToyEntity Unit := λ word cat =>
  match word, cat with
  | "John", .atom .NP => some ToyEntity.john
  | "Mary", .atom .NP => some ToyEntity.mary
  | "pizza", .atom .NP => some ToyEntity.pizza
  | "book", .atom .NP => some ToyEntity.book
  | "John", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (T ToyEntity.john)
  | "Mary", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (T ToyEntity.mary)
  | "sleeps", .lslash (.atom .S) _ (.atom .NP) => some ToyLexicon.sleeps_sem
  | "laughs", .lslash (.atom .S) _ (.atom .NP) => some ToyLexicon.laughs_sem
  | "sees", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.sees_sem
  | "eats", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.eats_sem
  | "reads", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.reads_sem
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (λ q p => p ∧ q)
  | "and", .rslash (.lslash (.rslash (.atom .S) _ (.atom .NP)) _
        (.rslash (.atom .S) _ (.atom .NP))) _ (.rslash (.atom .S) _ (.atom .NP)) =>
      some (λ q p x => p x ∧ q x)
  | _, _ => none

/-- "John sees Mary" with a type-raised subject produces the same truth value as the
canonical derivation. -/
def john_sees_mary_via_tr : Derivation Atom S :=
  .fapp john_tr (.fapp (.lex "sees" TV) (.lex "Mary" NP))

theorem interp_john_sees_mary_via_tr :
    john_sees_mary_via_tr.interp semLexicon = john_sees_mary.interp semLexicon := rfl

/-- Generalized conjunction delivers the conjunctive interpretation: the coordinated `S/NP`
predicate at an entity is the conjunction of the two predicates at it. -/
theorem coord_interp_pointwise (e : ToyEntity) :
    (john_sees_and_mary_eats.interp semLexicon).map (· e) =
      (match john_sees.interp semLexicon, mary_eats.interp semLexicon with
        | some m₁, some m₂ => some (m₁ e ∧ m₂ e)
        | _, _ => none) := rfl

/-- The spelled-out paraphrase "John sees pizza and Mary eats pizza". -/
def john_sees_pizza_and_mary_eats_pizza : Derivation Atom S :=
  .bapp (.bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "pizza" NP)))
    (.fapp (.lex "and" (conj S))
      (.bapp (.lex "Mary" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))))

/-- The non-constituent coordination and its spelled-out paraphrase receive the same truth
conditions: the composed derivation yields the canonical predicate-argument structure. -/
theorem nonConstituentCoord_eq_spelledOut :
    john_sees_and_mary_eats_pizza.interp semLexicon =
      john_sees_pizza_and_mary_eats_pizza.interp semLexicon := rfl

/-- A lexicon in which sentence `p` is true and `q` false, with the English coordinators
interpreted by the Boolean operation of their role. -/
private def pqLex : SemLexicon Unit Unit := λ w c =>
  match w, c with
  | "p", .atom .S => some True
  | "q", .atom .S => some False
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        λ q p => Coordinator.op English.Coordination.and_.role p q)
  | "or", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        λ q p => Coordinator.op English.Coordination.or_.role p q)
  | _, _ => none

private def dp : Derivation Atom S := .lex "p" S
private def dq : Derivation Atom S := .lex "q" S

/-- Which coordinator a derivation uses is part of its truth conditions: with a true and a
false conjunct, `and` and `or` differ. -/
theorem coord_role_load_bearing :
    (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex ≠
    (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex := by
  have hand : (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex
      = some (True ∧ False) := rfl
  have hor : (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex
      = some (True ∨ False) := rfl
  rw [hand, hor, ne_eq, Option.some.injEq, eq_iff_iff]
  exact λ h => (h.mpr (Or.inl trivial)).2

end Coordination

/-! ### Gapping -/

section Gapping

/-- Order-preserving type-raising of the argument of a function category over it: the
argument of `X\A` raises to `X/(X\A)` and that of `X/A` to `X\(X/A)`. -/
def raiseArg : Cat Atom → Option (Cat Atom)
  | .lslash x _ a => some (Cat.forwardTypeRaise a x)
  | .rslash x _ a => some (Cat.backwardTypeRaise a x)
  | .atom _ => none

/-- Harmonic composition, the order-preserving rules `>B` and `<B`. -/
def hcomp : Cat Atom → Cat Atom → Option (Cat Atom)
  | .rslash x _ y, .rslash y' n z => if y = y' then some (.rslash x n z) else none
  | .lslash y' n z, .lslash x _ y => if y = y' then some (.lslash x n z) else none
  | _, _ => none

/-- The argument cluster over a transitive verb category: the verb's two arguments raised
over the functions that seek them and composed harmonically, in whichever order the rules
allow. -/
def cluster (v : Cat Atom) : Option (Cat Atom) :=
  match v with
  | .lslash inner _ _ | .rslash inner _ _ => do
      let r₁ ← raiseArg inner
      let r₂ ← raiseArg v
      hcomp r₁ r₂ <|> hcomp r₂ r₁
  | .atom _ => none

/-- The verb-final transitive verb of Japanese, `(S\NP)\NP`. -/
def japaneseTV : Cat Atom := (S \ NP) \ NP

/-- The verb-initial transitive verb of Irish, `(S/NP)/NP`. -/
def irishTV : Cat Atom := (S / NP) / NP

/-- Over a verb-final verb the cluster looks rightward for the verb: the arguments raise
forward and compose forward, so the verb follows the coordinated clusters, backward gapping
(the book's chapter 7 (4)). -/
theorem cluster_sov : cluster japaneseTV = some (S / japaneseTV) := by decide

/-- Over a verb-initial verb the cluster looks leftward, so the verb precedes the clusters,
forward gapping (chapter 7 (19)). -/
theorem cluster_vso : cluster irishTV = some (S \ irishTV) := by decide

/-- A verb-medial verb has no cluster: its arguments raise in opposite directions and no
harmonic rule composes them. -/
theorem cluster_svo : cluster TV = none := by decide

/-- The backward-gapped conjunct "Ken-ga Naomi-o" as a derivation: forward raising and
forward composition. -/
def backwardGappedConjunct : Derivation Atom (S / japaneseTV) :=
  .fcomp (by decide) (.lex "Ken-ga" (S / (S \ NP)))
    (.lex "Naomi-o" ((S \ NP) / japaneseTV))

theorem backwardGappedConjunct_yield :
    backwardGappedConjunct.yield = ["Ken-ga", "Naomi-o"] := rfl

/-- The forward-gapped conjunct "Warren, potatoes" as a derivation: backward raising and
backward composition over a verb-initial verb. -/
def gappedConjunct : Derivation Atom (S \ irishTV) :=
  .bcomp (by decide) (.lex "Warren" ((S / NP) \ irishTV)) (.lex "potatoes" (S \ (S / NP)))

theorem gappedConjunct_yield : gappedConjunct.yield = ["Warren", "potatoes"] := rfl

/-- `RightwardInto t c`: `c` is a rightward function into `t`, the book's `t/$`. -/
def RightwardInto (t : Cat Atom) : Cat Atom → Prop
  | .rslash x _ _ => RightwardInto t x
  | .lslash x m y => Cat.lslash x m y = t
  | .atom a => Cat.atom a = t

/-- Decidability of `RightwardInto t`, by recursion on the category. -/
def RightwardInto.decidable (t : Cat Atom) : ∀ c, Decidable (RightwardInto t c)
  | .rslash x _ _ => RightwardInto.decidable t x
  | .lslash x m y => inferInstanceAs (Decidable (Cat.lslash x m y = t))
  | .atom a => inferInstanceAs (Decidable (Cat.atom a = t))

instance (t : Cat Atom) : DecidablePred (RightwardInto t) := RightwardInto.decidable t

/-- The virtual-conjunct revealing rule (chapter 7 (61)): a left conjunct of category `x`
decomposes into a rightward function `y` into `S` and the residue `x \ y`, so the residue
looks leftward whatever `y` is. -/
def reveal (x y : Cat Atom) : Cat Atom × Cat Atom := (y, x \ y)

/-- English gapping (chapter 7 (62)): the left conjunct reveals a virtual verb-initial verb
and a residue that is the cluster over it, with which the gapped right conjunct coordinates;
no verb-final verb can be revealed, so English gaps forward only. -/
theorem english_gap :
    RightwardInto S irishTV ∧ (reveal S irishTV).2 = (S \ irishTV) ∧
      cluster irishTV = some (S \ irishTV) ∧ ¬ RightwardInto S japaneseTV := by
  decide

/-- Dutch main-clause transitive verbs take both arguments rightward, so main clauses gap
forward (chapter 7 (21)). -/
theorem dutch_main_cluster : cluster ((S / NP) / NP) = some (S \ ((S / NP) / NP)) := by
  decide

/-- Dutch subordinate-clause transitive verbs take both arguments leftward, so subordinate
clauses gap backward (chapter 7 (11)). -/
theorem dutch_sub_cluster : cluster ((S \ NP) \ NP) = some (S / ((S \ NP) \ NP)) := by
  decide

/-- Stripping is the single-remnant case: one backward-raised subject, `S\(S/NP)`. -/
def strippedConjunct : Derivation Atom (S \ (S / NP)) := .lex "Warren" (S \ (S / NP))

/-- The book's taxonomy of elliptical constructions. -/
inductive EllipsisType
  /-- "Dexter ate bread, and Warren, potatoes" -/
  | gapping
  /-- "Dexter ran away, and Warren (too)" -/
  | stripping
  /-- "Dexter ate bread, and Warren did too" -/
  | vpEllipsis
  /-- "Dexter did something, but I don't know what" -/
  | sluicing
  deriving DecidableEq, Repr

/-- Gapping and stripping are mediated by the combinatory syntax; VP ellipsis and sluicing
by a separate anaphoric mechanism, since their categories are not otherwise in the grammar. -/
def SyntacticallyMediated : EllipsisType → Prop
  | .gapping | .stripping => True
  | .vpEllipsis | .sluicing => False

instance : DecidablePred SyntacticallyMediated := λ x => by
  cases x <;> unfold SyntacticallyMediated <;> infer_instance

end Gapping

/-! ### Cross-serial dependencies

Dutch verb clusters ([bresnan-etal-1982]) over a target-restricted grammar: subordinate-clause
verbs take NP arguments leftward and infinitival complements rightward, and the cluster forms
by forward crossed composition, so the NPs precede the whole cluster in the attested order
"Jan Piet (Marie) zag (helpen) zwemmen". -/

section CrossSerial

/-- Infinitival verb phrase. -/
def VP : Cat Atom := S \ NP

/-- Subordinate-clause perception verb `((S\NP)\NP)/VP`: infinitival complement to the right,
object and subject to the left. -/
def PercVSub : Cat Atom := ((S \ NP) \ NP) / VP

/-- Infinitival head with a raised object, `(VP\NP)/VP`. -/
def InfHeadSub : Cat Atom := (VP \ NP) / VP

/-- The Dutch fragment as a target-restricted grammar with target `S` and degree bound 2. -/
def dutchGrammar : Grammar Atom :=
  .targetRestricted
    [("Jan", NP), ("Piet", NP), ("Marie", NP), ("zag", PercVSub), ("helpen", InfHeadSub),
     ("zwemmen", VP)]
    .S 2

theorem jan_derives : dutchGrammar.Derives NP ["Jan"] := .lex (by decide)
theorem piet_derives : dutchGrammar.Derives NP ["Piet"] := .lex (by decide)
theorem marie_derives : dutchGrammar.Derives NP ["Marie"] := .lex (by decide)
theorem zag_derives : dutchGrammar.Derives PercVSub ["zag"] := .lex (by decide)
theorem helpen_derives : dutchGrammar.Derives InfHeadSub ["helpen"] := .lex (by decide)
theorem zwemmen_derives : dutchGrammar.Derives VP ["zwemmen"] := .lex (by decide)

/-- The crossed cluster "zag helpen zwemmen" is a leftward-seeking three-place predicate. -/
theorem crossed_cluster_derives :
    dutchGrammar.Derives (((S \ NP) \ NP) \ NP) ["zag", "helpen", "zwemmen"] :=
  .fc 1 zag_derives (.fc 0 helpen_derives zwemmen_derives ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- "(dat) Jan Piet zag zwemmen": the two-verb cluster needs no composition and the NPs
attach leftward. -/
theorem two_np_sub_derives : dutchGrammar.Derives S ["Jan", "Piet", "zag", "zwemmen"] :=
  .bc 0 jan_derives
    (.bc 0 piet_derives (.fc 0 zag_derives zwemmen_derives ⟨by decide, rfl⟩ rfl)
      ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- "(dat) Jan Piet Marie zag helpen zwemmen": the three NPs attach leftward to the crossed
cluster, Marie to the slot of "helpen", Piet to the object slot of "zag", Jan as subject, the
cross-serial binding in the attested order. -/
theorem three_np_sub_derives :
    dutchGrammar.Derives S ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"] :=
  .bc 0 jan_derives
    (.bc 0 piet_derives (.bc 0 marie_derives crossed_cluster_derives ⟨by decide, rfl⟩ rfl)
      ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

end CrossSerial

/-! ### Verb clusters and quantifier scope

In the verb-raising order the cluster forms by composition, so a quantified argument combines
with a function containing the tensed verb and can take scope over it; in the
verb-projection-raising order it combines with the embedded verb alone. -/

section Quantification

open Semantics.Scope Data.Examples

/-- Word order in a West Germanic verb cluster. -/
inductive VerbOrder
  /-- Object precedes the whole verb cluster. -/
  | verbRaising
  /-- Object follows the matrix verb. -/
  | verbProjectionRaising
  deriving DecidableEq, Repr, Inhabited

/-- Verb-raising order, Dutch (99a): the cluster "probeert te zingen" forms by crossed
composition before taking the object to its left. -/
def verbRaisingDeriv : Derivation Atom IV :=
  .bapp (.lex "veel liederen" NP)
    (.fcompx (by decide) (.lex "probeert" (IV / IV)) (.lex "te zingen" (IV \ NP)))

/-- Verb-projection-raising order, Dutch (99b): the matrix verb applies to a saturated
embedded VP, so the quantified object never combines with a function containing the tensed
verb. -/
def verbProjectionRaisingDeriv : Derivation Atom IV :=
  .fapp (.lex "probeert" (IV / IV))
    (.bapp (.lex "veel liederen" NP) (.lex "te zingen" (IV \ NP)))

/-- The derivation shape each verb order forces. -/
def schematicDeriv : VerbOrder → Derivation Atom IV
  | .verbRaising => verbRaisingDeriv
  | .verbProjectionRaising => verbProjectionRaisingDeriv

theorem verbRaisingDeriv_hasComp : verbRaisingDeriv.HasComp := by decide

theorem verbProjectionRaisingDeriv_applicationOnly :
    ¬verbProjectionRaisingDeriv.HasComp := by decide

/-- Scope availability as the account predicts it: a cluster built with composition is
scope-ambiguous, an application-only cluster surface-only. -/
def predictedAvailability (vo : VerbOrder) : BinaryScopeAvailability :=
  if (schematicDeriv vo).HasComp then .ambiguous else .surfaceOnly

/-- The word-order classification of an example. -/
def wordOrderOf (ex : LinguisticExample) : Option VerbOrder :=
  match ex.paperFeatures.lookup "wordOrder" with
  | some "verbRaising" => some .verbRaising
  | some "verbProjectionRaising" => some .verbProjectionRaising
  | _ => none

/-- The observed availability: the judgment on the example's inverse reading. -/
def observedAvailability (ex : LinguisticExample) : Option BinaryScopeAvailability :=
  match ex.readings.lookup "inverse" with
  | some .acceptable => some .ambiguous
  | some .unacceptable => some .surfaceOnly
  | _ => none

/-- The scope examples as pairs of word order and observed availability. -/
def scopeData : List (VerbOrder × BinaryScopeAvailability) :=
  Examples.all.filterMap λ ex =>
    (wordOrderOf ex).bind λ vo => (observedAvailability ex).map λ av => (vo, av)

/-- The prediction matches every judgment of the book's examples (96) to (100), credited in
the data to [bayer-1996], [kayne-1998], [haegeman-van-riemsdijk-1986] and [haegeman-1992]. -/
theorem predictedAvailability_eq_observed :
    ∀ d ∈ scopeData, predictedAvailability d.1 = d.2 := by
  decide

end Quantification

/-! ### Intonation and information structure

Alternative derivations of one string are alternative information structures, disambiguated
by tune: "(ANNA married)(MANNY)" carves the composed derivation into a theme and a rheme, and
prosodic phrases are tune-marked constituents, so only constituents of the grammar can be
phrases, the Sense Unit Condition of [selkirk-1984]. -/

section Intonation

open CCG.Intonation Prosody

/-- Accents for "(ANNA married)(MANNY)": theme accent on "Anna", rheme accent on "Manny",
"married" unaccented. -/
def annaMannyAccents : AccentAssignment := λ w =>
  match w with
  | "Anna" => .L_plus_H_star
  | "Manny" => .H_star
  | _ => .null

/-- "ANNA married": the composed theme constituent, category `S/NP`. -/
def anna_married : Derivation Atom (S / NP) :=
  .fcomp (by decide) (.lex "Anna" (S / (S \ NP))) (.lex "married" TV)

/-- The theme constituent projects `θ`: the theme accent on "Anna" unifies with unaccented
"married". -/
theorem anna_married_theme :
    anna_married.infoFeature annaMannyAccents = some .θ := rfl

/-- The rheme "MANNY" projects `ρ`. -/
theorem manny_rheme :
    (Derivation.lex "Manny" NP).infoFeature annaMannyAccents = some .ρ := rfl

/-- Folding the rheme into the theme's constituent clashes: the whole sentence projects no
single marking, so the tune forces the phrasing "[Anna married][Manny]". -/
theorem theme_rheme_clash :
    (Derivation.fapp anna_married (.lex "Manny" NP)).infoFeature annaMannyAccents
      = none := rfl

/-- The utterance as two tune-marked phrases. -/
def annaMannyUtterance : List ProsodicPhrase :=
  [⟨_, anna_married, themeTune⟩, ⟨_, .lex "Manny" NP, rhemeTune⟩]

/-- The extracted information structure: the theme is the `S/NP` constituent "ANNA married",
the rheme "MANNY". -/
theorem annaMannyUtterance_infoStructure :
    (extractInfoStructure annaMannyUtterance).map (λ i => (i.theme.map (·.cat), i.rheme.cat))
      = some (some (S / NP), NP) := rfl

end Intonation

/-! ### Truth conditions

Derivations interpreted compositionally over the toy model: a true sentence and a false one. -/

section TruthConditions

def mary_sleeps : Derivation Atom S := .bapp (.lex "Mary" NP) (.lex "sleeps" IV)

theorem ccg_predicts_john_sleeps : john_sleeps.interp semLexicon = some True := rfl

theorem ccg_predicts_mary_sleeps : mary_sleeps.interp semLexicon = some False := rfl

theorem ccg_predicts_john_sees_mary : john_sees_mary.interp semLexicon = some True := rfl

end TruthConditions

/-! ### The tune terminal as an intonation-phrase terminal -/

section BPTerminal

open Prosody BeckmanPierrehumbert1986 CCG.Intonation

/-- A tune from an intonation phrase of [beckman-pierrehumbert-1986] and a pitch accent: the
tune's terminal contour is the phrase's final phrase accent and boundary tone. -/
def ipToTune (ip : IntonationPhrase) (accent : PitchAccent) : Tune :=
  ⟨accent, ip.terminalContour⟩

theorem ipToTune_terminal (ip : IntonationPhrase) (accent : PitchAccent) :
    (ipToTune ip accent).terminal = ip.terminalContour := rfl

/-- A declarative intonation phrase, L phrase accent and L% boundary. -/
def declarativeIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .L_pct }

/-- A continuation-rise intonation phrase, L phrase accent and H% boundary. -/
def continuationIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .H_pct }

/-- The declarative phrase carries the rheme tune's terminal and the continuation-rise phrase
the theme tune's. -/
theorem bp_terminals_match_tunes :
    declarativeIP.terminalContour = rhemeTune.terminal ∧
      continuationIP.terminalContour = themeTune.terminal := by decide

end BPTerminal

end Steedman2000
