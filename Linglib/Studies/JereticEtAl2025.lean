import Linglib.Data.Examples.JereticEtAl2025
import Linglib.Syntax.Tree.Cat
import Linglib.Semantics.Alternatives.Source
import Linglib.Semantics.Alternatives.Competition
import Linglib.Semantics.Alternatives.Structural
import Linglib.Fragments.Romance.French.Determiners
import Linglib.Fragments.English.Determiners
import Mathlib.Tactic.DeriveFintype

/-!
# Jeretič et al. (2025): Core concepts and indirect alternatives

This file formalizes [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]'s account of the
anti-duality of French *tous*. English *all* and *every* are unusable in a domain known to hold
two individuals because Maximize Presupposition prefers *both* ([percus-2006],
[sauerland-2008]); *tous* is anti-dual too although French has no word for *both*, the puzzle
of [chemla-2007] taken by [buccola-kriz-chemla-2018] to show a conceptual alternative at work.
The account posits a dual number feature in every language, syncretic with the plural in
French, so that the string *tous les NP* is ambiguous between a plural and a dual parse; Avoid
Ambiguity (`Blocked`) bars the dual parse from pronunciation because *les deux NP* realizes its
meaning at no greater node count, and that expression, an indirect alternative in the sense of
the substrate's `Alternatives.indirectFrom`, licenses the Maximize Presupposition competition
the silent parse cannot enter on its own. The worked example runs this on (25): the dual parse
is blocked, pronounceability is thereby derived rather than stipulated, and *tous* violates
Maximize Presupposition through *les deux* (`tous_blocked_via_indirect`).

Across languages and quantifier slots a plain quantifier is predicted anti-dual exactly when a
dual competitor exists, a lexical dual item or a pronounceable dual expression at most as
complex as the plain one, which `Slot.competitor` derives from the paper's forms and their
node counts; `theory_matches_data` checks the prediction against the judgments the paper
reports, as rows: English *no* and *always* anti-dual, French *aucun* and *toujours* not,
Japanese *which*, *each*, and *one* anti-dual by the lexical dual *dotti* where English and
French are not. An account with direct alternatives only, [sauerland-2003]'s, predicts
anti-duality from lexical duals alone and so misses the indirect cells. The combination *tous
les deux*, the domain restriction of Avoid Ambiguity, and the alternatives the paper rejects
are not formalized.

## Implementation notes

* Node counts follow the paper: three heads each for *tous les NP* and *les deux NP* (38),
  two morphemes for *always* as *all* plus *ways*, for *toujours*, for suppletive *immer*, for
  *itu-mo*, and for *ni-kai*, four for *ni-kai-to-mo* and the English partitives, three for
  the French partitives; where the paper names no dual expression the list is empty.
* The English lexical duals are read from the fragment, their lexical status being their dual
  number restriction; French *les deux* is the fragment's entry, a two-word expression.

## References

* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
* [chemla-2007]
* [buccola-kriz-chemla-2018]
* [percus-2006]
* [sauerland-2008]
* [sauerland-2003]
-/

namespace JereticEtAl2025

open Data.Examples

/-! ### The typology -/

/-- The languages with reported judgments. -/
inductive Language where
  | english
  | french
  | german
  | japanese
  | icelandic
  deriving DecidableEq, Repr

/-- The quantifier slots: universal, negative, interrogative, distributive, existential, and
the temporal universal *always*. -/
inductive QSlot where
  | universal
  | negative
  | which
  | each
  | one
  | always
  deriving DecidableEq, Repr

/-- A dual expression a language offers for a slot: its form, whether it is a single lexical
item, and its node count. -/
structure DualForm where
  form : String
  lexical : Bool
  size : ℕ
  deriving DecidableEq, Repr

/-- A lexical dual item of a fragment: a quantifier whose number restriction is the dual. -/
def lexicalDual (form : String) (restriction : Option Number) : DualForm :=
  ⟨form, decide (restriction = some .dual), 1⟩

/-- The plain expression of a slot with its node count and the dual expressions the language
offers for it. -/
structure Slot where
  plain : String
  size : ℕ
  duals : List DualForm
  deriving DecidableEq, Repr

/-- The dual competitor a slot provides: a lexical dual item, the standard Maximize
Presupposition competitor; or a pronounceable dual expression at most as complex as the plain
one, which blocks the silent dual parse and stands in for it as an indirect alternative; or
nothing simple enough. -/
inductive Competitor where
  | lexicalDual
  | indirect
  | none
  deriving DecidableEq, Repr

/-- The competitor a slot provides, from its dual expressions. -/
def Slot.competitor (s : Slot) : Competitor :=
  if s.duals.any (·.lexical) then .lexicalDual
  else if s.duals.any (·.size ≤ s.size) then .indirect
  else .none

/-- The paper's cells: the plain expression, its node count, and the dual expressions of the
language with their counts. -/
def typology : Language → QSlot → Option Slot
  | .english, .universal =>
    some ⟨"all", 1, [lexicalDual English.Determiners.both.form
      English.Determiners.both.numberRestriction]⟩
  | .english, .negative =>
    some ⟨"no", 1, [lexicalDual English.Determiners.neither.form
      English.Determiners.neither.numberRestriction]⟩
  | .english, .which => some ⟨"which", 1, [⟨"which of the two", false, 4⟩]⟩
  | .english, .each => some ⟨"each", 1, [⟨"each of the two", false, 4⟩]⟩
  | .english, .one => some ⟨"one", 1, [⟨"one of the two", false, 4⟩]⟩
  | .english, .always => some ⟨"always", 2, [⟨"both times", false, 2⟩]⟩
  | .french, .universal =>
    some ⟨"tous les", 3, [⟨French.Determiners.les_deux.form, false, 3⟩]⟩
  | .french, .negative =>
    some ⟨"aucun", 1, [⟨"aucun des deux", false, 3⟩, ⟨"ni l'un ni l'autre", false, 5⟩]⟩
  | .french, .which => some ⟨"quel", 1, []⟩
  | .french, .each => some ⟨"chaque", 1, []⟩
  | .french, .one => some ⟨"un", 1, []⟩
  | .french, .always => some ⟨"toujours", 2, [⟨"les deux fois", false, 3⟩]⟩
  | .german, .negative => some ⟨"keine", 1, []⟩
  | .german, .always => some ⟨"immer", 2, [⟨"beide Male", false, 2⟩]⟩
  | .japanese, .which => some ⟨"dono", 1, [⟨"dotti", true, 1⟩]⟩
  | .japanese, .each => some ⟨"dono ... mo", 1, [⟨"dotti ... mo", true, 1⟩]⟩
  | .japanese, .one => some ⟨"dono ... ka", 1, [⟨"dotti ... ka", true, 1⟩]⟩
  | .japanese, .always =>
    some ⟨"itu-mo", 2, [⟨"ni-kai", false, 2⟩, ⟨"ni-kai-to-mo", false, 4⟩]⟩
  | .icelandic, .which => some ⟨"hvaða", 1, [⟨"hvor", true, 1⟩]⟩
  | _, _ => none

/-- The headline contrast: English *all* and French *tous* are anti-dual by different routes,
a lexical dual and an indirect alternative. -/
theorem universal_competitors :
    (typology .english .universal).map Slot.competitor = some .lexicalDual ∧
      (typology .french .universal).map Slot.competitor = some .indirect := by
  decide

/-! ### The judgments -/

/-- A reported judgment on a plain quantifier: its language, its slot, and whether it is
anti-dual, degraded in a domain of two. -/
def cellRow (r : LinguisticExample) : Option (Language × QSlot × Bool) := do
  let l ← r.parse? "language" [("english", Language.english), ("french", .french),
    ("german", .german), ("japanese", .japanese), ("icelandic", .icelandic)]
  let q ← r.parse? "slot" [("universal", QSlot.universal), ("negative", .negative),
    ("which", .which), ("each", .each), ("one", .one), ("always", .always)]
  let dual ← r.parse? "dual" [("true", true), ("false", false)]
  if dual then none else pure (l, q, decide (r.judgment ≠ .acceptable))

/-- The paper's judgments on plain quantifiers in a domain of two. -/
def cells : List (Language × QSlot × Bool) := Examples.all.filterMap cellRow

/-- On every reported cell a plain quantifier is anti-dual exactly when its slot provides a
competitor. -/
theorem theory_matches_data :
    ∀ c ∈ cells, ∀ s ∈ typology c.1 c.2.1, (s.competitor ≠ .none ↔ c.2.2 = true) := by
  decide +kernel

/-- An account with direct alternatives only predicts anti-duality from lexical duals alone,
so it misses the cells whose competitor is indirect, where the paper finds anti-duality. -/
theorem direct_account_misses_indirect :
    ∀ c ∈ cells, ∀ s ∈ typology c.1 c.2.1, s.competitor = .indirect → c.2.2 = true := by
  decide +kernel

/-! ### Avoid Ambiguity

(37): if a string is ambiguous between two parses and a string at most as complex realizes
the meaning of the first parse but has no parse equivalent to the second, the string cannot
realize the first parse; complexity is node count (38). The paper restricts the principle's
domain of application; `Blocked` is the unrestricted (37). -/

section AvoidAmbiguity

variable {S P M : Type*}

/-- A string is ambiguous iff it has two parses with distinct meanings. -/
def IsAmbiguous (parses : S → List P) (meaning : P → M) (s : S) : Prop :=
  ∃ p₁ ∈ parses s, ∃ p₂ ∈ parses s, meaning p₁ ≠ meaning p₂

/-- Avoid Ambiguity (37): `s` cannot realize its parse `p₁` when `s` is ambiguous between `p₁`
and some `p₂`, and a string `s'` at most as complex realizes `p₁`'s meaning but has no parse
equivalent to `p₂`. -/
def Blocked (parses : S → List P) (meaning : P → M) (size : S → Nat)
    (s : S) (p₁ : P) : Prop :=
  p₁ ∈ parses s ∧
  ∃ p₂ ∈ parses s, meaning p₂ ≠ meaning p₁ ∧
    ∃ s' : S, size s' ≤ size s ∧
      (∃ p₁' ∈ parses s', meaning p₁' = meaning p₁) ∧
      ∀ p₂' ∈ parses s', meaning p₂' ≠ meaning p₂

variable {parses : S → List P} {meaning : P → M} {size : S → Nat}
  {s : S} {p₁ : P}

/-- Only ambiguous strings block: unambiguous synonyms never compete under Avoid
Ambiguity. -/
theorem Blocked.isAmbiguous (h : Blocked parses meaning size s p₁) :
    IsAmbiguous parses meaning s :=
  let ⟨h₁, p₂, h₂, hne, _⟩ := h
  ⟨p₂, h₂, p₁, h₁, hne⟩

instance [DecidableEq P] [DecidableEq M] [Fintype S] :
    Decidable (Blocked parses meaning size s p₁) := by
  unfold Blocked; infer_instance

end AvoidAmbiguity

/-! ### The worked example (25)

*Tous les verres sont pleins* against *les deux verres sont pleins*, collapsed to head
structure: *tous V*, *les deux V*, and the silent witness *tous_DUAL V*. Trees are shallow,
one NP over two terminals, so every step is a `decide` or one Katzir substitution. -/

section WorkedExample

open Syntax
open Alternatives Alternatives.Structural

/-- Two evaluation contexts: a domain of two cups and a domain of three; the dual
presupposition is satisfied only in the first. -/
inductive WorldEx where
  | w2
  | w3
  deriving DecidableEq, Repr, Fintype

/-- The universal *tous*. -/
def tousLex : Tree Cat String := .terminal .Det "tous"

/-- The silent dual-bearing realization of *tous*, of the same category and so
Katzir-substitutable for `tousLex`. -/
def tousDualLex : Tree Cat String := .terminal .Det "tous_DUAL"

/-- The indirect alternative *les deux*, a portmanteau determiner for minimality. -/
def lesDeuxLex : Tree Cat String := .terminal .Det "les_deux"

/-- The common noun *verres*. -/
def verresLex : Tree Cat String := .terminal .N "verres"

/-- The lexicon of the worked example. -/
def frenchLex : List (Tree Cat String) := [tousLex, tousDualLex, lesDeuxLex, verresLex]

/-- *tous V*, the surface universal. -/
def tousVerres : Tree Cat String := .node .NP [tousLex, verresLex]

/-- *tous_DUAL V*, the silent witness, one Katzir substitution from `tousVerres` at the same
size. -/
def tousDualVerres : Tree Cat String := .node .NP [tousDualLex, verresLex]

/-- *les deux V*, the indirect alternative, of the same size as `tousVerres`. -/
def lesDeuxVerres : Tree Cat String := .node .NP [lesDeuxLex, verresLex]

/-- Whether a tree contains the silent dual marker. -/
def hasDualMarker (t : Tree Cat String) : Bool :=
  t.subtrees.any λ s => match s with
    | .terminal _ "tous_DUAL" => true
    | _ => false

/-- Whether a tree contains *les deux*. -/
def hasLesDeux (t : Tree Cat String) : Bool :=
  t.subtrees.any λ s => match s with
    | .terminal _ "les_deux" => true
    | _ => false

/-- French pronounceability: trees containing the silent dual marker are silent. Stipulated
here and derived from Avoid Ambiguity in `frenchPron_iff_not_blocked`. -/
abbrev frenchPron : Tree Cat String → Prop := λ t => hasDualMarker t = false

/-- The toy semantics: *tous V* asserts that all cups are full with a trivial presupposition;
the dual variants, silent or *les deux*, presuppose exactly two cups and are defined only in
the two-cup domain. -/
def meaning (t : Tree Cat String) (w : WorldEx) : Bool :=
  if hasDualMarker t || hasLesDeux t then
    match w with | .w2 => true | .w3 => false
  else
    true

/-- The two surface strings of (25). -/
inductive Str where
  | tousV
  | lesDeuxV
  deriving DecidableEq, Fintype

/-- The parses of each string: *tous les verres* is ambiguous between the plural and the dual
parse by syncretism; *les deux verres* is unambiguous. -/
def strParses : Str → List (Tree Cat String)
  | .tousV => [tousVerres, tousDualVerres]
  | .lesDeuxV => [lesDeuxVerres]

/-- String complexity: the maximal node count over the string's parses, uniform here. -/
def strSize (s : Str) : Nat := ((strParses s).map Tree.size).foldr max 0

/-- The dual parse of *tous les verres* is blocked by (37), witnessed by *les deux verres*. -/
theorem tousDual_blocked : Blocked strParses meaning strSize .tousV tousDualVerres := by
  decide

/-- The plural parse survives: *les deux verres* does not realize the plural meaning, and no
other string is simple enough. -/
theorem tousPl_not_blocked : ¬ Blocked strParses meaning strSize .tousV tousVerres := by
  decide

/-- Pronounceability is Avoid Ambiguity: on the strings of the example a parse is pronounceable
iff (37) does not block it, which derives the predicate the indirect-alternative source
consumes. -/
theorem frenchPron_iff_not_blocked :
    ∀ st : Str, ∀ p ∈ strParses st, (frenchPron p ↔ ¬ Blocked strParses meaning strSize st p) := by
  decide

/-- The presupposition, definedness of the sentence, `meaning` lifted to `Prop`. -/
def presupFn : Tree Cat String → WorldEx → Prop := λ t w => meaning t w = true

/-- The at-issue assertion, uniform across the three sentences, which differ only in
presupposition. -/
def assertionFn : Tree Cat String → WorldEx → Prop := λ _ _ => True

/-- The indirect-alternative source (43): Katzir alternatives filtered by pronounceability and
meaning-equivalence to a silent witness, complexity measured by `Tree.size`. -/
def frenchIndirectSrc : Tree Cat String → Set (Tree Cat String) :=
  indirectFrom (katzirSource frenchLex) frenchPron meaning Tree.size

/-- *tous_DUAL V* is a Katzir alternative of *tous V*, by substituting the dual determiner. -/
theorem tousDual_katzir_alt : tousDualVerres ∈ katzirSource frenchLex tousVerres := by
  apply Relation.ReflTransGen.single
  refine StructOp.inChild (cs := [tousLex, verresLex]) ⟨0, by decide⟩
    (StructOp.subst (φ := tousLex) (ψ := tousDualLex) rfl ?_)
  show tousDualLex ∈ frenchLex ++ tousVerres.subtrees
  refine List.mem_append_left _ (List.mem_cons_of_mem _ ?_)
  exact List.mem_cons_self

/-- *les deux V* is in the indirect-alternative source of *tous V*, witnessed by the silent
*tous_DUAL V* (43). -/
theorem lesDeux_indirectAlt_tous : lesDeuxVerres ∈ frenchIndirectSrc tousVerres := by
  refine ⟨by decide, by decide, tousDualVerres, tousDual_katzir_alt, by decide, ?_⟩
  funext w; cases w <;> rfl

/-- *tous V* violates Maximize Presupposition through the indirect alternative *les deux V*,
licensed by the silent witness: the paper's derivation of the anti-duality of *tous*. -/
theorem tous_blocked_via_indirect :
    Alternatives.Blocked (sameAssertion assertionFn frenchIndirectSrc) presupFn tousVerres := by
  refine ⟨lesDeuxVerres, ⟨lesDeux_indirectAlt_tous, rfl⟩,
    LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨WorldEx.w3, ?_, ?_⟩)⟩
  · intro w _
    show meaning tousVerres w = true
    cases w <;> rfl
  · show meaning tousVerres .w3 = true; rfl
  · show ¬ (meaning lesDeuxVerres .w3 = true); decide

end WorkedExample

end JereticEtAl2025
