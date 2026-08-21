import Mathlib.Data.Finset.Card
import Linglib.Studies.Corbett1991
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Fragments.Spanish.Gender
import Linglib.Fragments.Slavic.Russian.Gender
import Linglib.Fragments.Hausa.Gender

/-!
# Grammatical gender: a close look at gender assignment across languages

[kramer-2020] reviews how nouns are sorted into genders. Every gender
system assigns gender to some nouns by animacy, humanness, or social
gender/biological sex — the semantic core generalization — and the
remainder nouns take one gender or several, recycled from the core or
novel, in every combination (Table 2). Russian's remainder follows
declension class up to the Class III exceptions, and Hausa's feminine
remainder ends in *-ā*, a correlation that fails in the other direction.
Against these facts the review sets [harris-1991]'s lexical rules beside
[kramer-2015]'s gender on n for Spanish: the two agree on Spanish, but a
lexical entry holds one gender feature, so hybrid nouns call for a second
structural source, and the thesis of radical interpretability derives the
semantic core from the structural account alone.

## Main definitions

* `IsCore`, `SatisfiesSemanticCore`: the properties of (3) and the
  generalization (2) over [corbett-1991]'s profiles.
* `Remainder`: a language's core and remainder genders and the cells of
  Table 2.
* `declensionGender`: [corbett-1991]'s declension rule (18) for Russian.
* `phonologicalRule`: the disputed Hausa rule (26).
* `LexicalEntry`, `LexicalEntry.humanCloning`, `LexicalEntry.humanGender`:
  [harris-1991]'s lexical system (Figure 1, (23)).
* `nHead`, `determiners`, `determiner`: the four n's of (24) and the
  determiner items of (25).
* `RadicallyInterpretable`: (29) as a condition on a language's gender
  features.

## Main results

* `semantic_core_holds`: (2) across the sample.
* `Remainder.not_mixed_of_allSame`: the inapplicable cell of Table 2.
* `declension_exceptions`: (18) fails on exactly the Class III nouns of
  (19).
* `phonologicalRule_kada`, `feminine_remainder_aa`: the *-ā* correlation
  fails forwards and holds backwards.
* `lexical_faithful`, `structural_faithful`, `lexical_eq_structural`: both
  accounts recover the Fragment's genders.
* `determiner_iMasc_eq_plain`: [−fem] and featureless n share *el* by the
  Subset Principle.
* `lexical_no_hybrid`: no lexical entry fits (27).
* `exists_interpretable`, `lexical_allows_arbitrary_only`: radical
  interpretability yields the semantic core; the lexical account does not.
-/

namespace Kramer2020

open Corbett1991 (SemanticBasis Profile allProfiles)
open scoped DistributedMorphology.VocabularyItem
open DistributedMorphology
open Spanish.Gender (SpanishNoun)
open Russian.Gender (DeclClass)

/-! ### The semantic core (§1.2) -/

/-- The minimal properties of (3): animacy, humanness, and social gender or
biological sex. -/
def IsCore : SemanticBasis → Prop
  | .animacy | .humanness | .sex => True
  | .shape | .rationality => False

instance : DecidablePred IsCore := fun b => by cases b <;> unfold IsCore <;> infer_instance

/-- The semantic core generalization (2): a language with gender assigns it
to some nouns by a property of (3). -/
def SatisfiesSemanticCore (p : Profile) : Prop :=
  p.rawCount = 0 ∨ ∃ b ∈ p.semanticBases, IsCore b

instance : DecidablePred SatisfiesSemanticCore := fun _ => inferInstanceAs (Decidable (_ ∨ _))

theorem semantic_core_holds : ∀ p ∈ allProfiles, SatisfiesSemanticCore p := by decide

/-! ### Remainder nouns (§2.3.1) -/

/-- The genders a language assigns semantically and the genders of its
remainder nouns. -/
structure Remainder (G : Type*) where
  core : Finset G
  remainder : Finset G

namespace Remainder

variable {G : Type*} (r : Remainder G)

/-- The remainder nouns all take one gender. -/
def AllSame : Prop := r.remainder.card = 1

/-- The remainder genders are recycled from the core. -/
def Recycled : Prop := r.remainder ⊆ r.core

/-- The remainder genders are novel. -/
def Novel : Prop := Disjoint r.remainder r.core

/-- Recycled and novel genders both occur. -/
def Mixed : Prop := ¬ r.Recycled ∧ ¬ r.Novel

instance : Decidable r.AllSame := inferInstanceAs (Decidable (r.remainder.card = 1))

instance [DecidableEq G] : Decidable r.Recycled :=
  inferInstanceAs (Decidable (r.remainder ⊆ r.core))

instance [DecidableEq G] : Decidable r.Novel :=
  inferInstanceAs (Decidable (Disjoint r.remainder r.core))

instance [DecidableEq G] : Decidable r.Mixed := inferInstanceAs (Decidable (_ ∧ _))

/-- The cell of Table 2 marked not applicable: a single remainder gender is
recycled or novel. -/
theorem not_mixed_of_allSame (h : r.AllSame) : ¬ r.Mixed := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h
  rintro ⟨hr, hn⟩
  simp only [Recycled, Novel, hg, Finset.singleton_subset_iff,
    Finset.disjoint_singleton_left] at hr hn
  exact hn hr

/-- The core and remainder genders of a lexicon with a natural-gender
field. -/
def ofNouns {N : Type*} (nouns : List N) (natural : N → Bool) (gender : N → Gender) :
    Remainder Gender where
  core := ((nouns.filter natural).map gender).toFinset
  remainder := ((nouns.filter (!natural ·)).map gender).toFinset

/-- Dieri: female humans feminine, male humans masculine, every other noun
masculine. -/
def dieri : Remainder Gender := ⟨{.masculine, .feminine}, {.masculine}⟩

/-- Tamil: Dieri's core, with the remainder in a novel neuter. -/
def tamil : Remainder Gender := ⟨{.masculine, .feminine}, {.neuter}⟩

/-- Spanish: the remainder split arbitrarily over both core genders
(Table 1), read off the Fragment. -/
def spanish : Remainder Gender :=
  ofNouns Spanish.Gender.allNouns (·.isNaturalGender) (·.attestedGender)

/-- Blackfoot: animates animate; inanimates in a novel inanimate gender or
the recycled animate one. -/
def blackfoot : Remainder Gender := ⟨{.animate}, {.animate, .inanimate}⟩

/-- Table 2: same gender recycled (Dieri) or novel (Tamil), different
genders recycled (Spanish) or both (Blackfoot). -/
theorem table2 :
    dieri.AllSame ∧ dieri.Recycled ∧ tamil.AllSame ∧ tamil.Novel ∧
      ¬ spanish.AllSame ∧ spanish.Recycled ∧ ¬ blackfoot.AllSame ∧ blackfoot.Mixed := by
  decide

/-- Akɔɔse's cell: with the human gender as the core and at least seven
other remainder genders, the remainder takes different, novel genders. -/
theorem akoose_cell (r : Remainder ℕ) (hcore : r.core = {1}) (hcard : 7 ≤ r.remainder.card)
    (h : 1 ∉ r.remainder) : ¬ r.AllSame ∧ r.Novel :=
  ⟨fun h₁ => by unfold AllSame at h₁; omega,
    by rw [Novel, hcore]; exact Finset.disjoint_singleton_right.mpr h⟩

end Remainder

/-! ### Declension class in Russian (§2.3.2) -/

/-- [corbett-1991]'s assignment for the Russian remainder (18): Class I
masculine, Class II or III feminine, all others neuter. -/
def declensionGender : DeclClass → Gender
  | .I => .masculine
  | .II | .III => .feminine
  | .IV => .neuter

/-- (18) misassigns exactly the Class III nouns of (19): neuter *znamja*
and masculine *put'*. -/
theorem declension_exceptions :
    Russian.Gender.remainderNouns.filter
        (fun n => n.declClass.map declensionGender ≠ some n.attestedGender) =
      [Russian.Gender.znamja, Russian.Gender.put'] := by
  decide

/-! ### The final vowel in Hausa (§2.3.2, §3.3.1) -/

/-- The disputed rule (26): a noun in *-ā* is feminine, any other
masculine. -/
def phonologicalRule (n : Hausa.Noun) : Gender :=
  if n.EndsInAa then .feminine else .masculine

/-- (22e): *kadā̀* 'crocodile' ends in *-ā* and is masculine, so (26) is
false. -/
theorem phonologicalRule_kada : phonologicalRule Hausa.kada ≠ Hausa.kada.attestedGender := by
  decide

/-- The correlation in its valid direction, feminine gender realized as
*-ā*: every feminine noun outside the semantic core ends in *-ā*. -/
theorem feminine_remainder_aa :
    ∀ n ∈ Hausa.allNouns,
      n.isNaturalGender = false → n.attestedGender = .feminine → n.EndsInAa := by
  decide

/-! ### Lexical gender assignment (§3.2) -/

/-- A lexical entry in [harris-1991]'s system: the semantic features
[human] and [female] and the gender feature [f]. -/
structure LexicalEntry where
  human : Bool
  female : Bool
  f : Bool
  deriving DecidableEq, Repr, Fintype

namespace LexicalEntry

/-- Human Cloning (Figure 1): a [human] entry doubles into a [male] and a
[female] entry. -/
def humanCloning (e : LexicalEntry) : List LexicalEntry :=
  if e.human then [{ e with female := false }, { e with female := true }] else [e]

/-- The Human Gender rule (23): [female] → [f] / __ [human]. -/
def humanGender (e : LexicalEntry) : LexicalEntry :=
  { e with f := e.f || (e.human && e.female) }

/-- Agreement: feminine with [f], masculine by default. -/
def gender (e : LexicalEntry) : Gender := if e.f then .feminine else .masculine

end LexicalEntry

/-- The lexical entry of a Fragment noun: [human] for the natural-gender
nouns (higher animals honoris causa), [female] for the female-denoting
ones, and a listed [f] for the arbitrarily feminine remainder. -/
def lexicalEntry (n : SpanishNoun) : LexicalEntry :=
  ⟨n.isNaturalGender, n.isNaturalGender && n.attestedGender == .feminine,
    !n.isNaturalGender && n.attestedGender == .feminine⟩

/-- The lexical account recovers every Fragment gender. -/
theorem lexical_faithful :
    ∀ n ∈ Spanish.Gender.allNouns, (lexicalEntry n).humanGender.gender = n.attestedGender := by
  decide

/-- *persona*, listed with [f], stays feminine under Human Cloning. -/
theorem persona_cloned_feminine :
    (LexicalEntry.humanCloning ⟨true, false, true⟩).map (·.humanGender.gender) =
      [.feminine, .feminine] := rfl

/-! ### Structural gender assignment (§3.2) -/

/-- The four n's of (24). -/
def spanishHeads : List Categorizer.Head := [.n_iFem, .n_iMasc, .n_plain, .n_uFem]

/-- The n of a Fragment noun: interpretable gender for the natural-gender
nouns, u[+fem] for the arbitrarily feminine remainder — *persona* among
them — and plain n otherwise. -/
def nHead (n : SpanishNoun) : Categorizer.Head :=
  match n.attestedGender, n.isNaturalGender with
  | .feminine, true => .n_iFem
  | .masculine, true => .n_iMasc
  | .feminine, false => .n_uFem
  | _, _ => .n_plain

theorem nHead_mem_spanishHeads (n : SpanishNoun) : nHead n ∈ spanishHeads := by
  obtain ⟨_, _, g, b⟩ := n; cases g <;> cases b <;> simp [nHead, spanishHeads]

/-- Same-root nominals (14a) combine with either interpretable n. -/
def sameRootHeads : List Categorizer.Head := [.n_iFem, .n_iMasc]

/-- The features of a definite determiner: [d], [def], and the gender it
acquires by agreement. -/
inductive DetFeature where
  | d
  | definite
  | gender (v : Gender.Signed)
  deriving DecidableEq, Repr

/-- What the determiner carries after agreeing with a head. -/
def determinerFeatures (ch : Categorizer.Head) : List DetFeature :=
  [.d, .definite] ++ (ch.phi.gender.map fun gf => .gender gf.val).toList

/-- The Spanish definite determiners (25): *la* with [+fem], *el*
underspecified. -/
def determiners : List (VocabularyItem DetFeature String) :=
  [[.d, .definite, .gender ⟨.fem, .pos⟩] ⟷ "la", [.d, .definite] ⟷ "el"]

/-- The determiner a head takes, by the Subset Principle. -/
def determiner (ch : Categorizer.Head) : Option String :=
  subsetPrinciple determiners (determinerFeatures ch)

/-- A determiner with [−fem] and one with no gender feature both take
*el*: *la* carries a feature neither bears. -/
theorem determiner_iMasc_eq_plain :
    determiner .n_iMasc = some "el" ∧ determiner .n_plain = some "el" := by decide

/-- Natural and arbitrary feminine share *la*: one feature, [+fem]. -/
theorem determiner_iFem_eq_uFem :
    determiner .n_iFem = some "la" ∧ determiner .n_uFem = some "la" := by decide

/-- The structural account recovers every Fragment gender. -/
theorem structural_faithful :
    ∀ n ∈ Spanish.Gender.allNouns,
      determiner (nHead n) = some (if n.attestedGender = .feminine then "la" else "el") := by
  decide

/-- On Spanish the two accounts agree (§3.3). -/
theorem lexical_eq_structural :
    ∀ n ∈ Spanish.Gender.allNouns,
      ((lexicalEntry n).humanGender.gender = .feminine ↔ determiner (nHead n) = some "la") := by
  decide

/-! ### Hybrid nouns (§3.3.2) -/

/-- (27): the agreement targets of *vrač* 'doctor' — the Fragment's
morphologically masculine Class I noun — and their genders in one phrase. -/
def hybridTargets : List (String × Gender) := [("xoroš-aja", .feminine), ("glavn-yj", .masculine)]

/-- No lexical entry fits (27): an entry has one gender. The structural
account adds a second source of gender features above n. -/
theorem lexical_no_hybrid : ¬ ∃ e : LexicalEntry, ∀ t ∈ hybridTargets, t.2 = e.gender := by
  decide

/-! ### Radical interpretability and the semantic core (§3.3.3) -/

/-- The thesis of radical interpretability (29) as a condition on a
language's gender features: an uninterpretable instantiation of a
dimension implies an interpretable one. -/
def RadicallyInterpretable (fs : List GenderFeature) : Prop :=
  ∀ gf ∈ fs, gf.interp = .u → ∃ gf' ∈ fs, gf'.interp = .i ∧ gf'.val.dim = gf.val.dim

instance (fs : List GenderFeature) : Decidable (RadicallyInterpretable fs) := by
  unfold RadicallyInterpretable; infer_instance

theorem spanish_radicallyInterpretable :
    RadicallyInterpretable (spanishHeads.filterMap (·.phi.gender)) := by decide

/-- Under radical interpretability a language with gender features has an
interpretable one, so some nouns are gendered semantically: the semantic
core, from the structural account. -/
theorem exists_interpretable {fs : List GenderFeature} (h : RadicallyInterpretable fs)
    (hne : fs ≠ []) : ∃ gf ∈ fs, gf.interp = .i := by
  obtain ⟨gf, hgf⟩ := List.exists_mem_of_ne_nil fs hne
  cases hi : gf.interp with
  | i => exact ⟨gf, hgf, hi⟩
  | u => obtain ⟨gf', h₁, h₂, -⟩ := h gf hgf hi; exact ⟨gf', h₁, h₂⟩

/-- The lexical account excludes nothing: a lexicon whose two agreement
classes track no semantic feature is well formed, though no such language
is attested. -/
theorem lexical_allows_arbitrary_only :
    ∃ L : List LexicalEntry, (∀ e ∈ L, e.human = false) ∧
      (∃ e ∈ L, e.gender = .feminine) ∧ ∃ e ∈ L, e.gender = .masculine :=
  ⟨[⟨false, false, true⟩, ⟨false, false, false⟩], by decide⟩

end Kramer2020
