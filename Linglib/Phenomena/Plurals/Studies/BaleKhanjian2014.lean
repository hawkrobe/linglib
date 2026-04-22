import Linglib.Core.Tree
import Linglib.Theories.Semantics.Alternatives.Structural
import Linglib.Fragments.Armenian.Typology

/-!
# Bale & Khanjian (2014) — Singular-Plural Distinction in Western Armenian
@cite{bale-khanjian-2014}

Bale, Alan and Khanjian, Hrayr. *Linguistic Inquiry* 45.1: 1-26.
Doi pending verification.

## Empirical core

Western Armenian (ISO `hyw`) has a singular-plural marking system
*different* from English: so-called "singular" nouns have a **general
number** interpretation (one or more) in indefinite contexts, while
"plural" nouns are strictly plural (≥2). Numerals can modify either
form. Crucially, **definiteness** forces strict singular:

| Sentence                          | Translation                  | Status   |
|-----------------------------------|------------------------------|----------|
| (3)   *dəgha vaze-ts*             | "one or more boys ran"       | OK, GEN# |
| (11b) *dəgha-n vaze-ts*           | "the (single) boy ran"       | OK, STRICT.SG |
| (10a) *yergu dəgha vaze-ts*       | "two boys ran"               | OK |
| (10b) *yergu dəgha-ner vaze-ts-in*| "two boys ran"               | OK |
| (14a) *yergu dəgha-n vaze-ts*     | "the two boys ran"           | UNGRAMMATICAL |
| (14b) *yergu dəgha-ner-ə vaze-ts-in* | "the two boys ran"        | OK |

The puzzle: why does definiteness force strict singular but indefinite
singular has general number?

## Theoretical move

@cite{bale-khanjian-2014} argue against pure Gricean competition
(@cite{krifka-1989}, @cite{sauerland-2003}, @cite{spector-2007}), which
over-predicts strict-singular interpretations everywhere; against the
@cite{bliss-2004} purely-syntactic solution, which requires
language-specific stipulations; and for **@cite{katzir-2007}'s
syntactic-complexity competition** combined with @cite{bliss-2004}'s
syntactic structures.

Per @cite{bliss-2004}: the singular indefinite has only `NP` (existential
introduced by the verb); the plural indefinite has full `DP[∃ NumP[...]]`.
Per @cite{katzir-2007}: alternatives must be derivable from the original
by deletion, contraction, or same-category substitution — so a plural
alternative with *more* syntactic structure is not a viable alternative.

Hence:
- *Singular indefinite* has no viable plural alternative (plural is more
  complex) → no competition → general-number meaning preserved.
- *Singular definite* has a same-complexity plural alternative
  (substitute `-ner`/`-ə` for the null Num head and `-n`) → competition
  applies → strict-singular meaning derived.

The (14a) ungrammaticality is handled by **local Maximize Presupposition**
(@cite{singh-2011}), applied at the NumP level.

## Cross-paper engagement (Sudo 2016)

@cite{sudo-2016}'s §5 flags Armenian as a counterexample to his
blocking-principle account of obligatory classifier languages. The key
fact from this paper: Western Armenian numerals combine *directly* with
bare nouns (eq. 10a, *yergu dəgha vaze-ts*). This means the Sudo
framework's input — a language with overt classifiers in the lexicon
that block the silent ∪-operator — is not present in Western Armenian.
Sudo's `.sudoBlocking` strategy doesn't apply; the language sits in a
different typological cell.

The Western Armenian classifier system is recorded in
`Fragments/Armenian/Typology.lean` with `isObligatory := false` and
`pluralClfCooccur := false` (per footnote 3, plurals are incompatible
with classifiers).

## What is formalized

- A toy 3-boy domain with both general-number and strict-plural denotations
  (per eq. 9).
- The four syntactic structures (eqs. 21, 20, 32a, 32b) as `Tree Cat String`,
  reusing `Core.Tree`.
- Two structural-complexity theorems via `Tree.size`: indefinite plural
  is *strictly larger* than indefinite singular (no Katzir competition);
  definite plural is *equal in size* to definite singular (Katzir
  competition applies).
- A docstring-level pointer to `Theories/Semantics/Alternatives/Structural`
  for the full Katzir 2007 competition machinery.

## Out of scope

- Full derivation of the strict-singular meaning via local Maximize
  Presupposition (@cite{singh-2011} machinery in
  `Theories/Semantics/Presupposition/MaximizePresupposition.lean` could be
  applied; deferred).
- Korean / Turkish parallels (BK 2014 fn 14 + §2.3 cite Kim 2005 on Korean,
  Bliss 2004 on Turkish; not formalized here).
- The compositional semantics of `[-n]/[-ə]` as `sup`/`f_σ`-decomposed
  definiteness (BK 2014 §6, derivation 37–39; deferred to a future pass).
-/

set_option autoImplicit false

namespace BaleKhanjian2014

open Core.Tree

-- ============================================================================
-- §1: Toy domain (eq. 9)
-- ============================================================================

/-- A finite domain of three atomic boys: a, b, c. Mirrors the LMR2022
    `Dog` toy domain. The denotations in eq. 9 of @cite{bale-khanjian-2014}
    use exactly this shape. -/
inductive Boy where | a | b | c
  deriving DecidableEq, Repr

instance : Fintype Boy where
  elems := {.a, .b, .c}
  complete x := by cases x <;> decide

/-- Plural individuals as non-empty finsets of atomic boys. Sums of two
    or more boys are pluralities; singletons are atomic individuals. -/
abbrev Plurality := Finset Boy

/-- @cite{bale-khanjian-2014} (9a): general-number denotation of *dəgha*.
    Contains all singletons and all sums (the inclusive interpretation):
    `{a, b, c, ab, ac, bc, abc}`. Nonempty subsets of `Boy`. -/
def daghaGenNum : Finset Plurality :=
  (Finset.univ : Finset Plurality).filter (·.Nonempty)

/-- @cite{bale-khanjian-2014} (9b): strict-plural denotation of *dəgha-ner*.
    Contains only sums of two or more: `{ab, ac, bc, abc}`. -/
def daghaNerStrictPl : Finset Plurality :=
  (Finset.univ : Finset Plurality).filter (·.card ≥ 2)

/-- The strict-plural set is a proper subset of the general-number set —
    every plurality in `dəgha-ner` is also in `dəgha`, but not conversely.
    This is the formal content of "general number includes singular". -/
theorem strictPl_subset_genNum :
    daghaNerStrictPl ⊆ daghaGenNum := by
  intro x hx
  simp [daghaNerStrictPl, daghaGenNum] at *
  rcases hx with ⟨_, hcard⟩
  exact Finset.card_pos.mp (by omega)

/-- The general-number set has 7 elements (3 singletons + 3 pairs + 1 triple). -/
theorem daghaGenNum_card : daghaGenNum.card = 7 := by decide

/-- The strict-plural set has 4 elements (3 pairs + 1 triple). -/
theorem daghaNerStrictPl_card : daghaNerStrictPl.card = 4 := by decide

-- ============================================================================
-- §2: Bliss 2004 syntactic structures (eqs. 21, 20, 32a, 32b)
-- ============================================================================

/-- Eq. 21 — singular indefinite: just `[S [NP dəgha] [VP vaze-ts]]`.
    No DP, no NumP. Existential quantification introduced by the verb
    (Carlson 1977, Chierchia 1998). -/
def singularIndef : Tree Cat String :=
  .node .S [
    .node .NP [.terminal .N "dəgha"],
    .node .VP [.terminal .V "vaze-ts"]]

/-- Eq. 20 — plural indefinite:
    `[S [DP ∃ [NumP [NP dəgha] [Num -ner]]] [VP vaze-ts-in]]`.
    Full DP with covert existential D-head and overt plural Num. -/
def pluralIndef : Tree Cat String :=
  .node .S [
    .node .DP [
      .terminal .Det "∃",
      .node .NumP [
        .node .NP [.terminal .N "dəgha"],
        .terminal .Num "-ner"]],
    .node .VP [.terminal .V "vaze-ts-in"]]

/-- Eq. 32a — singular definite:
    `[S [DP [NumP [NP dəgha] [Num -∅]] [Det -n]] [VP vaze-ts]]`.
    Full DP with phonologically null Num head. -/
def singularDef : Tree Cat String :=
  .node .S [
    .node .DP [
      .node .NumP [
        .node .NP [.terminal .N "dəgha"],
        .terminal .Num "-∅"],
      .terminal .Det "-n"],
    .node .VP [.terminal .V "vaze-ts"]]

/-- Eq. 32b — plural definite:
    `[S [DP [NumP [NP dəgha] [Num -ner]] [Det -ə]] [VP vaze-ts-in]]`.
    Same template as `singularDef` with `-ner`/`-ə` in place of
    `-∅`/`-n`. -/
def pluralDef : Tree Cat String :=
  .node .S [
    .node .DP [
      .node .NumP [
        .node .NP [.terminal .N "dəgha"],
        .terminal .Num "-ner"],
      .terminal .Det "-ə"],
    .node .VP [.terminal .V "vaze-ts-in"]]

-- ============================================================================
-- §3: Structural complexity (Katzir 2007)
-- ============================================================================

open Alternatives.Structural

/-- The lexicon needed to derive `singularDef` from `pluralDef` and vice
    versa via @cite{katzir-2007} substitution operations: all six
    terminals that differ between the two trees, plus the shared noun.
    `equalComplexity src φ ψ` is checked against `src` in both directions,
    so this lexicon is symmetric. -/
def waLex : List (Tree Cat String) :=
  [ .terminal .Num "-∅",   .terminal .Num "-ner"
  , .terminal .Det "-n",   .terminal .Det "-ə"
  , .terminal .V "vaze-ts", .terminal .V "vaze-ts-in"
  , .terminal .N "dəgha" ]

/-- Intermediate tree on the singular→plural derivation: `singularDef`
    after substituting `Num "-∅"` with `Num "-ner"` at path [0, 0, 1].
    Same as `pluralDef` except still has `Det "-n"` and `V "vaze-ts"`. -/
private def intermedNum : Tree Cat String :=
  .node .S [
    .node .DP [
      .node .NumP [
        .node .NP [.terminal .N "dəgha"],
        .terminal .Num "-ner"],
      .terminal .Det "-n"],
    .node .VP [.terminal .V "vaze-ts"]]

/-- Intermediate tree on the singular→plural derivation: `intermedNum`
    after substituting `Det "-n"` with `Det "-ə"` at path [0, 1]. -/
private def intermedNumDet : Tree Cat String :=
  .node .S [
    .node .DP [
      .node .NumP [
        .node .NP [.terminal .N "dəgha"],
        .terminal .Num "-ner"],
      .terminal .Det "-ə"],
    .node .VP [.terminal .V "vaze-ts"]]

/-- **The headline definite-case theorem**: `singularDef` and `pluralDef`
    have *equal* @cite{katzir-2007} complexity — each is derivable from
    the other by a chain of three same-category leaf substitutions
    (`Num "-∅" ↔ "-ner"`, `Det "-n" ↔ "-ə"`, `V "vaze-ts" ↔ "vaze-ts-in"`),
    threaded through the `intermedNum` / `intermedNumDet` intermediates.

    This is the load-bearing claim from @cite{bale-khanjian-2014} §5: the
    plural definite is a viable structural alternative to the singular
    definite, licensing Katzir-mediated competition, which derives the
    strict-singular meaning. -/
theorem singularDef_pluralDef_equalComplexity :
    equalComplexity waLex singularDef pluralDef := by
  refine ⟨?_, ?_⟩
  · -- atMostAsComplex waLex singularDef pluralDef = ReflTransGen ... pluralDef singularDef
    -- Three substitutions reverse-direction: V → Det → Num
    refine .head ?_ (.head ?_ (.single ?_))
    · -- pluralDef → intermedNumDet: substitute V "vaze-ts-in" with V "vaze-ts" at [1, 0]
      apply StructOp.inChild ⟨1, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · -- intermedNumDet → intermedNum: substitute Det "-ə" with Det "-n" at [0, 1]
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · -- intermedNum → singularDef: substitute Num "-ner" with Num "-∅" at [0, 0, 1]
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
  · -- atMostAsComplex waLex pluralDef singularDef = ReflTransGen ... singularDef pluralDef
    refine .head ?_ (.head ?_ (.single ?_))
    · -- singularDef → intermedNum: substitute Num "-∅" with Num "-ner" at [0, 0, 1]
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · -- intermedNum → intermedNumDet: substitute Det "-n" with Det "-ə" at [0, 1]
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · -- intermedNumDet → pluralDef: substitute V "vaze-ts" with V "vaze-ts-in" at [1, 0]
      apply StructOp.inChild ⟨1, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])

/-- **The headline indefinite-case theorem**: `pluralIndef` is strictly
    larger than `singularIndef`. @cite{katzir-2007}'s deletion/
    contraction/substitution operations are non-increasing in tree size
    (deletion strictly reduces, the others preserve), so a strict size
    increase is sufficient to rule out structural-alternative status.
    Hence `pluralIndef ∉ structuralAlternatives lex singularIndef`,
    no Katzir-mediated competition fires, and `singularIndef` keeps its
    general-number meaning. -/
theorem singularIndef_size_lt_pluralIndef_size :
    singularIndef.size < pluralIndef.size := by decide

/-- The asymmetry between (in)definites: equal complexity for definites,
    strict size increase for indefinites. The empirical wedge that drives
    the competition asymmetry per @cite{katzir-2007}. -/
theorem definiteness_asymmetry :
    equalComplexity waLex singularDef pluralDef ∧
    singularIndef.size < pluralIndef.size :=
  ⟨singularDef_pluralDef_equalComplexity, singularIndef_size_lt_pluralIndef_size⟩

-- ============================================================================
-- §5: Cross-paper note — Sudo 2016 doesn't apply to Western Armenian
-- ============================================================================

/-- Cross-paper note (forward reference): @cite{sudo-2016}'s §5 flags
    Armenian as a counterexample. The @cite{bale-khanjian-2014} data
    show *why* the input shape is wrong: Western Armenian numerals
    combine directly with bare nouns (eq. 10a), so there is no overt
    classifier morpheme that the silent ∪-operator would be blocked
    by. The general predicate `hasObligatoryClassifierSystem`
    (`Core/Typology/LanguageProfile.lean`) captures the input-shape
    requirement that obligatory-CL frameworks like @cite{chierchia-1998}
    and @cite{sudo-2016} presuppose; Western Armenian fails it
    structurally.

    The dependency goes from BK 2014 → `Core/Typology` rather than
    BK 2014 → Sudo 2016 (which would violate the chronology rule —
    study files may reference older papers, not newer ones). -/
theorem western_armenian_lacks_obligatory_classifier_input :
    ¬ Fragments.Armenian.typology.hasObligatoryClassifierSystem := by decide

end BaleKhanjian2014
