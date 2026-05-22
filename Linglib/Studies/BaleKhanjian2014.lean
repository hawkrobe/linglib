import Mathlib.Data.Fintype.Powerset
import Linglib.Core.Tree
import Linglib.Theories.Semantics.Alternatives.Structural
import Linglib.Fragments.Armenian.ClassifierSystem

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
  @cite{bliss-2004} on Turkish; not formalized here).
- The compositional semantics of `[-n]/[-ə]` as `sup`/`f_σ`-decomposed
  definiteness (BK 2014 §6, derivation 37–39; deferred to a future pass).
- The §2.1 predicate-distribution data for general number (eqs. 4–5,
  *John-ə yev Brad-ə dəgha en* "John and Brad are boys (sg.)") which
  is the *primary* empirical anchor for the general-number claim,
  originally argued by @cite{donabedian-1993}.

## Post-2014 engagement

@cite{marti-2020} *Numerals and the theory of number* (S&P 13:3) revisits
the BGK 2011 / BK 2014 assumptions about Turkish and Western Armenian
and proposes an alternative numeral-semantic analysis that doesn't rely
on syntactic-complexity competition. A Marti 2020 study file would be
the natural cross-paper test case here.
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

/-- **The headline definite-case theorem**: `singularDef` and `pluralDef`
    have *equal* @cite{katzir-2007} complexity — each is derivable from
    the other by a chain of three same-category leaf substitutions
    (`Num "-∅" ↔ "-ner"`, `Det "-n" ↔ "-ə"`, `V "vaze-ts" ↔ "vaze-ts-in"`).

    Substrate helpers `equalComplexity_terminal_subst`,
    `equalComplexity_inChild`, and `equalComplexity.trans` are available
    in `Alternatives/Structural.lean` for cleaner future versions. The
    direct-construction proof below explicitly walks each
    `StructOp.inChild` chain (mechanical but verbose); a future
    `katzir_path_subst` tactic could collapse this to ~5 lines.

    Load-bearing claim from @cite{bale-khanjian-2014} §5: the plural
    definite is a viable structural alternative to the singular definite,
    licensing Katzir-mediated competition that derives the strict-singular
    meaning. -/
theorem singularDef_pluralDef_equalComplexity :
    equalComplexity waLex singularDef pluralDef := by
  -- Intermediate trees for the pluralDef → singularDef chain:
  -- After V substitution then Det substitution.
  let pluralVNer := pluralDef
  let intermed1 : Tree Cat String :=
    .node .S [
      .node .DP [
        .node .NumP [
          .node .NP [.terminal .N "dəgha"],
          .terminal .Num "-ner"],
        .terminal .Det "-ə"],
      .node .VP [.terminal .V "vaze-ts"]]
  let intermed2 : Tree Cat String :=
    .node .S [
      .node .DP [
        .node .NumP [
          .node .NP [.terminal .N "dəgha"],
          .terminal .Num "-ner"],
        .terminal .Det "-n"],
      .node .VP [.terminal .V "vaze-ts"]]
  refine ⟨?_, ?_⟩
  · -- pluralDef → intermed1 → intermed2 → singularDef
    refine .head (b := intermed1) ?_ (.head (b := intermed2) ?_ (.single ?_))
    · -- substitute V "vaze-ts-in" with V "vaze-ts" at [1, 0]
      apply StructOp.inChild ⟨1, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · -- substitute Det "-ə" with Det "-n" at [0, 1]
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · -- substitute Num "-ner" with Num "-∅" at [0, 0, 1]
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
  · -- singularDef → intermed2 → intermed1 → pluralDef (mirror)
    refine .head (b := intermed2) ?_ (.head (b := intermed1) ?_ (.single ?_))
    · apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · apply StructOp.inChild ⟨0, by simp⟩
      apply StructOp.inChild ⟨1, by simp⟩
      exact StructOp.subst rfl (by simp [waLex])
    · apply StructOp.inChild ⟨1, by simp⟩
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

/-! ## §3a: Cross-paper disagreement with @cite{sauerland-2003}

@cite{bale-khanjian-2014} explicitly reject Gricean / phi-MP accounts
of number competition (introduction + §3, citing @cite{krifka-1989},
@cite{sauerland-2003}, @cite{spector-2007}). Sauerland's
`mp_blocks_plural_at_atom` says that for any *atomic* individual, MP
selects the singular form over the plural — pre-empting general number.

BK 2014's data contradict this for indefinite singulars: *dəgha vaze-ts*
"one or more boys ran" (eq. 3) is felicitous about a single atomic boy,
even though Sauerland would predict pre-emption. The (formalized)
witness: the singleton `{Boy.a}` (a single atomic boy) is in the
general-number denotation `daghaGenNum` (eq. 9), and BK 2014's
empirical claim is that the singular indefinite is felicitous about
this referent. Sauerland's account predicts pre-emption; BK's data
deny it.

A *full* contradiction theorem requires bridging Sauerland's entity-
level MP (`Sauerland2003.mp_blocks_plural_at_atom : ∀ x : E, Atom x → ...`)
to BK's tree-level Katzir competition. Such a bridge is not currently
in linglib; this section provides the witness and the structural
argument in prose. -/

/-- Witness for the Sauerland-vs-BK disagreement: the singleton `{Boy.a}`
    is an atomic individual that BK 2014 say can be picked out by the
    indefinite singular *dəgha* (general-number reading), but
    @cite{sauerland-2003}'s `mp_blocks_plural_at_atom` would predict
    pre-emption by the strict-singular reading. -/
theorem singleton_atom_in_genNum :
    ({Boy.a} : Plurality) ∈ daghaGenNum := by decide

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
    classifier morpheme that the silent ∪-operator would be blocked by.
    Western Armenian's `classifierSystem` carries `isObligatory := false`,
    structurally failing the input shape that obligatory-CL frameworks
    like @cite{chierchia-1998} and @cite{sudo-2016} presuppose.

    The dependency goes from BK 2014 → `Fragments/Armenian/ClassifierSystem.lean`
    rather than BK 2014 → Sudo 2016 (which would violate the chronology
    rule — study files may reference older papers, not newer ones). -/
theorem western_armenian_lacks_obligatory_classifier_input :
    ¬ Fragments.Armenian.classifierSystem.IsObligatory := by decide

end BaleKhanjian2014
