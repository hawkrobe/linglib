import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Transderivational Correspondence Theory (TCT)
[benua-1997]

TCT extends [mccarthy-prince-1995] Correspondence Theory with O-O
faithfulness constraints over morphologically related words. The
characteristic architectural commitment is **recursive evaluation** with
**base priority**: the base form is computed under a sub-grammar
(IO-Faith + Markedness only), then frozen and supplied as a parameter
to the derivative's evaluation under a richer grammar (IO-Faith +
OO-Faith + Markedness).

## Distinguishing architectural feature

The base-priority discipline is what distinguishes TCT from siblings:

| Theory | Architecture | Base priority? |
|---|---|---|
| Parallel OT ([mccarthy-prince-1995]) | One pass, joint EVAL | n/a — no separate base |
| Optimal Paradigms ([mccarthy-2005]) | Symmetric pairwise OO-Faith over paradigm | No — no privileged base |
| Stratal OT ([kiparsky-2000]) | Cyclic stratal EVAL | Yes, but via *cycles* |
| **TCT ([benua-1997])** | Parallel within-form, recursive across forms | Yes, by sub-grammar |
| Lexical Conservatism ([steriade-1997]) | Anchor on attested wordform | Yes, but anchor optional |

We *encode* base priority by the type signature
`TCTGrammar.baseEval : List α → List α` — there is no derivative slot,
so derivative-back-influence is ill-typed by construction. This is a
modeling choice (one could equally have written
`baseEval : List α → List α → List α`); the type-level encoding
*reflects* the architectural commitment of [benua-1997]'s "Priority
of the Base", but does not *deduce* it.

## TETU-style misapplication schema (`TetruSchema`)

A constraint ranking of the form `M₁ ≫ OO-Ident ≫ M₂ ≫ IO-Faith` —
[benua-1997]'s transderivational analog of [mccarthy-prince-1995]'s
reduplicative TETU (The Emergence of The Unmarked) — produces *misapplication
identity effects*: context-sensitive markedness `M₂` is violated in the
derivative iff necessary to preserve OO-identity to the base. This unifies
overapplication and underapplication as duals of a single mechanism.
(`TetruSchema` / "TETRU" is this file's shorthand for the schema, not a term
from [benua-1997].)

The empirical case studies — Sundanese nasal harmony overapplication
and Tiberian Hebrew spirantization underapplication — are formalized
in `Studies/Benua1997.lean`.

## What lives where

This file: the *substrate* — Role enum, TCTGrammar structure, base-priority
type-level fact, TetruSchema structure with named constraint slots, and
the misapplication-unification theorem. Concrete evaluation (sub-grammar
selection, candidate generation) is paper-specific and lives in study
files. The paradigm-uniformity face of TCT (`Corr`-style 3-role diagram
constructors for within-paradigm OO-Faith) lives with the case studies in
`Studies/Benua1997/Basic.lean`.

TCT is [benua-1997]'s own framework with no second consumer, so it is anchored to
this paper's study directory rather than the OT theory layer.
-/

namespace Benua1997.TCT

open OptimalityTheory.Correspondence (Corr)
open Constraints OptimalityTheory

-- ============================================================================
-- § 1: TCT Roles
-- ============================================================================

/-- The three derivational roles of [benua-1997]: `.input` is the
    underlying form (UR); `.base` is the morphologically simpler related
    word; `.derivative` is the complex word whose phonology is being
    computed. The `(base, derivative)` edge of a `Corr TCT.Role α` carries
    OO-correspondence; the `(input, base)` and `(input, derivative)` edges
    carry IO-correspondence. -/
inductive Role where
  | input
  | base
  | derivative
  deriving DecidableEq, Repr

/-- Display label for a TCT role (used in constraint names: `IDENT-OO`,
    `MAX-IO-Base`, etc.). -/
def Role.label : Role → String
  | .input      => "I"
  | .base       => "B"
  | .derivative => "D"

-- ============================================================================
-- § 2: TCT Grammar — type-level base priority
-- ============================================================================

/-- A TCT grammar separates **base evaluation** (under a sub-grammar with
    no OO-Faith) from **derivative evaluation** (under the full grammar
    including OO-Faith against the frozen base output). The `α`-typed
    forms are tier-projected representations (segments, tones, etc.).

    The architectural claim of [benua-1997]'s "Priority of the Base"
    is *encoded* in the type signatures: `baseEval : List α → List α`
    cannot mention the derivative; `derivativeEval : List α → List α → List α`
    takes the base output as a frozen parameter. -/
structure TCTGrammar (α : Type*) where
  /-- Optimal base form, computed from the input alone. The signature
      `List α → List α` *encodes* the architectural commitment that no
      derivative is in scope — a modeling choice that reflects but does
      not deduce base priority. -/
  baseEval : List α → List α
  /-- Optimal derivative form, computed from the input and the (already-
      computed) base output. The base is a *frozen parameter*, not an
      argument under joint evaluation. -/
  derivativeEval : List α → List α → List α

/-- Compute the surface form of a TCT derivative: first evaluate the base,
    then the derivative against the frozen base. -/
def TCTGrammar.derive {α} (g : TCTGrammar α) (input : List α) : List α :=
  g.derivativeEval input (g.baseEval input)

/-- The TCT derivation factorizes through the base: changing only the
    `derivativeEval` does not change the base output. -/
theorem TCTGrammar.base_invariant_under_derivative_eval {α} (input : List α)
    (baseEval : List α → List α)
    (derivativeEval₁ derivativeEval₂ : List α → List α → List α) :
    (TCTGrammar.mk baseEval derivativeEval₁).baseEval input =
    (TCTGrammar.mk baseEval derivativeEval₂).baseEval input :=
  rfl

-- ============================================================================
-- § 3: TETRU Schema
-- ============================================================================

/-- The TETRU constraint-ranking schema as a structure with named slots.
    Used by [benua-1997] (analog of [mccarthy-prince-1995]'s
    reduplicative TETU schema, with OO-Ident replacing BR-Ident as the
    "covering" faithfulness constraint).

    The four slots, in dominance order:

    * `m1` — high-ranked markedness, blocks overapplication that would
      produce a too-marked structure (the case of Tiberian Hebrew TETRU).
    * `ooIdent` — OO-Identity. Outranks `m2`, forcing misapplication.
    * `m2` — context-sensitive markedness whose canonical satisfaction
      pattern is overridden by OO-Ident in the derivative.
    * `ioFaith` — Input-Output faithfulness. Lowest-ranked; can be violated
      to satisfy `m2` or `ooIdent`. -/
structure TetruSchema (C : Type*) where
  m1 : Constraint C
  ooIdent : Constraint C
  m2 : Constraint C
  ioFaith : Constraint C

/-- Convert a `TetruSchema` to a ranked list of constraints in dominance
    order: `[m1, ooIdent, m2, ioFaith]`. -/
def TetruSchema.toRanking {C : Type*} (s : TetruSchema C) :
    List (Constraint C) :=
  [s.m1, s.ooIdent, s.m2, s.ioFaith]

@[simp] theorem TetruSchema.toRanking_length {C : Type*} (s : TetruSchema C) :
    s.toRanking.length = 4 := rfl

/-- The TETRU schema places `m1` at the top of the ranking. -/
@[simp] theorem TetruSchema.toRanking_get_zero {C : Type*} (s : TetruSchema C) :
    s.toRanking[0]? = some s.m1 := rfl

/-- OO-Ident sits at position 1 of the TETRU ranking — strictly above
    `m2` and `ioFaith`. The load-bearing structural fact: under TETRU,
    OO-Ident dominates the markedness constraint that would otherwise
    block misapplication. -/
@[simp] theorem TetruSchema.toRanking_get_one {C : Type*} (s : TetruSchema C) :
    s.toRanking[1]? = some s.ooIdent := rfl

@[simp] theorem TetruSchema.toRanking_get_two {C : Type*} (s : TetruSchema C) :
    s.toRanking[2]? = some s.m2 := rfl

@[simp] theorem TetruSchema.toRanking_get_three {C : Type*} (s : TetruSchema C) :
    s.toRanking[3]? = some s.ioFaith := rfl

-- ============================================================================
-- § 4: Misapplication Unification (the load-bearing theorem)
-- ============================================================================

/-- **Misapplication unification** (the architectural content of TCT
    [benua-1997]): under TETRU, when two candidates tie on M₁, the candidate
    with strictly fewer OO-Ident violations has the lexicographically smaller
    violation profile under the ranking `[m1, ooIdent, m2, ioFaith]` — and so
    wins the TETRU tableau, regardless of its M₂ and IO-Faith violations.

    Empirical reading: the "misapplied" candidate (overapplied harmony in
    Sundanese, underapplied spirantization in Tiberian Hebrew) violates M₂
    to satisfy OO-Ident; the "canonical" candidate satisfies M₂ but
    violates OO-Ident. Under TETRU, the misapplied candidate strictly
    beats the canonical one at the OO-Ident level — this is what makes
    overapplication and underapplication duals of one mechanism. -/
theorem TetruSchema.misapplication_wins {C : Type*} (s : TetruSchema C)
    (canonical misapplied : C)
    (hM1 : s.m1 canonical = s.m1 misapplied)
    (hOO : s.ooIdent misapplied < s.ooIdent canonical) :
    buildViolationProfile s.toRanking.get misapplied
      < buildViolationProfile s.toRanking.get canonical := by
  -- First difference is at OO-Ident (index 1): the candidates tie on M₁
  -- (index 0), and `misapplied` strictly wins on OO-Ident — so its violation
  -- profile is lexicographically smaller under `[m1, ooIdent, m2, ioFaith]`
  -- regardless of M₂/IO-Faith, i.e. `misapplied` wins the TETRU tableau.
  refine ⟨⟨1, by simp⟩, fun j hj => ?_, ?_⟩
  · have hj0 : j.val = 0 := by have : j.val < 1 := hj; omega
    obtain rfl : j = ⟨0, by simp⟩ := Fin.ext hj0
    exact hM1.symm
  · exact hOO

end Benua1997.TCT
