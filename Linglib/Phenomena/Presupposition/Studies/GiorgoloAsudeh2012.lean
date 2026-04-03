import Linglib.Theories.Semantics.Composition.WriterMonad
import Linglib.Theories.Semantics.Lexical.Expressives.Basic
import Linglib.Phenomena.Presupposition.ProjectiveContent

/-!
# Giorgolo & Asudeh 2012: Monads for Conventional Implicatures
@cite{giorgolo-asudeh-2012}

## Core Claim

Conventional implicatures are modeled as Writer monad side-effects.
CI-contributing expressions (appositives, expressives) *log* propositions
to a side-issue dimension via `write`, while presupposition triggers
log conditions via `check`. The monadic type structure enforces
@cite{potts-2005}'s flow restriction by construction: `bind`'s function
argument receives only the at-issue value, never the CI log.

## Two-Stage Architecture

1. **Compositional phase**: at-issue and CI dimensions are separated;
   Potts's flow restrictions hold (at-issue → CI is one-way).
2. **Post-compositional phase**: anaphora resolution and presupposition
   checking can freely access both dimensions.

## Two Channels via Monad Transformer (Appendix A)

The analysis requires *two* Writer monads combined via a monad transformer:
- **Inner Writer** (CI): accumulates conventional implicature propositions
- **Outer Writer** (Presupposition): accumulates presuppositional conditions

`write` and `check` have the same definition `λt.⟨⊥, {t}⟩` (eq. 21)
but operate in different monad layers (fn. 4).

## Worked Example (§5): "John, who likes cats, likes dogs also."

- At-issue: like(john, dogs)
- CI: {like(john, cats)} — from the NRRC via `write`
- Presupposition: {∃z. like(john, z) ∧ z ≠ dogs} — from "also" via `check`

The presupposition is satisfied by the CI content: john likes cats,
and cats ≠ dogs. This satisfaction happens post-compositionally,
after both Writer logs are exposed.

## Relation to @cite{shan-2001}

@cite{shan-2001} showed monads capture deep structure in NL semantics
(focus, scope, questions, binding). @cite{giorgolo-asudeh-2012} apply
the *Writer* monad specifically to CIs, arguing it is preferable to
the continuation-based approach: each monad isolates one kind of
side-effect, and monad transformers compose them modularly.
-/

namespace Phenomena.Presupposition.Studies.GiorgoloAsudeh2012

open Semantics.Composition.WriterMonad (Writer)

-- ════════════════════════════════════════════════════
-- § Model
-- ════════════════════════════════════════════════════

inductive E where | john | cats | dogs
  deriving DecidableEq, Repr

def like (x y : E) : Bool :=
  match x, y with
  | .john, .cats | .john, .dogs => true
  | _, _ => false

-- ════════════════════════════════════════════════════
-- § Semantic Propositions (log entries)
-- ════════════════════════════════════════════════════

/-- CI propositions: unevaluated semantic objects logged by `write`. -/
inductive CIProp where
  | likes : E → E → CIProp
  deriving DecidableEq, Repr

/-- Presuppositional conditions: unevaluated conditions logged by `check`. -/
inductive PresupProp where
  /-- ∃z. like(subj, z) ∧ z ≠ obj — the presupposition of "also" -/
  | existsOtherLiked : E → E → PresupProp
  deriving DecidableEq, Repr

def CIProp.eval : CIProp → Bool
  | .likes x y => like x y

/-- Evaluate a presuppositional condition over the finite entity domain. -/
def PresupProp.eval : PresupProp → Bool
  | .existsOtherLiked subj obj =>
    [E.john, E.cats, E.dogs].any λ z => like subj z && !(z == obj)

-- ════════════════════════════════════════════════════
-- § Two-Channel Architecture (Monad Transformer, Appendix A)
-- ════════════════════════════════════════════════════

/-- Two-channel meaning: flattened `Writer Presup (Writer CI A)`.

    The outer Writer carries presuppositions; the inner carries
    conventional implicatures. Figure 1's result type is:
    `⟨⟨at-issue, {CI-props}⟩, {presup-conditions}⟩` -/
structure TwoChannel (CI Presup : Type*) (A : Type*) where
  val : A
  ciLog : List CI
  presupLog : List Presup

namespace TwoChannel

variable {CI Presup A B : Type*}

def pure (a : A) : TwoChannel CI Presup A := ⟨a, [], []⟩

def bind (m : TwoChannel CI Presup A) (f : A → TwoChannel CI Presup B)
    : TwoChannel CI Presup B :=
  let r := f m.val
  ⟨r.val, m.ciLog ++ r.ciLog, m.presupLog ++ r.presupLog⟩

/-- `write(t) = ⟨⊥, {t}⟩` (eq. 21): log a proposition to the CI channel. -/
def write (p : CI) : TwoChannel CI Presup Unit := ⟨(), [p], []⟩

/-- `check(t) = lift(⟨⊥, {t}⟩)` (eq. 21, fn. 4): log a condition to the
    presupposition channel. Same definition as `write`, different layer. -/
def check (p : Presup) : TwoChannel CI Presup Unit := ⟨(), [], [p]⟩

@[simp] theorem pure_val (a : A) :
    (TwoChannel.pure (CI := CI) (Presup := Presup) a).val = a := rfl
@[simp] theorem pure_ciLog (a : A) :
    (TwoChannel.pure (CI := CI) (Presup := Presup) a).ciLog = [] := rfl
@[simp] theorem pure_presupLog (a : A) :
    (TwoChannel.pure (CI := CI) (Presup := Presup) a).presupLog = [] := rfl
@[simp] theorem bind_val (m : TwoChannel CI Presup A) (f : A → TwoChannel CI Presup B) :
    (m.bind f).val = (f m.val).val := rfl
@[simp] theorem bind_ciLog (m : TwoChannel CI Presup A) (f : A → TwoChannel CI Presup B) :
    (m.bind f).ciLog = m.ciLog ++ (f m.val).ciLog := rfl
@[simp] theorem bind_presupLog (m : TwoChannel CI Presup A)
    (f : A → TwoChannel CI Presup B) :
    (m.bind f).presupLog = m.presupLog ++ (f m.val).presupLog := rfl

end TwoChannel

-- ════════════════════════════════════════════════════
-- § Isomorphism: TwoChannel ≅ Writer Presup (Writer CI A)
-- ════════════════════════════════════════════════════

section NestedIso
variable {CI Presup A : Type*}

def ofNestedWriter (m : Writer Presup (Writer CI A)) : TwoChannel CI Presup A :=
  ⟨m.val.val, m.val.log, m.log⟩

def toNestedWriter (m : TwoChannel CI Presup A) : Writer Presup (Writer CI A) :=
  ⟨⟨m.val, m.ciLog⟩, m.presupLog⟩

theorem nested_roundtrip (m : TwoChannel CI Presup A) :
    ofNestedWriter (toNestedWriter m) = m := by
  cases m; rfl

theorem nested_roundtrip_inv (m : Writer Presup (Writer CI A)) :
    toNestedWriter (ofNestedWriter m) = m := by
  rcases m with ⟨⟨_, _⟩, _⟩; rfl

end NestedIso

-- ════════════════════════════════════════════════════
-- § Lexical Entries (Table 1)
-- ════════════════════════════════════════════════════

/-! All lexical items not introducing CIs or presuppositions are
    η-lifted: `⟦word⟧ = η(standard-meaning)` (Table 1). -/

open TwoChannel (write check)

/-- `comma` (Table 1): `λj λl. j ⋆ λx. l ⋆ λf. write(f x) ⋆ λ_. η(x)`

    The prosodic comma introduces NRRC content as CI via `write`.
    Both arguments are monadic (⊸* in Glue), matching Table 1's type
    `j ⊸* (j ⊸ l) ⊸* j`. -/
def commaOp (subj : TwoChannel CIProp PresupProp E)
    (nrrcPred : TwoChannel CIProp PresupProp (E → CIProp))
    : TwoChannel CIProp PresupProp E :=
  subj.bind λ x =>
    nrrcPred.bind λ f =>
      (write (f x)).bind λ _ =>
        TwoChannel.pure x

/-- `also` (Table 1):
    `λv.λo.λs. s ⋆ λx. v ⋆ λf. o ⋆ λy. check(∃z. f z x ∧ z ≠ y) ⋆ λ_. η(f y x)`

    Takes verb, object, subject (all monadic per ⊸*). Checks the
    presupposition that the subject verb-s something other than the
    object, then returns the at-issue content `f y x`. -/
def alsoEntry (verb : TwoChannel CIProp PresupProp (E → E → Bool))
    (obj : TwoChannel CIProp PresupProp E)
    (subj : TwoChannel CIProp PresupProp E)
    : TwoChannel CIProp PresupProp Bool :=
  subj.bind λ x =>
    verb.bind λ f =>
      obj.bind λ y =>
        (check (.existsOtherLiked x y)).bind λ _ =>
          TwoChannel.pure (f y x)

-- ════════════════════════════════════════════════════
-- § Derivation: "John, who likes cats, likes dogs also" (§5)
-- ════════════════════════════════════════════════════

/-- "John, who likes cats" — comma writes like(john, cats) to CI. -/
def john_who_likes_cats : TwoChannel CIProp PresupProp E :=
  commaOp (TwoChannel.pure .john)
          (TwoChannel.pure (λ subj => CIProp.likes subj .cats))

/-- Full sentence (example 20):
    `also(likes)(dogs)(john_who_likes_cats)` -/
def sentence : TwoChannel CIProp PresupProp Bool :=
  alsoEntry (TwoChannel.pure (λ y x => like x y))
            (TwoChannel.pure .dogs)
            john_who_likes_cats

-- ════════════════════════════════════════════════════
-- § Verification: Result matches Figure 1
-- ════════════════════════════════════════════════════

/-! Figure 1's result:
    `⟨⟨like(j, dogs), {like(j, cats)}⟩, {∃z.like(j,z) ∧ z ≠ dogs}⟩` -/

/-- At-issue: like(john, dogs) = true. -/
theorem sentence_atIssue : sentence.val = true := rfl

/-- CI log: {like(john, cats)} from the NRRC via `write`. -/
theorem sentence_ci : sentence.ciLog = [.likes .john .cats] := rfl

/-- Presupposition log: {∃z.like(john,z) ∧ z ≠ dogs} from `also` via `check`. -/
theorem sentence_presup :
    sentence.presupLog = [.existsOtherLiked .john .dogs] := rfl

-- ════════════════════════════════════════════════════
-- § Post-Compositional Phase
-- ════════════════════════════════════════════════════

/-! Post-compositionally, both logs are exposed. CI content and
    presuppositional conditions are evaluated against the model. -/

/-- All CI content is true in the model. -/
theorem ci_true_in_model : sentence.ciLog.all CIProp.eval = true := rfl

/-- All presuppositions are satisfied in the model. -/
theorem presup_satisfied : sentence.presupLog.all PresupProp.eval = true := rfl

/-- The CI log provides the witness for presupposition satisfaction.

    The NRRC logs like(john, cats). Since like(john, cats) = true and
    cats ≠ dogs, the presupposition ∃z. like(john, z) ∧ z ≠ dogs is
    witnessed. This is the paper's central empirical point: the
    presupposition of "also" is satisfied by CI content from the NRRC,
    but this satisfaction is only computable post-compositionally
    (the log produced by `write` cannot be examined before the monadic
    computation terminates). -/
theorem ci_witnesses_presup :
    sentence.ciLog.any (λ ci =>
      match ci with
      | .likes subj obj => like subj obj && !(obj == .dogs)) = true := rfl

-- ════════════════════════════════════════════════════
-- § Potts's Flow Restriction (by construction)
-- ════════════════════════════════════════════════════

/-! ### Why the Writer monad enforces dimensional separation

The function in `bind` has type `A → TwoChannel CI Presup B`, not
`TwoChannel CI Presup A → TwoChannel CI Presup B`. It receives the
*value* stripped of both logs. This means:

- **At-issue → CI** (allowed): The comma operator receives `john`
  (the value) and uses it to construct CI content `like(john, cats)`.

- **CI → at-issue** (blocked): When `also` applies the verb,
  the function receives only `x = john`, `f = likes`, `y = dogs`.
  It cannot see that the CI log contains `like(john, cats)`.

- **Presup → at-issue** (blocked): Similarly, presuppositional
  conditions logged by `check` are invisible to subsequent at-issue
  computation.

This structural separation IS Potts's restriction, enforced by the
type system rather than stipulated as a constraint on derivations. -/

/-- Changing the NRRC content does not affect the at-issue result:
    the main clause function sees only the value, never the CI log. -/
def sentence_alt_nrrc : TwoChannel CIProp PresupProp Bool :=
  alsoEntry (TwoChannel.pure (λ y x => like x y))
            (TwoChannel.pure .dogs)
            (commaOp (TwoChannel.pure .john)
                     (TwoChannel.pure (λ subj => CIProp.likes subj .dogs)))

theorem flow_restriction : sentence.val = sentence_alt_nrrc.val := rfl

-- ════════════════════════════════════════════════════
-- § Integration: Projective Content Taxonomy
-- ════════════════════════════════════════════════════

/-! CI-contributing expressions modeled by the Writer monad —
    expressives, appositives, NRRCs — are exactly Class B in
    @cite{tonhauser-beaver-roberts-simons-2013}'s taxonomy:
    SCF=no (CI content can be informative), OLE=no (attributed
    to speaker, not attitude holder). The Writer's log threading
    captures this: content projects past all operators without
    requiring prior establishment in context. -/

open Phenomena.Presupposition.ProjectiveContent (ProjectiveClass ProjectiveTrigger)

theorem nrrc_is_classB : ProjectiveTrigger.nrrc.toClass = .classB := rfl
theorem appositive_is_classB : ProjectiveTrigger.appositive.toClass = .classB := rfl
theorem expressive_is_classB : ProjectiveTrigger.expressive.toClass = .classB := rfl

/-- Class B = SCF=no, OLE=no: the behavior the Writer monad models. -/
theorem classB_properties :
    ProjectiveClass.classB.scf = .noRequires ∧
    ProjectiveClass.classB.ole = .notObligatory := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Bridge: TwoChannel → TwoDimProp
-- ════════════════════════════════════════════════════

/-! For intensional models where values and log entries are world-indexed
    propositions, the CI channel maps directly to @cite{potts-2005}'s
    `TwoDimProp`. The presupposition channel is orthogonal. -/

open Semantics.Lexical.Expressives (TwoDimProp)

section Bridge
variable {W : Type*}

/-- Project the CI channel to a TwoDimProp.
    The at-issue value becomes `atIssue`; the conjoined CI log becomes `ci`.
    Presuppositional content is discarded (it lives in a separate dimension). -/
def twoChannelToTwoDim (m : TwoChannel (W → Bool) (W → Bool) (W → Bool))
    : TwoDimProp W :=
  { atIssue := m.val
  , ci := λ w => m.ciLog.all (· w) }

theorem bridge_preserves_atIssue (m : TwoChannel (W → Bool) (W → Bool) (W → Bool)) :
    (twoChannelToTwoDim m).atIssue = m.val := rfl

end Bridge

/-! ### Structural correspondence to PostSupp

`PostSupp S A` (@cite{charlow-2021}) is structurally identical to a single
Writer monad: a value paired with accumulated side-effect content, composed
via `pure`/`bind` with log sequencing via `dseq`. The Writer monad for CIs
and Charlow's `PostSupp` for modified numerals are the same pattern applied
to different side-effects (CI propositions vs cardinality tests), confirming
@cite{shan-2001}'s insight that monads capture recurring compositional
structure in natural language. -/

end Phenomena.Presupposition.Studies.GiorgoloAsudeh2012
