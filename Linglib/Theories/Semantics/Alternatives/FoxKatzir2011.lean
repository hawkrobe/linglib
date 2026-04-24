import Mathlib.Tactic.DeriveFintype
import Linglib.Theories.Semantics.Alternatives.Structural
import Linglib.Theories.Semantics.Alternatives.Symmetric
import Linglib.Theories.Semantics.Exhaustification.Innocent

/-!
# Fox & Katzir 2011: On the Characterization of Alternatives
@cite{fox-katzir-2011}

Fox, D. & Katzir, R. (2011). On the characterization of alternatives.
Natural Language Semantics, 19(1), 87–107.

## Core Argument

The formal alternatives for Scalar Implicatures (SI) and Association
with Focus (AF) are determined the same way — via @cite{katzir-2007}'s
structural complexity, not via Horn scales (for SI) or Rooth's focus
semantics (for AF). The single unified definition (eq. 37) takes a
contextual parameter C and is focus-sensitive.

## Section-by-section map

| F&K eq. | What it says                              | Where formalized |
| :-----: | ----------------------------------------- | ---------------- |
| (4)     | `SI_A(S) = ⋀{¬Sᵢ : Sᵢ ∈ N_SI(A,S)}`       | §4 below (`SI`) |
| (12)    | symmetric alternatives                    | `Symmetric.isSymmetric` |
| (17)    | `EXC_A(S) = ⋀{¬Sᵢ : Sᵢ ∈ N_AF(A,S)}`      | §5 below (`EXC`) |
| (18)    | `Only_A(S) = S ∧ EXC_A(S)`                | §5 below (`Only`) |
| (28)    | "Symmetry cannot be broken in C"          | `Symmetric.context_cannot_break_symmetry` (re-exported §7) |
| (35)    | `SS(X,C) = lex ∪ subtrees(X) ∪ salient C` | §3 below (`substitutionSourceFC`) |
| (37)    | `F(S, C)` via `≼_C`                       | §3 below (`formalAlternatives`) — focus restriction simplified |
| (38–41) | "John did all or none" disjunction        | §6 below |
| (50)    | relevance closure under ¬, ∧              | `Symmetric.RelevanceClosure` |

## What this file proves directly

1. §1: Some/all symmetric (eq. 12 instantiated); symmetric_complement verified.
2. §2: Innocent exclusion vacuous on the symmetric alt set; correct on Horn-restricted.
3. §3: F(S,C) extends Katzir 2007 with salient context. Without focus marking,
   our `formalAlternatives` is a (conservative) superset of F&K's eq. 37.
4. §4: SI / N_SI selectors.
5. §5: EXC / Only / N_AF — F&K's exhaustification operators.
6. §6: Second worked example — disjunction "John did all or none" (§4.1).
7. §7: Cross-reference to `Symmetric.context_cannot_break_symmetry` (eq. 28).

## Limitations (tracked, not fixed here)

- **Focus marking not represented** (eq. 37 simplification — see §3 docstring).
- **§5.2 allowable restriction / exhaustive relevance** (eqs. 55–56) is out of scope.
-/

namespace Alternatives.FoxKatzir2011

open Alternatives.Symmetric
open Exhaustification (innocent predToFinset altsFromPreds)


-- ============================================================
-- SECTION 1: Worked Example — Some/All (§1.1, p. 88)
-- ============================================================

/-!
## The Canonical Symmetric Example

S = "John did some of the homework"
S₁ = "John did all of the homework"
S₂ = "John did some but not all of the homework"

⟦S₁⟧ ∪ ⟦S₂⟧ = ⟦S⟧ and ⟦S₁⟧ ∩ ⟦S₂⟧ = ∅ — the classic partition.
-/

section SomeAll

/-- Three homework worlds: did all, did some (but not all), did none. -/
inductive HWWorld where | all_ | someNotAll | none_
  deriving Repr, DecidableEq, Fintype

private def hwDomain : List HWWorld := [.all_, .someNotAll, .none_]

private def didSome : HWWorld → Bool
  | .all_ | .someNotAll => true | .none_ => false
private def didAll : HWWorld → Bool
  | .all_ => true | _ => false
private def didSomeNotAll : HWWorld → Bool
  | .someNotAll => true | _ => false

/-- "All" and "some but not all" are symmetric alternatives of "some":
    they partition "some"'s denotation. -/
theorem some_all_symmetric :
    isSymmetric hwDomain didSome didAll didSomeNotAll = true := by
  native_decide

/-- Symmetric complement verified: some ∧ ¬all = sbna on this domain. -/
theorem some_all_complement :
    hwDomain.all (fun w => (didSome w && !didAll w) == didSomeNotAll w)
      = true := by
  native_decide

/-- Alternatives for "some": {some, all, sbna}. -/
private def someAlts : Finset (Finset HWWorld) :=
  altsFromPreds [didSome, didAll, didSomeNotAll]

/-- Horn-scale alternatives: {some, all} only — no symmetric partner. -/
private def hornAlts : Finset (Finset HWWorld) :=
  altsFromPreds [didSome, didAll]

/-- The prejacent: "some". -/
private def somePrej : Finset HWWorld := predToFinset didSome

/-- With both symmetric alternatives, neither is innocently excludable:
    MCE₁ excludes all (index 1), MCE₂ excludes sbna (index 2). -/
theorem some_symmetric_neither_ie :
    predToFinset didAll ∉ innocent.excluded someAlts somePrej ∧
    predToFinset didSomeNotAll ∉ innocent.excluded someAlts somePrej := by
  decide

/-- Without the symmetric alternative sbna (i.e., with Horn-scale
    alternatives {some, all}), "all" IS innocently excludable. -/
theorem some_hornscale_all_ie :
    predToFinset didAll ∈ innocent.excluded hornAlts somePrej := by
  decide

/-- The symmetry problem in a nutshell: with the full set
    {some, all, sbna}, exh is vacuous (no SIs — exhIE = some). With the
    restricted set {some, all}, exh correctly derives ¬all (exhIE
    excludes the all-world). -/
theorem symmetry_problem :
    innocent.exh someAlts somePrej = somePrej ∧
    innocent.exh hornAlts somePrej = predToFinset didSome \ predToFinset didAll := by
  decide

end SomeAll


-- ============================================================
-- SECTION 2: F Breaks Symmetry — Bridge to Katzir 2007 (§2–3)
-- ============================================================

/-!
## F Breaks Symmetry

While C cannot break symmetry, the formal alternatives F(S) can.
@cite{katzir-2007}'s structural definition excludes "some but not all"
from F("some") because it requires ConjP/NegP structure not derivable
from the substitution source.

- `all_is_alternative_to_some`: "all" ∈ F("some")
- `symmetry_problem_solved`: "some but not all" ∉ F("some")

These are re-exported from `Structural.lean`.
-/

section FBreaksSymmetry

open Alternatives.Structural

/-- F contains the non-symmetric alternative (all) but excludes the
    symmetric partner (sbna). This is exactly what's needed for exh
    to derive the correct SI ¬all. -/
theorem f_breaks_symmetry :
    allSentence ∈ structuralAlternatives exLexicon someSentence ∧
    someButNotAllSentence ∉ structuralAlternatives exLexicon
      someSentence :=
  ⟨all_is_alternative_to_some, symmetry_problem_solved⟩

end FBreaksSymmetry


-- ============================================================
-- SECTION 3: Unified F for SI and AF (claim 27, p. 94)
-- ============================================================

/-!
## Unified Definition: F_SI = F_AF (claim 27)

Fox & Katzir argue that the formal alternatives for SI and AF should
be defined identically — both via structural complexity (extending
@cite{katzir-2007} to focused constituents).

The standard view (26):
- For SI: F(S) = Horn scales (stipulated)
- For AF: F(S) = Rooth's focus semantics (type-based)

Their proposal (37): both use structural alternatives restricted to
focused constituents:
  F(S, C) = {S' : S' derived from S by replacing focused
             constituents with items ≲_C-comparable}

This preserves focus sensitivity (from Rooth) while allowing symmetry
breaking (from Katzir).

**Simplification**: our `formalAlternatives` does not enforce the focus
restriction (replacements may target any constituent, not only focused
ones). The full definition 37 would require focus-marking on parse tree
nodes. This simplification is conservative: the actual F(S,C) is a
subset of our `formalAlternatives`.
-/

/-- The substitution source for F(S, C) (conditions 34–35):
    Lexicon ∪ sub-constituents of S ∪ salient constituents in C.

    This extends @cite{katzir-2007}'s substitution source (def 41)
    with contextually salient material, enabling examples like
    Matsumoto's "warm"/"a little bit more than warm" (ex. 36). -/
def substitutionSourceFC {C W : Type}
    (lexicon : List (Core.Tree.Tree C W))
    (φ : Core.Tree.Tree C W)
    (salient : List (Core.Tree.Tree C W)) :
    List (Core.Tree.Tree C W) :=
  lexicon ++ φ.subtrees ++ salient

/-- Structural alternatives with contextual extension (definition 37).
    F(S, C) = {S' : S' ≲_C S}, where the substitution source includes
    salient constituents from context C.

    When `salient = []`, this reduces to @cite{katzir-2007}'s original
    `structuralAlternatives` (modulo the focus restriction; see above). -/
def formalAlternatives {C W : Type}
    (lex : List (Core.Tree.Tree C W))
    (φ : Core.Tree.Tree C W)
    (salient : List (Core.Tree.Tree C W)) :
    Set (Core.Tree.Tree C W) :=
  {ψ | Alternatives.Structural.atMostAsComplex
    (substitutionSourceFC lex φ salient) ψ φ}


-- ============================================================
-- SECTION 4: N_SI / N_AF — the alternative-selectors (fn. 4, §1.2)
-- ============================================================

/-!
## Which alternatives get negated?

Once F(S,C) is fixed, two further selections matter:

- `nSI` (footnote 4 in `@cite{fox-katzir-2011}`): for SI, the "standard
  view" picks the strictly stronger alternatives — those whose
  denotations are proper subsets of the prejacent.
- `nAF` (footnote 8 in `@cite{fox-katzir-2011}`): for AF/Only, the
  standard view picks the *non-weaker* alternatives — those whose
  denotations are not supersets of the prejacent (so the prejacent
  itself, anything strictly stronger, and anything logically
  independent, but not the entailers of the prejacent).

We work at the proposition level: alternatives are elements of
`Finset (Finset W)` and the prejacent is a `Finset W`. Subset =
entailment. -/

section Selectors

variable {W : Type} [Fintype W] [DecidableEq W]

/-- N_SI(A, S) (footnote 4): alternatives strictly stronger than S. -/
def nSI (alts : Finset (Finset W)) (S : Finset W) : Finset (Finset W) :=
  alts.filter (fun p => p ⊂ S)

/-- N_AF(A, S) (footnote 8): alternatives non-weaker than S. -/
def nAF (alts : Finset (Finset W)) (S : Finset W) : Finset (Finset W) :=
  alts.filter (fun p => ¬ S ⊆ p)

omit [Fintype W] in
/-- Every strictly-stronger alternative is non-weaker, so N_SI ⊆ N_AF.
    This is why the AF exhaustifier `Only` is at least as informative
    as the SI strengthener `SM` on the same alternative set. -/
theorem nSI_subset_nAF (alts : Finset (Finset W)) (S : Finset W) :
    nSI alts S ⊆ nAF alts S := by
  intro p hp
  simp only [nSI, nAF, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.2⟩

end Selectors


-- ============================================================
-- SECTION 5: SI / EXC / Only — F&K's exhaustification operators
-- ============================================================

/-!
## The operators

At the proposition level (treating each sentence as the set of worlds
where it is true), conjoining the negations of a set of alternatives
just removes their union from the universe. The four operators are
therefore set-difference operators parameterised by which N(A,S) we
use and whether we conjoin with the prejacent:

| operator | F&K eq. | what it returns                                |
| -------- | :-----: | ---------------------------------------------- |
| `SI`     | (4)     | `Univ \ ⋃ N_SI(A,S)` — the SI alone            |
| `SM`     | (5)     | `S \ ⋃ N_SI(A,S)` — strengthened meaning       |
| `EXC`    | (17)    | `Univ \ ⋃ N_AF(A,S)` — the only-exclusion alone |
| `Only`   | (18)    | `S \ ⋃ N_AF(A,S)` — `S ∧ EXC_A(S)`             |
-/

section Operators

variable {W : Type} [Fintype W] [DecidableEq W]

/-- SI_A(S) (eq. 4): conjunction of negations of N_SI(A,S),
    rendered as the complement of the union of strictly-stronger alts. -/
def SI (alts : Finset (Finset W)) (S : Finset W) : Finset W :=
  Finset.univ \ (nSI alts S).biUnion id

/-- SM_A(S) = S ∧ SI_A(S) (eq. 5): the strengthened meaning. -/
def SM (alts : Finset (Finset W)) (S : Finset W) : Finset W :=
  S \ (nSI alts S).biUnion id

/-- EXC_A(S) (eq. 17): the only-style exclusion. -/
def EXC (alts : Finset (Finset W)) (S : Finset W) : Finset W :=
  Finset.univ \ (nAF alts S).biUnion id

/-- Only_A(S) = S ∧ EXC_A(S) (eq. 18). -/
def Only (alts : Finset (Finset W)) (S : Finset W) : Finset W :=
  S \ (nAF alts S).biUnion id

omit [Fintype W] in
theorem SM_subset_S (alts : Finset (Finset W)) (S : Finset W) :
    SM alts S ⊆ S :=
  fun _ hw => (Finset.mem_sdiff.mp hw).1

omit [Fintype W] in
theorem Only_subset_S (alts : Finset (Finset W)) (S : Finset W) :
    Only alts S ⊆ S :=
  fun _ hw => (Finset.mem_sdiff.mp hw).1

omit [Fintype W] in
/-- Because `nSI ⊆ nAF`, removing the union of N_AF removes at least
    as much, so `Only` is at least as informative as `SM`. -/
theorem Only_subset_SM (alts : Finset (Finset W)) (S : Finset W) :
    Only alts S ⊆ SM alts S := by
  intro w hw
  simp only [Only, SM, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hw ⊢
  refine ⟨hw.1, ?_⟩
  rintro ⟨p, hp_si, hwp⟩
  exact hw.2 ⟨p, nSI_subset_nAF alts S hp_si, hwp⟩

end Operators


-- ============================================================
-- SECTION 6: §4.1 second worked example — disjunction symmetry
-- ============================================================

/-!
## "John did all or none" (eqs. 38–41)

Bare disjunction `(38)`: ⟦all⟧ and ⟦none⟧ partition ⟦all or none⟧, so
they are symmetric alternatives. Innocent exclusion is therefore
vacuous — neither disjunct can be negated.

Embedded under a universal `(40)`: the previously symmetric pair
becomes non-symmetric, because the universal admits worlds where the
disjunction holds but neither disjunct does. Innocent exclusion now
derives both SIs.
-/

section BareDisjunction

private def didNone : HWWorld → Bool
  | .none_ => true | _ => false

/-- "John did all of the homework or did none of it." -/
private def didAllOrNone : HWWorld → Bool
  | .all_ | .none_ => true | .someNotAll => false

/-- Eq. 39: ⟦all⟧ and ⟦none⟧ are symmetric alternatives of ⟦all or none⟧. -/
theorem all_none_symmetric :
    isSymmetric hwDomain didAllOrNone didAll didNone = true := by
  decide

/-- The disjunction's alternative set: {all-or-none, all, none}. -/
private def disjAlts : Finset (Finset HWWorld) :=
  altsFromPreds [didAllOrNone, didAll, didNone]

private def disjPrej : Finset HWWorld := predToFinset didAllOrNone

/-- Eq. 38: with both symmetric disjuncts in the alternative set, neither
    is innocently excludable. -/
theorem disjunction_neither_ie :
    predToFinset didAll ∉ innocent.excluded disjAlts disjPrej ∧
    predToFinset didNone ∉ innocent.excluded disjAlts disjPrej := by
  decide

/-- Eq. 38: bare disjunction has no SIs — innocent-exclusion exh is vacuous. -/
theorem disjunction_no_si :
    innocent.exh disjAlts disjPrej = disjPrej := by
  decide

end BareDisjunction


section EmbeddedDisjunction

/-- Worlds tracking deontic profile: what John's accessible homework
    completions look like. `reqEither` holds when the accessible worlds
    contain both an all-world and a none-world but not a some-not-all
    world — making the disjunction true throughout while neither
    disjunct is. -/
inductive RWorld where | reqAll | reqNone | reqEither | reqSomeNotAll
  deriving Repr, DecidableEq, Fintype

private def rDomain : List RWorld := [.reqAll, .reqNone, .reqEither, .reqSomeNotAll]

/-- ⟦John is determined to do all or none⟧ — true wherever every
    accessible world has John doing all or none, i.e., everywhere
    except `reqSomeNotAll`. -/
private def reqAllOrNone : RWorld → Bool
  | .reqAll | .reqNone | .reqEither => true
  | .reqSomeNotAll => false

private def reqAll : RWorld → Bool
  | .reqAll => true | _ => false

private def reqNone : RWorld → Bool
  | .reqNone => true | _ => false

/-- Eq. 41: under universal embedding, the previously symmetric pair fails
    to partition the disjunction — `reqEither` witnesses the gap. -/
theorem embedded_not_symmetric :
    isSymmetric rDomain reqAllOrNone reqAll reqNone = false := by
  decide

private def reqAlts : Finset (Finset RWorld) :=
  altsFromPreds [reqAllOrNone, reqAll, reqNone]

private def reqPrej : Finset RWorld := predToFinset reqAllOrNone

/-- Eq. 40: under universal embedding both `reqAll` and `reqNone` are
    innocently excludable. The SIs ¬reqAll and ¬reqNone arise. -/
theorem embedded_admits_si :
    predToFinset reqAll ∈ innocent.excluded reqAlts reqPrej ∧
    predToFinset reqNone ∈ innocent.excluded reqAlts reqPrej := by
  decide

/-- Eq. 40 (consequence): exhaustification narrows the embedded
    disjunction to the `reqEither` world — every accessible world has
    all or none, but not all the same way. -/
theorem embedded_exh_isolates_either :
    innocent.exh reqAlts reqPrej = {RWorld.reqEither} := by
  decide

end EmbeddedDisjunction


-- ============================================================
-- SECTION 7: §5.1 — Relevance closure ⟹ C cannot break symmetry
-- ============================================================

/-!
## Why C cannot break symmetry (constraint 28)

Eq. 28 is derived in @cite{fox-katzir-2011} §5.1 from the relevance-
closure conditions of eq. 50. The theorem itself lives on its theory-
neutral substrate in `Alternatives/Symmetric.lean` (it predates F&K and
is used across the post-2011 exhaustification literature); we re-state
it here so the paper anchor surfaces it.

`Alternatives.Symmetric.context_cannot_break_symmetry` — if a
`RelevanceClosure` is closed under negation and conjunction (eq. 50),
and both `S` and `S₁` are relevant, then `S ∧ ¬S₁` is also relevant.
Combined with `Symmetric.symmetric_complement`
(`S ∧ ¬S₁ ≡ S₂` whenever `S₁`, `S₂` are symmetric alternatives of `S`),
this forces `S₂` to be relevant whenever `S₁` is — so contextual
restriction cannot keep one symmetric alternative while eliminating the
other.
-/

theorem context_cannot_break_symmetry_FK2011 {W : Type}
    (rc : Alternatives.Symmetric.RelevanceClosure W)
    (s s₁ : W → Bool) (hs : rc.relevant s = true)
    (h₁ : rc.relevant s₁ = true) :
    rc.relevant (fun w => s w && !s₁ w) = true :=
  Alternatives.Symmetric.context_cannot_break_symmetry rc s s₁ hs h₁


end Alternatives.FoxKatzir2011
