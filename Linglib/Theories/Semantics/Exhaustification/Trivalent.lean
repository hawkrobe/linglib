import Linglib.Theories.Semantics.Exhaustification.Fox2007
import Linglib.Core.Logic.Truth3

/-!
# Trivalent Exhaustification
@cite{spector-sudo-2017}

Benjamin Spector and Yasutada Sudo, "Presupposed Ignorance and
Exhaustification: How Scalar Implicatures and Presuppositions Interact."
*Linguistics and Philosophy* 40, pp. 473–517.

## Core Operators

Two trivalent exhaustification operators extend bivalent EXH
(@cite{fox-2007}) to handle presupposition-bearing sentences:

- **EXH¹** (weak negation): `~ψ = true` when `ψ` is undefined →
  does NOT import presuppositions from alternatives
- **EXH²** (strong negation): `~ψ = #` when `ψ` is undefined →
  DOES import presuppositions from alternatives

Both reuse the same innocently excludable (IE) alternatives
computed by Fox's algorithm on the classical truth conditions.

## Connection to Presupposition Projection

@cite{wang-davidson-2026} show that this distinction is empirically
consequential for presupposition filtering across disjunction:
- EXH² + any projection theory predicts that exclusive disjunction
  increases projection (Type A)
- EXH¹ + any projection theory predicts no effect of exclusivity
  on projection (Type B)

Their Mandarin experiment finds no effect of exclusivity on filtering,
consistent with Type B (EXH¹).

## Design

This file is generic infrastructure, not a paper replication.
The IE computation reuses `Fox2007.ieIndices` (computable, Bool-based).
The trivalent layer wraps the bivalent IE result with `Truth3` semantics.
-/

namespace Exhaustification.Trivalent

open Core.Duality (Truth3 Prop3)
open Exhaustification.Fox2007


-- ════════════════════════════════════════════════════════════════
-- § 1. Classical extraction
-- ════════════════════════════════════════════════════════════════

/-- Extract the classical (bivalent) truth conditions from a
    trivalent proposition: `true` maps to `true`; `false` and
    `indet` both map to `false`.

    The IE computation operates on these classical truth conditions —
    entailment, consistency, and maximality are all defined bivalently.
    The trivalent layer applies only *after* IE is computed. -/
def classicalPart {W : Type} (p : W → Truth3) : W → Bool :=
  fun w => p w == .true


-- ════════════════════════════════════════════════════════════════
-- § 2. EXH¹ — weak-negation exhaustification
-- ════════════════════════════════════════════════════════════════

/-- Trivalent EXH¹ (weak negation).

    @cite{spector-sudo-2017}'s weak-negation operator (reproduced
    as (4)/(5) in @cite{wang-davidson-2026}):
    - Presupposes whatever φ presupposes: φ(w)=# → EXH¹(w)=#
    - Asserts φ and weakly negates all IE alternatives
    - Weak negation: `~# = true`, so alternatives' presuppositions
      do NOT project through EXH¹

    Type B in @cite{wang-davidson-2026}: predicts no effect of
    exclusivity on presupposition filtering. -/
def exh1 {W : Type} [BEq W] (domain : List W) (alts : List (W → Truth3))
    (p : W → Truth3) : W → Truth3 :=
  let boolAlts := alts.map classicalPart
  let ie := ieIndices domain (classicalPart p) boolAlts
  fun w => match p w with
    | .indet => .indet
    | .false => .false
    | .true =>
      -- Weak negation: ψ(w) ≠ true suffices (indet counts as "negated")
      if ie.all fun i => match alts[i]? with
        | some q => q w != .true
        | none => true
      then .true
      else .false


-- ════════════════════════════════════════════════════════════════
-- § 3. EXH² — strong-negation exhaustification
-- ════════════════════════════════════════════════════════════════

/-- Trivalent EXH² (strong negation).

    @cite{spector-sudo-2017}'s strong-negation operator (reproduced
    as (6)/(7) in @cite{wang-davidson-2026}):
    - Presupposes whatever φ presupposes AND whatever the negated
      IE alternatives presuppose
    - Asserts φ and strongly negates all IE alternatives
    - Strong negation: `~# = #`, so alternatives' presuppositions
      DO project through EXH²

    Type A in @cite{wang-davidson-2026}: predicts that increasing
    exclusivity reduces presupposition filtering. -/
def exh2 {W : Type} [BEq W] (domain : List W) (alts : List (W → Truth3))
    (p : W → Truth3) : W → Truth3 :=
  let boolAlts := alts.map classicalPart
  let ie := ieIndices domain (classicalPart p) boolAlts
  fun w =>
    -- Strong negation: any IE alternative undefined → result undefined
    if ie.any fun i => match alts[i]? with
      | some q => q w == .indet
      | none => false
    then .indet
    else match p w with
      | .indet => .indet
      | .false => .false
      | .true =>
        -- Strong negation: all IE alternatives must be false (not indet)
        if ie.all fun i => match alts[i]? with
          | some q => q w == .false
          | none => true
        then .true
        else .false


-- ════════════════════════════════════════════════════════════════
-- § 4. Key properties
-- ════════════════════════════════════════════════════════════════

/-- EXH¹ preserves the presupposition of the prejacent:
    if φ(w) = #, then EXH¹(φ)(w) = #. -/
theorem exh1_preserves_presup {W : Type} [BEq W] (domain : List W)
    (alts : List (W → Truth3)) (p : W → Truth3) (w : W)
    (h : p w = .indet) : exh1 domain alts p w = .indet := by
  unfold exh1; simp only [h]

/-- EXH² also preserves the prejacent's presupposition. -/
theorem exh2_preserves_presup {W : Type} [BEq W] (domain : List W)
    (alts : List (W → Truth3)) (p : W → Truth3) (w : W)
    (h : p w = .indet) : exh2 domain alts p w = .indet := by
  unfold exh2; split <;> simp_all


-- ════════════════════════════════════════════════════════════════
-- § 5. Concrete verification: disjunction with presupposition
-- ════════════════════════════════════════════════════════════════

/-!
### Bathroom disjunction example

"φ or ψ" where ψ presupposes π and ¬φ entails π.

Using the four-world model from Fox2007.lean (`PQWorld`), we add
a presupposition to q: q is defined only when p is false (i.e.,
the presupposition π = ¬p holds). This is the "bathroom disjunction"
pattern used in @cite{wang-davidson-2026}'s experiment.
-/

section BathroomDisjunction

/-- Three worlds for a bathroom disjunction:
    - `pOnly`: p true, q's presupposition fails (#)
    - `qOnly`: p false, q true (presupposition satisfied)
    - `neither`: p false, q false (presupposition satisfied) -/
inductive BathWorld where
  | pOnly | qOnly | neither
  deriving Repr, DecidableEq, BEq

def bDomain : List BathWorld := [.pOnly, .qOnly, .neither]

/-- p: always defined (no presupposition). -/
def pT3 : BathWorld → Truth3
  | .pOnly => .true
  | _ => .false

/-- q: presupposes ¬p (defined only when p is false). -/
def qT3 : BathWorld → Truth3
  | .pOnly => .indet  -- presupposition failure
  | .qOnly => .true
  | .neither => .false

/-- Inclusive disjunction under Strong Kleene allows filtering:
    at `pOnly`, p is true and q is undefined, but `join` returns true.
    The second disjunct's presupposition is "filtered". -/
theorem inclusive_allows_filtering :
    Truth3.join (pT3 .pOnly) (qT3 .pOnly) = .true := by rfl

/-- Exclusive disjunction does NOT allow filtering:
    at `pOnly`, `xor` returns undefined because q's value is unknown. -/
theorem exclusive_no_filtering :
    Truth3.xor (pT3 .pOnly) (qT3 .pOnly) = .indet := by rfl

/-- Inclusive disjunction as Prop3 (Strong Kleene). -/
def inclDisj : BathWorld → Truth3 := fun w => Truth3.join (pT3 w) (qT3 w)

/-- Exclusive disjunction as Prop3 (Strong Kleene). -/
def exclDisj : BathWorld → Truth3 := fun w => Truth3.xor (pT3 w) (qT3 w)

/-- Inclusive disjunction is defined at pOnly (filtering). -/
theorem incl_defined_at_pOnly : inclDisj .pOnly = .true := by rfl

/-- Exclusive disjunction is undefined at pOnly (no filtering). -/
theorem excl_undef_at_pOnly : exclDisj .pOnly = .indet := by rfl

/-- EXH¹ applied to inclusive disjunction: the presupposition
    is unchanged because EXH¹ uses weak negation.

    The alternatives are {p∨q, p, q, p∧q}. The conjunction
    alternative p∧q is the only IE alternative (by Fox 2007).
    Since p∧q is undefined at pOnly (q is undefined there),
    weak negation treats ~(p∧q) as true → no new presupposition. -/

def bathAlts : List (BathWorld → Truth3) :=
  [ inclDisj, pT3, qT3
  , fun w => Truth3.meet (pT3 w) (qT3 w) ]

theorem exh1_disjunction_pOnly :
    exh1 bDomain bathAlts inclDisj .pOnly = .true := by native_decide

/-- EXH² applied to inclusive disjunction: the conjunction
    alternative p∧q is undefined at pOnly, so strong negation
    makes EXH² undefined there → presupposition imported. -/
theorem exh2_disjunction_pOnly :
    exh2 bDomain bathAlts inclDisj .pOnly = .indet := by native_decide

end BathroomDisjunction


end Exhaustification.Trivalent
