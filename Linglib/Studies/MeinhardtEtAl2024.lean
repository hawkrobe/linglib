/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Mealy
import Linglib.Phonology.Subregular.ISL
import Linglib.Phonology.Subregular.OSL
import Linglib.Core.Computability.Subsequential
import Linglib.Phonology.Subregular.Dependence
import Linglib.Core.Computability.Bimachine

/-!
# Meinhardt, Mai, Baković and McCollum (2024): Weak Determinism and ATR Harmony

This file formalizes the Maasai case of [meinhardt-mai-bakovic-mccollum-2024], which
tightens the weakly deterministic function class of [heinz-lai-2013] by an explicit
interaction condition. Bidirectional iterative ATR harmony in Maasai is attested and weakly
deterministic, an unbounded semiambient pattern in which every target depends on one side
at a time, so its two contradirectional subsequential passes do not interact; Turkana,
identical but for exceptionally dominant retracted suffix vowels, is attested and
non-deterministic, an unbounded circumambient pattern in which some targets depend on both
sides at once. Dominance is an underlying specification of the spreading value on vowels,
carried by roots and suffixes alike. The rightward spreading pass is output-strictly-local
after [chandlee-eyraud-heinz-2015], the bidirectional dominant–recessive map is weakly
deterministic through a non-interacting bimachine (`maasai_weaklyDeterministic`) with
two-sided unbounded dependence (`maasai_twoSidedUnboundedDependence`) but without
requiring both sides at once (`maasai_not_requiresBothSides`), the boundary the paper draws.

## Implementation notes

The alphabet has four symbols carrying the dominant–recessive distinction; the bidirectional
map is modelled directly, raising a recessive vowel when a dominant one occurs anywhere,
rather than as a two-pass composition, and the opaque low vowel, the re-paired low vowel,
glide effects, and the Turkana half of the paper are not represented.

## TODO

The paper is not on file; page and example locators are transcribed from an earlier version
of this file and are UNVERIFIED.

## References

* [meinhardt-mai-bakovic-mccollum-2024]
* [heinz-lai-2013]
* [chandlee-eyraud-heinz-2015]
* [wilson-2006]
-/

namespace MeinhardtEtAl2024

open Subregular

/-- Minimal alphabet capturing the dominance-vs-recessive distinction
that drives Maasai ATR harmony per [meinhardt-mai-bakovic-mccollum-2024]
p. 1203. Four symbols stand in for the relevant phonological contrasts:

* `recL` — a recessive [-ATR] vowel (e.g., /ɪ/, /ʊ/). Surfaces as
  [-ATR] absent harmony; raises to [+ATR] under spread.
* `recH` — a recessive vowel surfacing [+ATR] (e.g., /i/, /u/): the
  raised form of `recL`, and transparent to further spread.
* `dom` — a dominant vowel: underlyingly specified [+ATR], the trigger
  of spreading (the paper's load-bearing distinction).
* `a` — the opaque /a/. Blocks spread.

Consonants are omitted as they are transparent to the harmony. -/
inductive Seg
  | recL
  | recH
  | dom
  | a
  deriving DecidableEq, Repr

instance : Fintype Seg where
  elems := {.recL, .recH, .dom, .a}
  complete := λ x => by cases x <;> simp

namespace Seg

/-- Whether the segment is a [+ATR] vowel (after surface realisation).
A `dom` segment surfaces as [+ATR] by definition; `recH` is underlyingly
[+ATR]; `recL` is [-ATR] (until raised by spread); `a` is neither. -/
def isPlusATR : Seg → Bool
  | .recH | .dom => true
  | _ => false

/-- Surface form of a segment under spreading [+ATR]: recessive [-ATR]
vowels raise; everything else passes through unchanged (including the
opaque /a/, which blocks the spread that would have reached it). -/
def raise : Seg → Seg
  | .recL => .recH
  | s => s

end Seg

/-- **OSL rule encoding rightward [+ATR] spreading from a dominant root.**

The rule's k = 2: the output decision at each position depends on the
**single immediately preceding output symbol** (per
[chandlee-eyraud-heinz-2015] the canonical OSL fragment of
phonological maps). Rule logic:

* Current input is `dom` → emit `recH` (dominant always surfaces as
  [+ATR]).
* Current input is `a` → emit `a` (opaque, blocks spread; the next
  position's output context will be `a`, not a +ATR vowel).
* Current input is `recH` → emit `recH` (already +ATR, passes through).
* Current input is `recL` and previous output was `recH` → emit `recH`
  (spread continues).
* Current input is `recL` otherwise → emit `recL` (no spread to here).

Single-direction iterative spreading patterns are OSL but not ISL
([chandlee-eyraud-heinz-2015]), because the output decision genuinely
depends on the *output* history (how spread has propagated) rather than
the *input* history alone. -/
def rightwardATR_osl : OSLRule 2 Seg Seg where
  windowOutput outputWindow currentInput :=
    match currentInput, outputWindow with
    | .a, _ => [.a]
    | .dom, _ => [.recH]
    | .recH, _ => [.recH]
    | .recL, .recH :: _ => [.recH]
    | .recL, _ => [.recL]

/-- **Ex 1a-i (rightward half)**: the dominant root triggers spread to
the following recessive vowel.

Toy encoding of the rightward portion of /kɪ-√noŋ-ʊ/ → [ki-√noŋ-u]:
input `[dom, recL]` (a dominant root vowel followed by a recessive
suffix vowel) → output `[recH, recH]`. -/
example : rightwardATR_osl.apply [.dom, .recL] = [.recH, .recH] := by decide

/-- **Ex 1a-ii (rightward half)**: spread continues across multiple
recessive vowels. -/
example : rightwardATR_osl.apply [.dom, .recL, .recL] = [.recH, .recH, .recH] := by
  decide

/-- **Blocking**: /a/ blocks rightward spread; recessive vowels after
/a/ remain [-ATR]. -/
example : rightwardATR_osl.apply [.dom, .a, .recL] = [.recH, .a, .recL] := by
  decide

/-- **No spread without dominant trigger**: a string of recessive vowels
with no dominant root passes through unchanged. -/
example : rightwardATR_osl.apply [.recL, .recL] = [.recL, .recL] := by decide

/-- **Rightward [+ATR] spreading is Left-Output-Strictly-Local**
([chandlee-eyraud-heinz-2015], the result
[meinhardt-mai-bakovic-mccollum-2024] builds on). Witness: the OSL rule
`rightwardATR_osl` defined above.

This is the **tighter** classification per the paper — single-direction
iterative spreading patterns are properly contained in OSL, strictly
above the ISL class but strictly below the (Left-)Subsequential class. -/
theorem rightwardATR_osl_isLeftOutputStrictlyLocal :
    IsLeftOutputStrictlyLocal 2 rightwardATR_osl.apply :=
  rightwardATR_osl.isLeftOutputStrictlyLocal_apply

/-- **Rightward [+ATR] spreading is also Left-Subsequential** — the umbrella class,
lifted from the OSL classification via OSL ⊆ Left-Subsequential
(`isLeftOutputStrictlyLocal_left_subsequential`). -/
theorem rightwardATR_osl_isLeftSubsequential :
    IsLeftSubsequential rightwardATR_osl.apply :=
  isLeftOutputStrictlyLocal_left_subsequential
    rightwardATR_osl_isLeftOutputStrictlyLocal

/-! ### Bidirectional Maasai harmony — weakly deterministic (faithful)

Maasai dominant-recessive ATR harmony spreads [+ATR] from a dominant root to recessive
vowels on *both* sides. Modelled here in its non-opaque core: a recessive `recL` raises
to `recH` iff the word contains a dominant vowel anywhere (`maasai`). This is a *union*
of two independent spreading passes, so it is **weakly deterministic**
([meinhardt-mai-bakovic-mccollum-2024], unbounded *semiambient*): the bimachine `maasaiBM`
tracks a dominant seen on each side and its output is literally a `unite` of one-sided
rules. A recessive's surface ATR still co-varies with information unboundedly far on
either side, so `maasai` satisfies `TwoSidedUnboundedDependence` — as does Tutrugbu. The
contrast is exactly the WD/ND boundary the paper draws: only Tutrugbu is *circumambient*,
needing both sides at once (`RequiresBothSides`), which Maasai never does. -/

open Subregular

/-- The word contains a dominant trigger. -/
def hasDom (xs : List Seg) : Bool := xs.any (· == .dom)

/-- Bidirectional dominant-recessive harmony (non-opaque core): a recessive raises iff the
word has a dominant trigger anywhere. -/
def maasai (xs : List Seg) : List Seg :=
  xs.map (λ s => if hasDom xs && s == .recL then .recH else s)

/-- The non-interacting bimachine: each side's state tracks a dominant seen on that side;
a recessive raises if *either* side has one — a union of one-sided rules. -/
def maasaiBM : Bimachine Bool Bool Seg Seg :=
  .ofFlags (· == .dom) (· == .dom) λ l s r => if (l || r) && s == .recL then .recH else s

/-- `maasaiBM`'s cell output is a `unite` of one-sided raise-rules. -/
theorem maasaiBM_isNonInteracting : maasaiBM.IsNonInteracting :=
  ⟨⟨λ l s => if l && s == .recL then .recH else s,
    λ r s => if r && s == .recL then .recH else s,
    by decide, by intro l s r; cases s <;> cases l <;> cases r <;> rfl⟩⟩

private theorem hasDom_split (xs : List Seg) (i : ℕ) (hi : i < xs.length) :
    hasDom xs = (hasDom (xs.take i) || hasDom (xs.drop (i + 1)) || (xs[i] == .dom)) := by
  simp only [hasDom]
  have heq : xs = xs.take i ++ [xs[i]] ++ xs.drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop]
  conv_lhs => rw [heq]
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  cases (xs.take i).any (· == .dom) <;> cases (xs.drop (i + 1)).any (· == .dom) <;>
    cases (xs[i] == Seg.dom) <;> rfl

private theorem maasaiBM_cell_eq (xs : List Seg) (i : ℕ) (hi : i < xs.length) :
    (if (((xs.take i).any (· == .dom) || (xs.drop (i + 1)).any (· == .dom))
        && xs[i] == .recL) then Seg.recH else xs[i])
    = if hasDom xs && xs[i] == .recL then .recH else xs[i] := by
  rw [hasDom_split xs i hi]
  cases xs[i] <;> simp [hasDom]

/-- The bimachine computes `maasai`. -/
theorem maasaiBM_run : maasaiBM.run = maasai := by
  funext xs
  apply List.ext_getElem?
  intro i
  rw [maasaiBM, Bimachine.getElem?_ofFlags_run]
  rcases lt_or_ge i xs.length with hi | hi
  · rw [List.getElem?_eq_getElem hi, Option.map_some, maasaiBM_cell_eq xs i hi]
    simp only [maasai, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, hasDom]
  · rw [List.getElem?_eq_none hi, Option.map_none]
    simp only [maasai, List.getElem?_map, List.getElem?_eq_none (by simpa using hi),
      Option.map_none]

/-- **Maasai ATR harmony is weakly deterministic** ([meinhardt-mai-bakovic-mccollum-2024]):
the bidirectional dominant-recessive spread is a non-interacting bimachine. -/
theorem maasai_weaklyDeterministic : IsNonInteractingBimachineComputable maasai :=
  maasaiBM_run ▸ maasaiBM.isNonInteractingBimachineComputable maasaiBM_isNonInteracting

/-- **Maasai has two-sided unbounded dependence** — at every distance, a medial
recessive's ATR flips under a dominant placed far to the left *or* far to the right,
each side alone sufficing. Tutrugbu satisfies this too
(`tutrugbu_twoSidedUnboundedDependence`); the difference is that Maasai does *not*
`RequiresBothSides`, so it stays weakly deterministic. The paper's positive
classification of Maasai as unbounded *semiambient* — every target fixed by information
from at most one side — is the stronger claim, `maasai_semiambient`. -/
theorem maasai_twoSidedUnboundedDependence : TwoSidedUnboundedDependence maasai := by
  refine .of_flanks (fill := Seg.recL) (xOn := Seg.recL) (yOn := Seg.recL)
    (xOff := Seg.dom) (yOff := Seg.dom)
    (n := λ d => 2 * d + 1) (t := λ d => d + 1)
    (λ d => by omega) (λ d => by omega) (λ d => ?_) (λ d => ?_) <;>
  · have hb : hasDom (flankWord Seg.recL Seg.recL Seg.recL (2 * d + 1)) = false := by
      simp [hasDom, flankWord]
    have hp : ∀ y, hasDom (flankWord Seg.dom Seg.recL y (2 * d + 1)) = true := λ y => by
      simp [hasDom, flankWord]
    have hp' : ∀ x, hasDom (flankWord x Seg.recL Seg.dom (2 * d + 1)) = true := λ x => by
      simp [hasDom, flankWord]
    simp only [maasai, List.getElem?_map,
      getElem?_flankWord_mid (show 0 < d + 1 by omega) (show d + 1 ≤ 2 * d + 1 by omega),
      hb, hp, hp']
    decide

/-- **Maasai is semiambient** — the paper's positive classification: every harmonised
cell is licensed by one side alone, the far dominant that triggers it. -/
theorem maasai_semiambient : OneSidedChanges maasai :=
  maasai_weaklyDeterministic.oneSidedChanges

/-- Hence Maasai does **not** require both sides — it escapes the teeth, unlike Tutrugbu.
Covariation (both languages) and interaction (Tutrugbu only) come apart. -/
theorem maasai_not_requiresBothSides : ¬ RequiresBothSides maasai := λ h =>
  h.not_isNonInteractingBimachineComputable maasai_weaklyDeterministic

/-- Strictness witness `synchronous ⊊ WD`: Maasai is weakly deterministic yet not
Mealy-computable — the length-preserving-stratum reading of [heinz-lai-2013]'s
`LSF, RSF ⊆ WD` corollary being strict, with `maasai` as their own dominant-recessive
witness (their Thms. 6 and 7). A Mealy-computable map is right-myopic
(`IsMealyComputable.boundedDependence_right`), but Maasai's bidirectional spread is not
(`maasai_twoSidedUnboundedDependence`); the block-class exclusion is
`maasai_not_leftSubsequential`. -/
theorem maasai_not_mealyComputable : ¬ IsMealyComputable maasai := λ h =>
  maasai_twoSidedUnboundedDependence.unboundedDependence .right h.boundedDependence_right

/-- **Maasai is not left-subsequential** — the *block* class is excluded too: `maasai`
is length-preserving, so a left-subsequential computer's delay bound would cap its
right dependence (`IsLeftSubsequential.boundedDependence_right`), but the spread's
right dependence is unbounded. -/
theorem maasai_not_leftSubsequential : ¬ IsLeftSubsequential maasai := λ h =>
  maasai_twoSidedUnboundedDependence.unboundedDependence .right
    (h.boundedDependence_right λ xs => by simp [maasai])

end MeinhardtEtAl2024
