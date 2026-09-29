/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Mealy
public import Linglib.Phonology.Subregular.ISL
public import Linglib.Phonology.Subregular.OSL
public import Linglib.Core.Computability.Subsequential
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Core.Computability.Bimachine

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

## References

* [meinhardt-mai-bakovic-mccollum-2024]
* [heinz-lai-2013]
* [chandlee-eyraud-heinz-2015]
* [wilson-2006]
-/

@[expose] public section

namespace MeinhardtEtAl2024

open Subregular

/-- Minimal alphabet capturing the dominance-vs-recessive distinction
that drives Maasai ATR harmony per [meinhardt-mai-bakovic-mccollum-2024]
p. 1203. Four symbols stand in for the relevant phonological contrasts.

* `recL` — a recessive [-ATR] vowel (e.g., /ɪ/, /ʊ/), surfacing as
  [-ATR] absent harmony and raising to [+ATR] under spread.
* `recH` — a recessive vowel surfacing [+ATR] (e.g., /i/, /u/), the
  raised form of `recL`, and transparent to further spread.
* `dom` — a dominant vowel, underlyingly specified [+ATR] and the trigger
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
  complete := fun x ↦ by cases x <;> simp

namespace Seg

/-- Whether the segment is a [+ATR] vowel after surface realisation, which holds of `dom` and
`recH` and fails of `recL` (until raised by spread) and of `a`. -/
def isPlusATR : Seg → Bool
  | .recH | .dom => true
  | _ => false

/-- The surface form of a segment under spreading [+ATR], which raises recessive [-ATR] vowels
and passes everything else through unchanged, including the opaque /a/. -/
def raise : Seg → Seg
  | .recL => .recH
  | s => s

end Seg

/-- **OSL rule encoding rightward [+ATR] spreading from a dominant root.**

With k = 2 the output decision at each position depends on the
**single immediately preceding output symbol**, as in the canonical OSL fragment of
phonological maps of [chandlee-eyraud-heinz-2015]. The rule emits as follows.

* Current input is `dom` → emit `recH` (dominant always surfaces as
  [+ATR]).
* Current input is `a` → emit `a` (opaque, blocks spread; the next
  position's output context will be `a`, not a +ATR vowel).
* Current input is `recH` → emit `recH` (already +ATR, passes through).
* Current input is `recL` and previous output was `recH` → emit `recH`
  (spread continues).
* Current input is `recL` otherwise → emit `recL` (no spread to here).

Single-direction iterative spreading patterns are OSL but not ISL
([chandlee-eyraud-heinz-2015]), because the output decision depends on the
*output* history (how far spread has propagated) rather than the *input*
history alone (`rightwardATR_osl_not_isLeftInputStrictlyLocal`). -/
def rightwardATR_osl : OSLRule 2 Seg Seg where
  windowOutput outputWindow currentInput :=
    match currentInput, outputWindow with
    | .a, _ => [.a]
    | .dom, _ => [.recH]
    | .recH, _ => [.recH]
    | .recL, .recH :: _ => [.recH]
    | .recL, _ => [.recL]

/-- The dominant root triggers spread to the following recessive vowel (Ex 1a-i, rightward
half), in a toy encoding of the rightward portion of /kɪ-√noŋ-ʊ/ → [ki-√noŋ-u] as input
`[dom, recL]` and output `[recH, recH]`. -/
example : rightwardATR_osl.apply [.dom, .recL] = [.recH, .recH] := by decide

/-- Spread continues across multiple recessive vowels (Ex 1a-ii, rightward half). -/
example : rightwardATR_osl.apply [.dom, .recL, .recL] = [.recH, .recH, .recH] := by
  decide

/-- The opaque /a/ blocks rightward spread, so recessive vowels after it remain [-ATR]. -/
example : rightwardATR_osl.apply [.dom, .a, .recL] = [.recH, .a, .recL] := by
  decide

/-- Without a dominant trigger, a string of recessive vowels passes through unchanged. -/
example : rightwardATR_osl.apply [.recL, .recL] = [.recL, .recL] := by decide

/-- **Rightward [+ATR] spreading is Left-Output-Strictly-Local**, witnessed by
`rightwardATR_osl` ([chandlee-eyraud-heinz-2015], the result
[meinhardt-mai-bakovic-mccollum-2024] builds on). -/
theorem rightwardATR_osl_isLeftOutputStrictlyLocal :
    IsLeftOutputStrictlyLocal 2 rightwardATR_osl.apply :=
  rightwardATR_osl.isLeftOutputStrictlyLocal_apply

private theorem rightwardATR_osl_apply_dom_replicate (n : ℕ) :
    rightwardATR_osl.apply (.dom :: List.replicate n .recL) = List.replicate (n + 1) .recH := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', ← List.cons_append, OSLRule.apply_append_singleton, ih,
      List.replicate_succ' (n := n + 1), List.replicate_succ', List.rtake_concat_succ,
      List.rtake_zero, List.nil_append]
    rfl

private theorem rightwardATR_osl_apply_replicate (n : ℕ) :
    rightwardATR_osl.apply (List.replicate n .recL) = List.replicate n .recL := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', OSLRule.apply_append_singleton, ih]
    cases n with
    | zero => rfl
    | succ m =>
      rw [List.replicate_succ', List.rtake_concat_succ, List.rtake_zero, List.nil_append]
      rfl

/-- **Rightward [+ATR] spreading is not Input-Strictly-Local** for any window, since a
dominant vowel followed by `k - 1` recessive ones and `k` recessive vowels end in the same
`k - 1` input segments while a further recessive vowel raises only after the first. -/
theorem rightwardATR_osl_not_isLeftInputStrictlyLocal (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k rightwardATR_osl.apply := fun h ↦ by
  have hw : ∀ s : Seg, (s :: List.replicate (k - 1) .recL).rtake (k - 1) =
      List.replicate (k - 1) .recL := fun s ↦ by
    simpa using List.rtake_append_length (l₁ := [s]) (l₂ := List.replicate (k - 1) Seg.recL)
  have e := congrFun (h.factorsThrough_residual (a := .dom :: List.replicate (k - 1) .recL)
    (b := .recL :: List.replicate (k - 1) .recL) (by simp only [hw])) [.recL]
  rw [Function.residual_eq_drop (h.isPrefix _), Function.residual_eq_drop (h.isPrefix _)] at e
  simp only [List.cons_append, ← List.replicate_succ',
    rightwardATR_osl_apply_dom_replicate, ← List.replicate_succ,
    rightwardATR_osl_apply_replicate, List.length_replicate, List.drop_replicate,
    Nat.add_sub_cancel_left] at e
  exact absurd e (by decide)

/-- **Rightward [+ATR] spreading is also Left-Subsequential**, through OSL ⊆
Left-Subsequential (`IsLeftOutputStrictlyLocal.isLeftSubsequential`). -/
theorem rightwardATR_osl_isLeftSubsequential :
    IsLeftSubsequential rightwardATR_osl.apply :=
  rightwardATR_osl_isLeftOutputStrictlyLocal.isLeftSubsequential

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

/-- Bidirectional dominant-recessive harmony in its non-opaque core, under which a recessive
raises iff the word has a dominant trigger anywhere. -/
def maasai (xs : List Seg) : List Seg :=
  xs.map (fun s ↦ if hasDom xs && s == .recL then .recH else s)

/-- The non-interacting bimachine, whose state on each side tracks a dominant seen on that
side, raising a recessive if *either* side has one as a union of one-sided rules. -/
def maasaiBM : Bimachine Bool Bool Seg Seg :=
  .ofFlags (· == .dom) (· == .dom) fun l s r ↦ if (l || r) && s == .recL then .recH else s

/-- `maasaiBM`'s cell output is a `unite` of one-sided raise-rules. -/
theorem maasaiBM_isNonInteracting : maasaiBM.IsNonInteracting :=
  ⟨⟨fun l s ↦ if l && s == .recL then .recH else s,
    fun r s ↦ if r && s == .recL then .recH else s,
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

/-- **Maasai ATR harmony is weakly deterministic**, the bidirectional dominant-recessive
spread being a non-interacting bimachine ([meinhardt-mai-bakovic-mccollum-2024]). -/
theorem maasai_weaklyDeterministic : IsNonInteractingBimachineComputable maasai :=
  maasaiBM_run ▸ maasaiBM.isNonInteractingBimachineComputable maasaiBM_isNonInteracting

/-- **Maasai has two-sided unbounded dependence** — at every distance, a medial
recessive's ATR flips under a dominant placed far to the left *or* far to the right,
each side alone sufficing. Tutrugbu satisfies this too
(`tutrugbu_twoSidedUnboundedDependence`), but Maasai does *not*
`RequiresBothSides`, so it stays weakly deterministic. The paper's positive
classification of Maasai as unbounded *semiambient*, with every target fixed by information
from at most one side, is the stronger claim `maasai_semiambient`. -/
theorem maasai_twoSidedUnboundedDependence : TwoSidedUnboundedDependence maasai := by
  refine .of_flanks (fill := Seg.recL) (xOn := Seg.recL) (yOn := Seg.recL)
    (xOff := Seg.dom) (yOff := Seg.dom)
    (n := fun d ↦ 2 * d + 1) (t := fun d ↦ d + 1)
    (fun d ↦ by omega) (fun d ↦ by omega) (fun d ↦ ?_) (fun d ↦ ?_) <;>
  · have hb : hasDom (flankWord Seg.recL Seg.recL Seg.recL (2 * d + 1)) = false := by
      simp [hasDom, flankWord]
    have hp : ∀ y, hasDom (flankWord Seg.dom Seg.recL y (2 * d + 1)) = true := fun y ↦ by
      simp [hasDom, flankWord]
    have hp' : ∀ x, hasDom (flankWord x Seg.recL Seg.dom (2 * d + 1)) = true := fun x ↦ by
      simp [hasDom, flankWord]
    simp only [maasai, List.getElem?_map,
      getElem?_flankWord_mid (show 0 < d + 1 by omega) (show d + 1 ≤ 2 * d + 1 by omega),
      hb, hp, hp']
    decide

/-- **Maasai is semiambient**, the paper's positive classification, with every harmonised
cell licensed by one side alone, the far dominant that triggers it. -/
theorem maasai_semiambient : OneSidedChanges maasai :=
  maasai_weaklyDeterministic.oneSidedChanges

/-- Hence Maasai does **not** require both sides — it escapes the teeth, unlike Tutrugbu.
Covariation (both languages) and interaction (Tutrugbu only) come apart. -/
theorem maasai_not_requiresBothSides : ¬ RequiresBothSides maasai := fun h ↦
  h.not_isNonInteractingBimachineComputable maasai_weaklyDeterministic

/-- Maasai is weakly deterministic yet not Mealy-computable, witnessing
`synchronous ⊊ WD` in the length-preserving-stratum reading of [heinz-lai-2013]'s
`LSF, RSF ⊆ WD` corollary being strict, with `maasai` as their own dominant-recessive
witness (their Thms. 6 and 7). A Mealy-computable map is right-myopic
(`IsMealyComputable.boundedDependence_right`), but Maasai's bidirectional spread is not
(`maasai_twoSidedUnboundedDependence`), and the block class is excluded by
`maasai_not_leftSubsequential`. -/
theorem maasai_not_mealyComputable : ¬ IsMealyComputable maasai := fun h ↦
  maasai_twoSidedUnboundedDependence.unboundedDependence .right h.boundedDependence_right

/-- **Maasai is not left-subsequential**, excluding the *block* class too, since `maasai`
is length-preserving, so a left-subsequential computer's delay bound would cap its
right dependence (`IsLeftSubsequential.boundedDependence_right`), but the spread's
right dependence is unbounded. -/
theorem maasai_not_leftSubsequential : ¬ IsLeftSubsequential maasai := fun h ↦
  maasai_twoSidedUnboundedDependence.unboundedDependence .right
    (h.boundedDependence_right fun xs ↦ by simp [maasai])

end MeinhardtEtAl2024
