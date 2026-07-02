/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.OSL
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Computability.Subregular.Function.LetterSubsequential
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# Meinhardt, Mai, Baković & McCollum (2024): ATR Harmony Subregular Classification

Worked example using the function-level subregular substrate
(`Core/Computability/Subregular/Function/`) to classify a fragment of
Eastern Nilotic ATR harmony per [meinhardt-mai-bakovic-mccollum-2024].

## The paper

[meinhardt-mai-bakovic-mccollum-2024] (NLLT 42:1191-1232) propose a
tightening of the [heinz-lai-2013] Weakly Deterministic (WD) function
class. Their thesis:

* **Bidirectional** iterative ATR harmony in Maasai and Turkana (Eastern
  Nilotic) is *attested* and **WD** — a composition of two subsequential
  FSTs reading from opposite directions, where the two passes do not
  interact in the technical sense the paper formalises (§5).
* Hypothetical *unbounded-circumambient* "sour grapes" patterns
  ([wilson-2003]; [wilson-2006]) are *unattested* and
  **non-deterministic** — the inner and outer passes interact, placing
  the function strictly above WD in the hierarchy (Fig. 1).
* The original Heinz-Lai 2013 WD definition was too permissive,
  admitting some unattested patterns; Meinhardt et al. patch it by
  formalising the *interaction* condition explicitly (§§5–6).

## Maasai dominant/recessive harmony (paper §3.1, p. 1203)

The empirically critical fact (paper p. 1203, "(non-exceptional)
dominant vowels are underlyingly specified for the spreading value of
the harmonic feature, [+ATR]"): **dominance is a lexical property of
the root**, independent of the surface ATR value of any individual
segment. A dominant root *triggers* spreading regardless of its
constituent vowels' phonetic ATR; a recessive root does not.

The bidirectional Maasai pattern (paper p. 1193, ex 1a):

* (i) Full bidirectional spreading from a dominant root: /kɪ-√noŋ-ʊ/ →
  [ki-√noŋ-u] '1pl-love-pres' — [+ATR] spreads from the (dominant)
  root in both directions, raising recessive prefix /ɪ/ to [i] and
  recessive suffix /ʊ/ to [u].
* (ii) Leftward spread blocked by /a/: /ɪ-√as-ɪʃɔ-rɛ/ → [ɪ-√as-iʃo-re]
  '2sg-do-intr-appl' — the spreading [+ATR] reaches the rightward
  vowels but is blocked leftward by the opaque /a/, leaving the prefix
  /ɪ/ unchanged.

## What this file does (audit-corrected)

Per CLAUDE.md "stimulus contrasts" discipline for Studies files:

1. Defines a 4-symbol alphabet `Seg` capturing the dominant/recessive
   distinction the paper insists is empirically load-bearing — the
   formaliser-invented alphabet from the previous version of this file
   (which conflated [+ATR] with the spreading trigger) is replaced.
2. Encodes the **rightward [+ATR] spreading** half of Maasai harmony
   as both a `SFST` and an `OSLRule`. Per paper §5.4 (p. 45), single-
   direction iterative spreading is **Output-Strictly-Local** — the
   output decision at each position depends on whether the immediately
   preceding **output** symbol is +ATR. The OSL classification is
   tighter than Left-Subsequential and is what the paper actually
   predicts for the unidirectional pass.
3. Decide-checks input/output examples corresponding to ex 1a-i and
   ex 1a-ii from the paper (encoded in the toy alphabet).
4. Proves the **bidirectional** dominant-recessive map `maasai` is
   **weakly deterministic** (`maasai_weaklyDeterministic`) via a
   non-interacting bimachine, yet unbounded-circumambient *as
   covariation* (`maasai_isUnboundedCircumambient`) — the same predicate
   Tutrugbu satisfies — while *not* `RequiresBothSides`
   (`maasai_not_requiresBothSides`). That asymmetry is the WD/ND boundary
   [meinhardt-mai-bakovic-mccollum-2024] draws.

## What this file does NOT do

* Does not encode the full Maasai/Turkana paradigms — only the minimal
  pair sufficient to illustrate substrate use. Paper §§3–4 contains
  far richer data including back-rounding harmony interactions and
  exceptional roots.
* Does not prove sour-grapes patterns are non-deterministic
  (impossibility argument requires a sophisticated pumping-style
  reasoning, deferred to a follow-up dedicated to negative results).
* Models the bidirectional map directly (`maasai`: raise a recessive iff
  a dominant occurs anywhere) rather than as an explicit two-pass
  composition `leftwardATR.runRight ∘ rightwardATR.run`, and omits the
  opaque /a/ blocking — the non-opaque core already exhibits weak
  determinism and the WD/ND covariation contrast.

## Scope note: cross-construction extrapolation

The OSL framing here characterises ATR harmony **within a single
spell-out domain** (root + affixes). [sande-clem-dabkowski-2026]
argue that ATR harmony in Guébie particle-verb focus-fronting
constructions is *also* local at the moment of spell-out but
*surface-discontinuous* after subsequent A′-movement. Their pattern
is not a counterexample to the OSL classification of root-internal
ATR harmony — the two analyses describe disjoint construction types
— but it does refute the broader extrapolation that "ATR harmony is
strictly local on the surface" universally. See
`Studies/SandeClemDabkowski2026.lean` for the
discontinuous case.
-/

namespace MeinhardtEtAl2024

open Subregular

-- ============================================================================
-- § 1: Dominant/Recessive Alphabet
-- ============================================================================

/-- Minimal alphabet capturing the dominance-vs-recessive distinction
that drives Maasai ATR harmony per [meinhardt-mai-bakovic-mccollum-2024]
p. 1203. Four symbols stand in for the relevant phonological contrasts:

* `recL` — a recessive [-ATR] vowel (e.g., /ɪ/, /ʊ/). Surfaces as
  [-ATR] absent harmony; raises to [+ATR] under spread.
* `recH` — a recessive [+ATR] vowel (e.g., /i/, /u/). Already [+ATR];
  passes spread through.
* `dom` — a dominant vowel. Triggers [+ATR] spread regardless of its
  own surface quality (the paper's load-bearing distinction).
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

-- ============================================================================
-- § 2: Rightward [+ATR] Spreading as an OSL Rule
-- ============================================================================

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

Per paper §5.4 (p. 45): single-direction iterative spreading patterns
are OSL but not ISL, because the output decision genuinely depends on
the *output* history (how spread has propagated) rather than the *input*
history alone. -/
def rightwardATR_osl : OSLRule 2 Seg Seg where
  windowOutput outputWindow currentInput :=
    match currentInput, outputWindow with
    | .a, _ => [.a]
    | .dom, _ => [.recH]
    | .recH, _ => [.recH]
    | .recL, .recH :: _ => [.recH]
    | .recL, _ => [.recL]

/-- Equivalent SFST for the same map: state tracks whether spread is
active. Demonstrates that the rule has both an OSL representation
(above) and a Subsequential representation (here) — the latter being
the umbrella class. -/
def rightwardATR : SFST Seg Seg Bool where
  start := false
  step spreading s :=
    match s with
    | .a => (false, [.a])
    | .dom => (true, [.recH])
    | .recH => (true, [.recH])
    | .recL => if spreading then (true, [.recH]) else (false, [.recL])
  finalOutput _ := []

-- ============================================================================
-- § 3: Worked Examples (paper p. 1193, ex 1a, simplified)
-- ============================================================================

/-- **Ex 1a-i (rightward half)**: the dominant root triggers spread to
the following recessive vowel.

Toy encoding of the rightward portion of /kɪ-√noŋ-ʊ/ → [ki-√noŋ-u]:
input `[dom, recL]` (a dominant root vowel followed by a recessive
suffix vowel) → output `[recH, recH]`. -/
example : rightwardATR.run [.dom, .recL] = [.recH, .recH] := by decide

example : rightwardATR_osl.apply [.dom, .recL] = [.recH, .recH] := by decide

/-- **Ex 1a-ii (rightward half)**: spread continues across multiple
recessive vowels. -/
example : rightwardATR.run [.dom, .recL, .recL] = [.recH, .recH, .recH] := by
  decide

example : rightwardATR_osl.apply [.dom, .recL, .recL] = [.recH, .recH, .recH] := by
  decide

/-- **Blocking**: /a/ blocks rightward spread; recessive vowels after
/a/ remain [-ATR]. -/
example : rightwardATR.run [.dom, .a, .recL] = [.recH, .a, .recL] := by decide

example : rightwardATR_osl.apply [.dom, .a, .recL] = [.recH, .a, .recL] := by
  decide

/-- **No spread without dominant trigger**: a string of recessive vowels
with no dominant root passes through unchanged. -/
example : rightwardATR.run [.recL, .recL] = [.recL, .recL] := by decide

example : rightwardATR_osl.apply [.recL, .recL] = [.recL, .recL] := by decide

/-- **Two SFSTs / OSL rules agree** on the encoded examples. (Full
extensional equivalence on all inputs would require a separate
induction; this is the expected agreement on paper-cited cases.) -/
example : rightwardATR.run [.dom, .recL, .a, .recL]
        = rightwardATR_osl.apply [.dom, .recL, .a, .recL] := by decide

-- ============================================================================
-- § 4: Subregular Classification
-- ============================================================================

/-- **Rightward [+ATR] spreading is Left-Output-Strictly-Local**
([chandlee-eyraud-heinz-2015]; [meinhardt-mai-bakovic-mccollum-2024]
§5.4). Witness: the OSL rule `rightwardATR_osl` defined above.

This is the **tighter** classification per the paper — single-direction
iterative spreading patterns are properly contained in OSL, strictly
above the ISL class but strictly below the (Left-)Subsequential class. -/
theorem rightwardATR_osl_isLeftOutputStrictlyLocal :
    IsLeftOutputStrictlyLocal 2 rightwardATR_osl.apply :=
  rightwardATR_osl.isLeftOutputStrictlyLocal_apply

/-- **Rightward [+ATR] spreading is also Left-Subsequential** (a weaker
claim than OSL but the umbrella class). Witness: the SFST. -/
theorem rightwardATR_isLeftSubsequential :
    IsLeftSubsequential rightwardATR.run :=
  rightwardATR.isLeftSubsequential

/-- Since OSL ⊆ Left-Subsequential (`Function/Hierarchy.lean`), the OSL
classification automatically lifts. -/
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
rules. Yet — like Tutrugbu — a recessive's surface ATR co-varies with information
unboundedly far on either side, so `maasai` *also* satisfies `IsUnboundedCircumambient`.
The contrast is exactly the WD/ND boundary the paper draws: both maps are circumambient
*as covariation*, but only Tutrugbu `RequiresBothSides` (suppression/conjunction). -/

open Subregular

/-- The word contains a dominant trigger. -/
def hasDom (xs : List Seg) : Bool := xs.any (· == .dom)

/-- Bidirectional dominant-recessive harmony (non-opaque core): a recessive raises iff the
word has a dominant trigger anywhere. -/
def maasai (xs : List Seg) : List Seg :=
  xs.map (fun s => if hasDom xs && s == .recL then .recH else s)

/-- The non-interacting bimachine: each side's state tracks a dominant seen on that side;
a recessive raises if *either* side has one — a union of one-sided rules. -/
def maasaiBM : Bimachine Bool Bool Seg Seg where
  lInit := false
  lStep l s := l || (s == .dom)
  rInit := false
  rStep r s := r || (s == .dom)
  out l s r := if (l || r) && s == .recL then .recH else s

/-- `maasaiBM`'s cell output is a `unite` of one-sided raise-rules. -/
theorem maasaiBM_isNonInteracting : maasaiBM.IsNonInteracting :=
  ⟨fun l s => if l && s == .recL then .recH else s,
   fun r s => if r && s == .recL then .recH else s, by
    intro l s r; cases s <;> cases l <;> cases r <;> rfl⟩

/-- The left state after a prefix is exactly "a dominant occurs in it". -/
theorem maasaiBM_lState (xs : List Seg) : maasaiBM.lState xs = xs.any (· == .dom) := by
  show xs.foldl (fun l s => l || (s == .dom)) false = xs.any (· == .dom)
  have : ∀ (acc : Bool) (ys : List Seg), ys.foldl (fun l s => l || (s == .dom)) acc
      = (acc || ys.any (· == .dom)) := by
    intro acc ys; induction ys generalizing acc with
    | nil => simp
    | cons y ys ih => simp [ih, Bool.or_assoc]
  simpa using this false xs

/-- The right state after a suffix is exactly "a dominant occurs in it". -/
theorem maasaiBM_rState (xs : List Seg) : maasaiBM.rState xs = xs.any (· == .dom) := by
  show xs.foldr (fun s r => r || (s == .dom)) false = xs.any (· == .dom)
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [ih, Bool.or_comm]

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
    maasaiBM.out (maasaiBM.lState (xs.take i)) xs[i] (maasaiBM.rState (xs.drop (i + 1)))
    = if hasDom xs && xs[i] == .recL then .recH else xs[i] := by
  rw [maasaiBM_lState, maasaiBM_rState, hasDom_split xs i hi]
  show (if (((xs.take i).any (· == .dom) || (xs.drop (i + 1)).any (· == .dom)) && xs[i] == .recL)
      then .recH else xs[i]) =
    (if (((xs.take i).any (· == .dom) || (xs.drop (i + 1)).any (· == .dom) || (xs[i] == .dom))
      && xs[i] == .recL) then .recH else xs[i])
  cases xs[i] <;> simp

/-- The bimachine computes `maasai`. -/
theorem maasaiBM_run : maasaiBM.run = maasai := by
  funext xs
  apply List.ext_getElem?
  intro i
  rw [maasaiBM.run_getElem?]
  rcases lt_or_ge i xs.length with hi | hi
  · rw [List.getElem?_eq_getElem hi, Option.map_some, maasaiBM_cell_eq xs i hi]
    simp only [maasai, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, hasDom]
  · rw [List.getElem?_eq_none hi, Option.map_none]
    simp only [maasai, List.getElem?_map, List.getElem?_eq_none (by simpa using hi),
      Option.map_none]

/-- **Maasai ATR harmony is weakly deterministic** ([meinhardt-mai-bakovic-mccollum-2024]):
the bidirectional dominant-recessive spread is a non-interacting bimachine. -/
theorem maasai_weaklyDeterministic : IsBimachineWeaklyDeterministic maasai :=
  maasaiBM_run ▸ isBimachineWeaklyDeterministic maasaiBM maasaiBM_isNonInteracting

/-- **Maasai is unbounded-circumambient *as covariation*** — at every distance, a medial
recessive's ATR flips under a dominant placed far to the left *or* far to the right. The
same predicate Tutrugbu satisfies (`tutrugbu_isUnboundedCircumambient`); the difference is
that Maasai does *not* `RequiresBothSides`. -/
theorem maasai_isUnboundedCircumambient : IsUnboundedCircumambient maasai := by
  intro d
  refine ⟨List.replicate (2 * d + 3) .recL, d + 1, by simp; omega, fun s => ?_⟩
  match s with
  | .left =>
    refine ⟨(List.replicate (2 * d + 3) .recL).set 0 .dom,
      ⟨by simp, fun k _ => by rw [List.getElem?_set_ne (by omega)]⟩, ?_⟩
    simp only [maasai]
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_set_ne (by omega : 0 ≠ d + 1)]
    have hd : hasDom ((List.replicate (2 * d + 3) .recL).set 0 .dom) = true := by
      simp only [hasDom, List.any_eq_true]
      exact ⟨Seg.dom, List.mem_set (by simp) Seg.dom, rfl⟩
    have hb : hasDom (List.replicate (2 * d + 3) .recL) = false := by simp [hasDom]
    simp [hd, hb, (by omega : d + 1 < 2 * d + 3)]
  | .right =>
    refine ⟨(List.replicate (2 * d + 3) .recL).set (2 * d + 2) .dom,
      ⟨by simp, fun k _ => by rw [List.getElem?_set_ne (by omega)]⟩, ?_⟩
    simp only [maasai]
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_set_ne (by omega : 2 * d + 2 ≠ d + 1)]
    have hd : hasDom ((List.replicate (2 * d + 3) .recL).set (2 * d + 2) .dom) = true := by
      simp only [hasDom, List.any_eq_true]
      exact ⟨Seg.dom, List.mem_set (by simp) Seg.dom, rfl⟩
    have hb : hasDom (List.replicate (2 * d + 3) .recL) = false := by simp [hasDom]
    simp [hd, hb, (by omega : d + 1 < 2 * d + 3)]

/-- Hence Maasai does **not** require both sides — it escapes the teeth, unlike Tutrugbu.
Covariation (both languages) and interaction (Tutrugbu only) come apart. -/
theorem maasai_not_requiresBothSides : ¬ RequiresBothSides maasai := fun h =>
  not_isBimachineWeaklyDeterministic_of_requiresBothSides h maasai_weaklyDeterministic

/-- **Strictness witness `subsequential ⊊ WD`**: Maasai is weakly deterministic yet *not*
left-subsequential. A synchronous left-subsequential map is right-myopic
(`IsLetterLeftSubsequential.isRightMyopic`), but Maasai's bidirectional spread is not
(`maasai_isUnboundedCircumambient`). -/
theorem maasai_not_letterLeftSubsequential : ¬ IsLetterLeftSubsequential maasai := fun h =>
  maasai_isUnboundedCircumambient.not_myopic .right h.isRightMyopic

end MeinhardtEtAl2024
