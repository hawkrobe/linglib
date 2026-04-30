/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.OSL
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Computability.Subregular.Function.Hierarchy

/-!
# Meinhardt, Mai, Baković & McCollum (2024): ATR Harmony Subregular Classification

Worked example using the function-level subregular substrate
(`Core/Computability/Subregular/Function/`) to classify a fragment of
Eastern Nilotic ATR harmony per @cite{meinhardt-mai-bakovic-mccollum-2024}.

## The paper

@cite{meinhardt-mai-bakovic-mccollum-2024} (NLLT 42:1191-1232) propose a
tightening of the @cite{heinz-lai-2013} Weakly Deterministic (WD) function
class. Their thesis:

* **Bidirectional** iterative ATR harmony in Maasai and Turkana (Eastern
  Nilotic) is *attested* and **WD** — a composition of two subsequential
  FSTs reading from opposite directions, where the two passes do not
  interact in the technical sense the paper formalises (§5).
* Hypothetical *unbounded-circumambient* "sour grapes" patterns
  (@cite{wilson-2003}; @cite{wilson-2006}) are *unattested* and
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
4. Documents the **bidirectional upgrade** and its WD classification.
   Formal proof deferred to `Function/WeaklyDeterministic.lean` (in
   this PR), which lands both Heinz-Lai 2013 and Meinhardt et al. 2024
   definitions side-by-side per linglib's "make incompatibilities
   visible" thesis.

## What this file does NOT do

* Does not encode the full Maasai/Turkana paradigms — only the minimal
  pair sufficient to illustrate substrate use. Paper §§3–4 contains
  far richer data including back-rounding harmony interactions and
  exceptional roots.
* Does not prove sour-grapes patterns are non-deterministic
  (impossibility argument requires a sophisticated pumping-style
  reasoning, deferred to a follow-up dedicated to negative results).
* Does not encode the leftward pass or the bidirectional composition
  (substrate ready: `SFST.compose` from `Function/Subsequential.lean`
  and `IsLeftSubsequential.comp` from `Function/Hierarchy.lean` would
  be the building blocks; the WD predicate then certifies non-
  interaction of the two passes).
-/

namespace Phenomena.Phonology.Studies.MeinhardtEtAl2024

open Core.Computability.Subregular.Function

-- ============================================================================
-- § 1: Dominant/Recessive Alphabet
-- ============================================================================

/-- Minimal alphabet capturing the dominance-vs-recessive distinction
that drives Maasai ATR harmony per @cite{meinhardt-mai-bakovic-mccollum-2024}
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
@cite{chandlee-eyraud-heinz-2015} the canonical OSL fragment of
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
def rightwardATR : SFST Bool Seg Seg where
  initial := false
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
(@cite{chandlee-eyraud-heinz-2015}; @cite{meinhardt-mai-bakovic-mccollum-2024}
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
  ⟨Bool, rightwardATR, rfl⟩

/-- Since OSL ⊆ Left-Subsequential (`Function/Hierarchy.lean`), the OSL
classification automatically lifts. -/
theorem rightwardATR_osl_isLeftSubsequential :
    IsLeftSubsequential rightwardATR_osl.apply :=
  isLeftOutputStrictlyLocal_left_subsequential
    rightwardATR_osl_isLeftOutputStrictlyLocal

/-! ### Bidirectional Maasai harmony — WD classification

The full Maasai/Turkana pattern in (1a) is **bidirectional**: [+ATR]
spreads from a dominant root vowel both leftward and rightward, with
spread blocked by the opaque /a/ in either direction (per ex 1a-ii).
The bidirectional function is the composition of `rightwardATR`
(left-subsequential) with a `leftwardATR` (right-subsequential —
mirror image via `SFST.runRight`):

```
maasai := leftwardATR.runRight ∘ rightwardATR.run     -- (or vice versa)
```

@cite{meinhardt-mai-bakovic-mccollum-2024} call such *non-interacting*
two-pass compositions **Weakly Deterministic**. The non-interaction
condition is what their paper formalises and tightens compared to
@cite{heinz-lai-2013}'s original definition.

**Both definitions land in `Function/WeaklyDeterministic.lean`** (this
PR) per linglib's "make incompatibilities visible" thesis: the
`IsWeaklyDeterministic_HL2013` and `IsWeaklyDeterministic_MMBM2024`
predicates state the contested pair side-by-side. The Maasai
bidirectional function is claimed WD by both definitions; the
divergence point — sour-grapes-style functions admitted by HL2013 but
rejected by MMBM2024 — is where the patch matters.

Sour grapes harmony (@cite{wilson-2003}; @cite{wilson-2006}) — where
leftward spread fails *entirely* if blocked at any position — is the
canonical example of a function above WD: the inner (rightward) and
outer (leftward) passes interact, so no non-interacting two-pass
composition can compute it. The paper argues sour grapes is unattested
cross-linguistically; formalising the impossibility-of-WD claim is
deferred to a follow-up.
-/

end Phenomena.Phonology.Studies.MeinhardtEtAl2024
