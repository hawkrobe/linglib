import Linglib.Phonology.Segmental.Basic
import Linglib.Fragments.Latin.Phonology

/-!
# Sen (2015): Latin /l/ Allophony as Positional Underspecification [sen-2015]

Latin /l/ has clear ([l]) and dark ([ɫ]) realisations whose distribution
[sen-2015] ch. 2 analyses as positional underspecification of the
feature [back]. The chosen formal analysis (§2.4, eq. 23) settles on an
equipollent specification in which all three positional /l/ allophones
share a tongue-body-displacement feature [+high] while differing on
[back]: coda /l/ is [+high, +back] (dark), geminate /ll/ is
[+high, −back] (clear), and onset /l/ is [+high, Ø back] — left
unspecified for [back] and inheriting a surface value from the following
vowel by categorical spreading (cf. [keating-1988], with the
categorical-vs-gradient distinction discussed under Implementation notes).

This file derives the three positional /l/ allophones from the Latin
Fragment's single /l/ phoneme via `Segment.setFeature`, implements the
inheritance mechanism as categorical feature spreading through
`Segment.fillFromContext` (with the spreading theorem
`surfaceL_inherits_back` and worked surface theorems for onset /l/ before
each Latin short vowel), and proves the categorical context-invariance of
coda /l/ and geminate /ll/, illustrating that `fillFromContext` is
feature-filling rather than feature-overwriting.

## Main definitions

* `lWithDorsal` — the Fragment's /l/ with [+high] added (Sen's dorsal
  articulation, shared by all three positional allophones).
* `lOnset` — onset /l/: [+high, Ø back].
* `lCoda` — coda /l/: [+high, +back] (dark).
* `lGeminate` — geminate /ll/: [+high, −back] (clear).
* `surfaceL` — feature spreading applied to onset /l/.
* `surfaceCoda`, `surfaceGem` — spreading applied to the already-
  specified coda and geminate values (no-op for [back]).

## Main results

* `surfaceL_inherits_back` — onset /l/ takes its surface [back] value from
  the following segment.
* `surfaceL_before_{i,e,o,u}` — concrete realisations from the Fragment's
  four primary short vowels: clear before front vowels, dark before back
  vowels.
* `surfaceL_before_a` — Fragment/Sen divergence on /a/: the Fragment
  encodes /a/ as [Ø back] (Hayes 2009 convention), so the categorical
  model leaves onset /l/ at [Ø back]; Sen groups /a/ as a darkening
  context for onset /l/.
* `surfaceCoda_*`, `surfaceGem_*` — coda and geminate /l/ stay at their
  underlying [back] value regardless of context.

## Implementation notes

The Latin Fragment exposes a single /l/ phoneme. The three positional
allophones are derived here by `Segment.setFeature` on `Latin.Phonology.l`,
with the dorsal [+high] articulation that distinguishes /l/'s phonetic
profile factored into `lWithDorsal`. Sen's analysis treats this dorsal
raising as common to all three /l/ allophones — only [back] distinguishes
them at the underlying level.

The spreading theorems use `Segment.fillFromContext` rather than the
overwriting `Segment.setFeature`: the operation is *filling*, which
preserves the existing value of [back] on coda and geminate /l/ even when
they are followed by a vowel with a conflicting [back] specification. The
`surfaceCoda_*` and `surfaceGem_*` theorems witness this behaviour
end-to-end.

**Categorical vs. gradient layer.** This file formalises Sen's
*categorical* phonological analysis (eq. 19/23): the ternary [back]
underspecification, and the prediction that an unspecified target
inherits the immediately following specified value. Sen's full account
adds a *gradient phonetic interpolation* layer (§2.4-2.5, Fig. 2.3) in
which surface darkness varies along a gradient scale running from
darkest (coda) through onset /l/ before /a o u/, then /e/, then /e:/,
to clearest (onset before /i/ and geminate /ll/); in particular, onset
/l/ before /e/ is "dark" in Sen's gradient picture while the categorical
model formalised here has /l/ inherit /e/'s [−back] and surface "clear".
On p. 41 Sen explicitly rejects synchronic categorical feature spreading
as the *actuating* mechanism, on the grounds that it would over-predict
identical effects in identical-feature contexts; the substrate's
`fillFromContext` is exactly such a categorical operation — Keating's
schema (2) case (b) ([keating-1988] p. 287), in which the target
acquires a feature value from its neighbour, rather than her case (c)
gradient phonetic interpolation in which the target stays unspecified
and the phonetics builds a continuous trajectory through it. The
categorical underspecification claim is captured faithfully; the
gradient phonetic implementation, which is what Keating's own term
*interpolation* picks out, is out of scope.

**Fragment-vs-Sen divergence on /a/.** The Latin Fragment leaves /a/
unspecified for [back] (following [hayes-2009]'s convention that
low vowels carry no primary [back] value), so the categorical
`fillFromContext` leaves onset /l/ before /a/ at [Ø back]. Sen instead
groups /a/ with /o u/ as a darkening context for onset /l/ (§2.3.1,
Fig. 2.2), which would require either encoding /a/ as [+back] in Latin
or modelling Keating's propagation across the underspecified
intermediate. `surfaceL_before_a` records what the categorical model and
the Fragment's vowel inventory predict, not Sen's empirical claim.

**Diachronic content out of scope.** [sen-2015] also develops a
diachronic account (the historical loss of geminate /l/, inverse
compensatory lengthening, the prehistory of clear/dark /l/ split); this
study formalises only the synchronic underspecification analysis of
ch. 2. The parallel analysis for /r/ (vowel reduction before TR clusters)
in ch. 4 is also deferred.

## Todo

* Multi-segment interpolation across consonant + vowel sequences, once
  `Segment.fillFromContextTier` lands in the Underspec substrate.
* The parallel reduction analysis for /r/ (Sen ch. 4).
-/

namespace Sen2015

open Phonology Latin.Phonology

/-! ### Positional /l/ values

The Fragment's `l` lacks a [high] specification. Sen 2015 ch. 2 analyses
all three positional allophones as bearing [+high] (the dorsal articulation
that distinguishes /l/ from a pure alveolar). The three allophones diverge
on [back] alone: coda [+back], geminate [−back], onset [Ø back]. -/

/-- The Fragment's /l/ extended with the dorsal [+high] specification
common to all three positional allophones. -/
def lWithDorsal : Segment := l.setFeature .high true

/-- Onset /l/: [+high] with [back] left unspecified for Keating-style
interpolation from the following vowel. -/
def lOnset : Segment := lWithDorsal

/-- Coda /l/ (dark [ɫ]): [+high, +back]. -/
def lCoda : Segment := lWithDorsal.setFeature .back true

/-- Geminate /ll/ (clear [l]): [+high, −back]. -/
def lGeminate : Segment := lWithDorsal.setFeature .back false

/-! ### Underlying specification status -/

/-- Onset /l/ is unspecified for [back]: the Keating interpolation target. -/
theorem lOnset_unspecified_back : lOnset.Unspecified .back := by decide

/-- Coda /l/ is [+back] underlyingly (dark). -/
theorem lCoda_back : lCoda.HasValue .back true := by decide

/-- Geminate /l/ is [−back] underlyingly (clear). -/
theorem lGeminate_front : lGeminate.HasValue .back false := by decide

/-- All three positional /l/ allophones are [+high] (Sen's dorsal articulation). -/
theorem all_lAllophones_high :
    lOnset.HasValue .high true ∧ lCoda.HasValue .high true ∧
      lGeminate.HasValue .high true := by decide

/-! ### Keating interpolation on onset /l/

Onset /l/ inherits its surface [back] value from the following segment.
The general theorem `surfaceL_inherits_back` exhibits the mechanism; the
per-vowel theorems below are concrete instances. -/

/-- Surface form of onset /l/ before a context segment, via Keating
interpolation on [back]. -/
def surfaceL (ctx : Segment) : Segment := lOnset.fillFromContext .back ctx

/-- The key theorem: onset /l/'s surface [back] equals the following
segment's [back] value, by `fillFromContext` applied to an unspecified
target. -/
theorem surfaceL_inherits_back (ctx : Segment) :
    (surfaceL ctx) .back = ctx .back :=
  Segment.fillFromContext_apply_self_of_unspecified lOnset lOnset_unspecified_back ctx

/-- Onset /l/ before /i/ surfaces clear ([−back]): /i/ is [−back]. -/
theorem surfaceL_before_i : (surfaceL i).HasValue .back false := by decide

/-- Onset /l/ before /e/ inherits /e/'s [−back] in the categorical model,
predicting clear /l/. Sen's gradient phonetic analysis (Fig. 2.2, p. 33)
treats this context as "Dark" — relatively dark, dark enough to colour a
preceding vowel — a distinction the categorical layer formalised here
does not capture. -/
theorem surfaceL_before_e : (surfaceL e).HasValue .back false := by decide

/-- Onset /l/ before /o/ surfaces dark ([+back]): /o/ is [+back]. -/
theorem surfaceL_before_o : (surfaceL o).HasValue .back true := by decide

/-- Onset /l/ before /u/ surfaces dark ([+back]): /u/ is [+back]. -/
theorem surfaceL_before_u : (surfaceL u).HasValue .back true := by decide

/-- Fragment-vs-Sen divergence on /a/: the Latin Fragment encodes /a/ as
[Ø back] (Hayes 2009 convention for low vowels), so the categorical
`fillFromContext` leaves onset /l/ before /a/ at [Ø back]. Sen instead
groups /a/ with /o u/ as a darkening context for onset /l/; this theorem
records what the Fragment's vowel inventory and the categorical model
predict, not Sen's empirical claim. -/
theorem surfaceL_before_a : (surfaceL a).Unspecified .back := by decide

/-! ### Context-invariance of categorically-specified /l/

Coda /l/ and geminate /l/ have [back] specified underlyingly, so
`fillFromContext` is a no-op for them: they retain their categorical
[back] value regardless of the following segment. -/

/-- Surface form of coda /l/ in some right context. -/
def surfaceCoda (ctx : Segment) : Segment := lCoda.fillFromContext .back ctx

/-- Surface form of geminate /l/ in some right context. -/
def surfaceGem (ctx : Segment) : Segment := lGeminate.fillFromContext .back ctx

/-- Coda /l/ stays [+back] for any context, by `fillFromContext` applied
to an already-specified target. -/
theorem surfaceCoda_invariant (ctx : Segment) :
    (surfaceCoda ctx).HasValue .back true :=
  Segment.fillFromContext_apply_self_of_specified lCoda lCoda_back ctx

/-- Geminate /l/ stays [−back] for any context. -/
theorem surfaceGem_invariant (ctx : Segment) :
    (surfaceGem ctx).HasValue .back false :=
  Segment.fillFromContext_apply_self_of_specified lGeminate lGeminate_front ctx

/-- Concrete witness: coda /l/ followed by the front vowel /i/ stays dark,
contrasting with `surfaceL_before_i` where onset /l/ surfaces clear. -/
theorem surfaceCoda_before_i : (surfaceCoda i).HasValue .back true :=
  surfaceCoda_invariant i

/-- Concrete witness: geminate /l/ followed by the back vowel /o/ stays
clear, contrasting with `surfaceL_before_o` where onset /l/ surfaces dark. -/
theorem surfaceGem_before_o : (surfaceGem o).HasValue .back false :=
  surfaceGem_invariant o

/-! ### Cross-feature preservation

The interpolation modifies only [back]; the dorsal [+high] specification
and every other feature on onset /l/ pass through unchanged. -/

/-- Onset /l/'s [+high] dorsal articulation survives interpolation. -/
theorem surfaceL_high (ctx : Segment) : (surfaceL ctx).HasValue .high true := by
  have h : (surfaceL ctx) .high = lOnset .high :=
    Segment.fillFromContext_apply_of_ne lOnset (by decide : (Feature.back) ≠ .high) ctx
  show (surfaceL ctx) .high = some true
  rw [h]
  decide

end Sen2015
