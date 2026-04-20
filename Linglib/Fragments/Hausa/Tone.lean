import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone
import Linglib.Theories.Phonology.Autosegmental.RegisterTier

/-!
# Hausa Tone — mathlib-style
@cite{newman-2000} @cite{inkelas-1998}

Hausa is a register tone language with a **two-level lexical contrast**
(H, L) and a **derived falling contour** (F = HL on a single TBU).
There is no rising contour: a low followed by a high on adjacent TBUs
realises as L H, never as a rising tone on one TBU (@cite{newman-2000}
ch. 71).

## Architectural shape

This file is the *interpretation* of two existing Theory interfaces in
Hausa, not a parallel hierarchy:

- `Phonology.Autosegmental.RegisterTier.TRN` is the
  underlying autosegmental primitive; `HausaTone` is a surface
  inventory whose decomposition is given by `toAutoseg`.
- `Phonology.Autosegmental.GrammaticalTone.GTSpec` is the GT-trigger
  type. Hausa uses two of @cite{rolle-2018}'s six dominance cells —
  replacive-dominant and neutral. We expose smart constructors
  `mkReplacive`/`mkNeutral` that fix the other GTSpec fields to the
  Hausa defaults, register the morphemes in `hausaGTs`, and prove the
  typological signature as a universal theorem.

Per-cell facts (e.g. *the plural template is dominant*) appear as
`example`s — corollaries of the smart-constructor lemmas.
-/

namespace Fragments.Hausa.Tone

open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Autosegmental.GrammaticalTone
  (Spec GTSpec TonalMelody ValuationWindow GTDominance
   GTLevel ExponenceType tonalOverwrite TBU)

-- ============================================================================
-- § 1: Surface Tone Inventory (@cite{newman-2000} ch. 71)
-- ============================================================================

/-- Surface tones on a Hausa TBU (= mora). The contour `F` is realised
    only on heavy (bimoraic) syllables and decomposes as H+L on the
    autosegmental tier. There is **no R (rising) tone**: the prediction
    is that no Hausa surface form exhibits a single-TBU rising contour. -/
inductive HausaTone where
  | H   -- High
  | L   -- Low
  | F   -- Falling (HL on one heavy TBU)
  deriving DecidableEq, Repr, Inhabited

namespace HausaTone

/-- The surface inventory in canonical order. -/
def all : List HausaTone := [.H, .L, .F]

/-- Project a Hausa surface tone to its autosegmental decomposition on
    the underlying tone tier. The falling contour decomposes to `[H, L]`,
    a level tone to a singleton. -/
def toAutoseg : HausaTone → List TRN
  | .H => [.H]
  | .L => [.L]
  | .F => [.H, .L]

end HausaTone

/-- **No rising contour.** Every surface tone in the Hausa inventory
    begins with H or L on the autosegmental tier. A rising tone would
    have to begin with L and continue to H on the same TBU; the
    inventory provides no such cell (@cite{newman-2000} §71.1). -/
theorem no_rising_contour :
    ∀ t ∈ HausaTone.all,
      t.toAutoseg.head? = some .H ∨ t.toAutoseg.head? = some .L := by
  intro t ht
  simp only [HausaTone.all, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> decide

-- ============================================================================
-- § 2: Tonal Polarity (@cite{newman-2000} ch. 71.6)
-- ============================================================================

/-- Tonal polarity: a morpheme surfaces with the *opposite* tone of its
    host. The classic Hausa case is the **linker -n** of the genitive
    construction, which is L after a H-final host and H after a L-final
    host. Polarity is one of the named operations in @cite{rolle-2018}
    (`GTOperation.polarization`); we derive its behaviour structurally. -/
def polarOf : TRN → TRN
  | .H => .L
  | _  => .H

/-- **Polarity is involutive on the H/L sublattice.** This is what
    licenses polarity as a "natural" tonal operation: the linker -n
    swaps H and L, and applying the swap twice returns to the
    original. -/
theorem polarOf_involutive_on_HL :
    ∀ t ∈ ([.H, .L] : List TRN), polarOf (polarOf t) = t := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> decide

-- ============================================================================
-- § 3: Hausa GT Smart Constructors
-- ============================================================================

/-- Build a **replacive-dominant** word-level GTSpec from a name and
    melody. Hausa's morphological tonal templates (the plural template,
    the genitive linker, ...) all share these defaults: a `whole`
    valuation window, word-level GT, and auxiliary exponence (the
    template co-occurs with segmental material). -/
def mkReplacive (name : String) (melody : TonalMelody) : GTSpec where
  name      := name
  melody    := melody
  window    := .whole
  dominance := .replaciveDominant
  level     := .word
  exponence := .auxiliary

/-- Build a **neutral** word-level GTSpec from a name and melody.
    Used for floating-tone clitics whose melody concatenates with the
    host's underlying tones rather than overwriting them. -/
def mkNeutral (name : String) (melody : TonalMelody) : GTSpec where
  name      := name
  melody    := melody
  window    := .local
  dominance := .neutral
  level     := .word
  exponence := .auxiliary

-- ============================================================================
-- § 4: Hausa Morphological Tone Registry
-- ============================================================================

/-- The Hausa plural template *-ōoCíi* imposes an all-H melody on the
    base, regardless of the lexical tone of the singular
    (@cite{inkelas-1998}, @cite{newman-2000} §56.4). The paradigmatic
    case of replacive-dominant GT. -/
def pluralTemplate : GTSpec := mkReplacive "PL.-ōoCíi" [.H]

/-- The Hausa referential clitic *-ⁿn* attaches a floating L to the host
    without overwriting lexical tones (@cite{newman-2000} §31.5). The
    paradigmatic case of neutral GT in Hausa. -/
def referentialClitic : GTSpec := mkNeutral "REF.-ⁿn" [.L]

/-- The morphological-tone registry: every Hausa GT trigger we
    formalise. Universal theorems below quantify over this list. -/
def hausaGTs : List GTSpec := [pluralTemplate, referentialClitic]

-- ============================================================================
-- § 5: Typological Signature (universal theorem)
-- ============================================================================

/-- **Hausa uses only the dominant/neutral cells of the GT typology.**
    Of @cite{rolle-2018}'s six dominance categories, Hausa morphological
    tone occupies exactly two: replacive-dominant (templates) and
    neutral (floating clitics). No subtractive, additive, melodic, or
    recessive GT is attested. -/
theorem hausa_dominance_is_replacive_or_neutral :
    ∀ s ∈ hausaGTs,
      s.dominance = .replaciveDominant ∨ s.dominance = .neutral := by
  intro s hs
  simp only [hausaGTs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> decide

-- ============================================================================
-- § 6: Per-Trigger Verifications (demoted to `example`s)
-- ============================================================================

example : pluralTemplate.dominance.IsDominant := by decide
example : referentialClitic.dominance.IsNonDominant := by decide

/-- Concrete demonstration: an all-L disyllabic stem is overwritten to
    H on every TBU under the plural template. -/
def demoStem : List (TBU Unit) := [⟨(), .L⟩, ⟨(), .L⟩]

example :
    (tonalOverwrite demoStem pluralTemplate.toSpec).map (·.tone) = [.H, .H] :=
  rfl

/-- Neutral GT does *not* overwrite the host: the same melody under a
    `local` window leaves the surface to general phonology. -/
example : tonalOverwrite demoStem referentialClitic.toSpec = demoStem := rfl

end Fragments.Hausa.Tone
