/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.AR

/-!
# Tangale tone processes and the elision cascade

[kidda-1985]'s tonal and segmental rules that carry the perfective
focus-marking reflex of [hartmann-zimmermann-2004]. Tonemes are two
(H, L; §1.16); High Tone Spread (her (31)) links a boundary-adjacent
H one TBU rightward, creating a falling contour on the docked TBU,
and Left Line Delinking (her (35a), her coinage) then erases the
original line, shifting the H. Segmentally, final-vowel elision plus
u-epenthesis into the resulting final cluster produce the perfective
alternation *pon-go ~ pon-ug* (her (4a)): the suffix surfaces
faithful at a prosodic boundary and elided–repaired phrase-medially.
`boundary_audible` is the witness that blocking the cascade — the
prosodic reflex of [hartmann-zimmermann-2004]'s perfective focus —
is perceptible.
-/

namespace Tangale

open Autosegmental

/-- Tangale tonemes ([kidda-1985] §1.16): two levels; extralow is a
phonetic realization, and falling contours arise only from spread. -/
inductive Tone where
  | H | L
  deriving DecidableEq, Repr

variable {β : Type*}

/-- High Tone Spread ([kidda-1985] (31)): the toneme at `i` — an H
linked to TBU `j` at a morpheme or word boundary — spreads onto the
following TBU. The structural description is carried by the
application theorems. -/
def hts (g : Graph Tone β) (i j : ℕ) : Graph Tone β := g.link i (j + 1)

/-- Left Line Delinking ([kidda-1985] (35a)): erase the original
(left) line after the toneme has spread rightward. -/
def lld (g : Graph Tone β) (i j : ℕ) : Graph Tone β := g.delink i j

/-- Spread creates the falling contour (§4.6): the docked TBU
surfaces with H on top of whatever it already bore. -/
theorem hts_surfacesWith_H {g : Graph Tone β} {i j : ℕ}
    (hH : g.upper.get? i = some Tone.H) :
    (hts g i j).SurfacesWith Tone.H (j + 1) :=
  ⟨i, Finset.mem_insert_self _ _, hH⟩

/-- Spread followed by Left Line Delinking shifts the H one TBU
rightward ((34)): the docked TBU keeps the new line and the source
loses the original. -/
theorem lld_hts_shift {g : Graph Tone β} {i j : ℕ}
    (hH : g.upper.get? i = some Tone.H) :
    (lld (hts g i j) i j).SurfacesWith Tone.H (j + 1) ∧
    (i, j) ∉ (lld (hts g i j) i j).links := by
  refine ⟨⟨i, ?_, hH⟩, by simp [lld, hts]⟩
  simp [lld, hts]

/-- Blocking is representationally visible: where the spread line is
absent, applying HTS changes the graph. -/
theorem hts_ne_self {g : Graph Tone β} {i j : ℕ}
    (h : (i, j + 1) ∉ g.links) : hts g i j ≠ g :=
  fun he => h (he ▸ Finset.mem_insert_self _ _)

/-- 'Horse is good' ([kidda-1985] (29a) *tuužé koŋ*): H on the noun's
final TBU, L on the predicate. -/
def horseIsGood : Graph Tone Unit :=
  ⟨.ofList [Tone.H, Tone.L], .ofList [(), (), ()], {(0, 1), (1, 2)}⟩

/-- After HTS the predicate TBU bears both H and L — the falling
contour of *tụụzẹ́ kôŋ*, realized as such pause-finally ((29a)). -/
example :
    (hts horseIsGood 0 1).SurfacesWith Tone.H 2 ∧
    (hts horseIsGood 0 1).SurfacesWith Tone.L 2 := by decide

/-! ### The elision cascade (Ch. 2)

Final-vowel elision builds consonant clusters; the cluster
constraints then force u-epenthesis. On the perfective suffix this
yields [kidda-1985]'s (4a) alternation `pón-é + gó → pon-go`
(clause-final, faithful) vs `pon-ug` (phrase-medial, elided and
repaired) — the alternation whose blocking under focus is
[hartmann-zimmermann-2004]'s prosodic reflex. -/

/-- CV slots for the cluster phonotactics. -/
inductive Slot where
  | C | V
  deriving DecidableEq, Repr

/-- The cluster constraints ([kidda-1985] p. 64): initial clusters
are impermissible, medial three-consonant clusters are disallowed,
and word-final clusters are not permitted. -/
def Phonotactic (w : List Slot) : Prop :=
  ¬ [Slot.C, Slot.C] <+: w ∧
  ¬ [Slot.C, Slot.C, Slot.C] <:+: w ∧
  ¬ [Slot.C, Slot.C] <:+ w

instance (w : List Slot) : Decidable (Phonotactic w) :=
  inferInstanceAs (Decidable (¬ _ ∧ ¬ _ ∧ ¬ _))

/-- Final-vowel elision (§2.2): delete a word-final vowel. Triggered
by suffixation, compounding, and phrase-medial position; blocked at
a prosodic boundary. -/
def ve (w : List Slot) : List Slot :=
  if w.getLast? = some Slot.V then w.dropLast else w

/-- u-epenthesis ((4)): repair a word-final cluster by inserting the
vowel between the penultimate and ultimate consonants. -/
def epenthesize (w : List Slot) : List Slot :=
  if [Slot.C, Slot.C] <:+ w then w.dropLast ++ [Slot.V, Slot.C] else w

/-- *pón-é* 'knew' ((4a)). -/
def ponE : List Slot := [.C, .V, .C, .V]
/-- The perfective suffix *gó*. -/
def go : List Slot := [.C, .V]

/-- The boundary form: word-internal elision only; the suffix
surfaces faithful (*pon-go*; before a focused constituent,
*wai-gó lánda* of [hartmann-zimmermann-2004] (25)). -/
def blockedForm : List Slot := ve ponE ++ go

/-- The phrase-medial form: phrasal elision hits the suffix vowel and
epenthesis repairs the final cluster (*pon-ug ŋâi* 'knew Ngai'). -/
def elidedForm : List Slot := epenthesize (ve (ve ponE ++ go))

/-- The cascade is audible: both outputs are phonotactically licit
and they differ — blocking phrasal elision (the prosodic boundary
of the perfective focus reflex) is perceptible. -/
theorem boundary_audible :
    blockedForm ≠ elidedForm ∧
    Phonotactic blockedForm ∧ Phonotactic elidedForm := by decide

end Tangale
