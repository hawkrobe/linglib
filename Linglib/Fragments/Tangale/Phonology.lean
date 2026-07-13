/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Junction

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

open Autosegmental

/-- High Tone Spread ([kidda-1985] (31)) on the link presentation: the toneme
    at `i` — an H linked to TBU `j` at a morpheme or word boundary — spreads
    onto the following TBU. -/
def hts (L : Bool → Bool → ℕ → ℕ → Prop) (i j : ℕ) (b b' : Bool) (p q : ℕ) : Prop :=
  L b b' p q ∨ b = true ∧ b' = false ∧ p = i ∧ q = j + 1

/-- Left Line Delinking ([kidda-1985] (35a)): erase the original (left) line
    after the toneme has spread rightward. -/
def lld (L : Bool → Bool → ℕ → ℕ → Prop) (i j : ℕ) (b b' : Bool) (p q : ℕ) : Prop :=
  L b b' p q ∧ ¬ (b = true ∧ b' = false ∧ p = i ∧ q = j)

variable {ws : ∀ b, List (TwoTier Tone Unit b)} {L : Bool → Bool → ℕ → ℕ → Prop}

/-- Spread creates the falling contour (§4.6): the docked TBU surfaces with H
    on top of whatever it already bore. -/
theorem hts_surfacesWith_H {i j : ℕ} (hH : (ws true)[i]? = some Tone.H)
    (hj : j + 1 < (ws false).length) :
    (AR.ofData ws (hts L i j)).surfacesWith Tone.H (j + 1) := by
  rcases List.getElem?_eq_some_iff.mp hH with ⟨hi, -⟩
  refine ⟨i, (AR.link_ofData true false i (j + 1)).mpr
    ⟨by decide, hi, hj, Or.inl (Or.inr ⟨rfl, rfl, rfl, rfl⟩)⟩, ?_⟩
  rw [AR.tierWord_ofData]
  exact hH

/-- Spread followed by Left Line Delinking shifts the H one TBU rightward
    ((34)): the docked TBU keeps the new line and the source loses the
    original. -/
theorem lld_hts_shift {i j : ℕ} (hH : (ws true)[i]? = some Tone.H)
    (hj : j + 1 < (ws false).length) (hne : j + 1 ≠ j)
    (hor : ∀ p q, ¬ L false true p q) :
    (AR.ofData ws (lld (hts L i j) i j)).surfacesWith Tone.H (j + 1) ∧
      ¬ (AR.ofData ws (lld (hts L i j) i j)).link true false i j := by
  rcases List.getElem?_eq_some_iff.mp hH with ⟨hi, -⟩
  constructor
  · refine ⟨i, (AR.link_ofData true false i (j + 1)).mpr
      ⟨by decide, hi, hj, Or.inl ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, ?_⟩⟩, ?_⟩
    · rintro ⟨-, -, -, h⟩
      exact hne h
    · rw [AR.tierWord_ofData]
      exact hH
  · rintro h
    rcases (AR.link_ofData true false i j).mp h with
      ⟨-, -, -, ⟨-, hno⟩ | ⟨hraw | ⟨hfalse, -⟩, -⟩⟩
    · exact hno ⟨rfl, rfl, rfl, rfl⟩
    · exact hor _ _ hraw
    · exact absurd hfalse (by decide)

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
