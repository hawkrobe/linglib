/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Linglib.Phonology.Harmony.Basic

/-!
# Aksënova, Rawski, Graf & Heinz 2024: the computational power of harmonic forms

[aksenova-rawski-graf-heinz-2024] §34.3.1 works out three double vowel
harmonies with their TSL grammars printed (Tables 34.3–34.5); a single tier
always suffices. This study transcribes the grammars featurally and
stress-tests `Phonology.Harmony.Pattern`: Kirghiz is the conjunction of two
patterns on one tier (`kirghiz_two_patterns`); Buryat's asymmetric blocking
defeats every symmetric relation (`buryat_not_symmetric`) — the finding that
forced blocker imposition into `Pattern.Compatible` — and with imposition is
expressible (`buryat_expressible`, certified on the (9) forms); Yakut's
harmonizing blockers show the same asymmetry (`yakut_asymmetric`); whether its
configuration-dependent grammar is a conjunction of patterns is left open.

Constructor names ASCII-ize the IPA: `ih` = ɨ, `oe` = ö, `ue` = ü, `oh` = ɔ,
`uh` = ʊ. TODO: the §34.3.4 tier-relation typology (same/embedded/disjoint
attested, partial overlap unattested) over Table 34.8's rows.
-/

namespace AksenovaEtAl2024

open Phonology.Harmony

/-! ### Kirghiz ((5), Table 34.3): double harmony, one tier, two patterns -/

/-- The Kirghiz vowel tier `T = {a, ɨ, e, i, o, ö, u, ü}`. -/
inductive KirghizV where
  | a | ih | e | i | o | oe | u | ue
  deriving DecidableEq, Fintype, Repr

namespace KirghizV

def front : KirghizV → Bool
  | .e | .i | .oe | .ue => true
  | .a | .ih | .o | .u => false

def round : KirghizV → Bool
  | .o | .oe | .u | .ue => true
  | .a | .ih | .e | .i => false

end KirghizV

/-- Table 34.3, featurally: pairs disagreeing in fronting or rounding. -/
def kirghizBanned (x y : KirghizV) : Prop :=
  x.front ≠ y.front ∨ x.round ≠ y.round

instance : DecidableRel kirghizBanned := fun x y => by
  unfold kirghizBanned; infer_instance

/-- Frontness harmony as a pattern: all vowels participate. -/
def kirghizFront : Pattern KirghizV Bool :=
  { value := fun v => some v.front, participation := fun _ => .participating }

/-- Rounding harmony as a pattern on the same tier. -/
def kirghizRound : Pattern KirghizV Bool :=
  { value := fun v => some v.round, participation := fun _ => .participating }

/-- Kirghiz's grammar is the conjunction of the two patterns' compatibilities. -/
theorem kirghiz_two_patterns (x y : KirghizV) :
    kirghizBanned x y ↔
      ¬ (kirghizFront.Compatible x y ∧ kirghizRound.Compatible x y) := by
  revert x y; decide

/-- Spot-checks against Table 34.3: `*ai`, `*oe` banned; `üö` licensed. -/
example : kirghizBanned .a .i ∧ kirghizBanned .o .e ∧
    ¬ kirghizBanned .ue .oe := by decide

/-! ### Buryat ((9), Table 34.4): asymmetric blocking defeats symmetry -/

/-- The Buryat vowel tier `T = {a, e, ɔ, o, ʊ, u}` (transparent /i/ excluded). -/
inductive BuryatV where
  | a | e | oh | o | uh | u
  deriving DecidableEq, Fintype, Repr

namespace BuryatV

def tense : BuryatV → Bool
  | .e | .o | .u => true
  | .a | .oh | .uh => false

def high : BuryatV → Bool
  | .uh | .u => true
  | .a | .e | .oh | .o => false

def round : BuryatV → Bool
  | .oh | .o | .uh | .u => true
  | .a | .e => false

end BuryatV

/-- Table 34.4's bans: ATR disagreement anywhere; rounding disagreement
    between non-high vowels; a rounded non-high vowel after a high vowel. -/
def buryatBanned (x y : BuryatV) : Prop :=
  x.tense ≠ y.tense ∨
    (¬ x.high ∧ ¬ y.high ∧ x.round ≠ y.round) ∨
    (x.high ∧ ¬ y.high ∧ y.round)

instance : DecidableRel buryatBanned := fun x y => by
  unfold buryatBanned; infer_instance

/-- The high-vowel blocking clause is asymmetric: `*ʊɔ` is banned but `ɔʊ`
    is fine ((9b)). -/
theorem buryat_asymmetric : buryatBanned .uh .oh ∧ ¬ buryatBanned .oh .uh := by
  decide

/-- No symmetric adjacency relation renders Buryat's grammar. -/
theorem buryat_not_symmetric (R : BuryatV → BuryatV → Prop)
    (hsymm : ∀ x y, R x y ↔ R y x) : ¬ ∀ x y, R x y ↔ buryatBanned x y := by
  intro h
  exact buryat_asymmetric.2 ((h _ _).mp ((hsymm _ _).mp ((h _ _).mpr
    buryat_asymmetric.1)))

/-- ATR harmony: all tier vowels participate. -/
def buryatATR : Pattern BuryatV Bool :=
  { value := fun v => some v.tense, participation := fun _ => .participating }

/-- Rounding harmony: high vowels are opaque blockers transmitting
    unroundedness to what follows. -/
def buryatRound : Pattern BuryatV Bool :=
  { value := fun v => some (if v.high then false else v.round)
    participation := fun v => if v.high then .opaque else .participating }

/-- With imposition, Buryat is expressible: the printed grammar is exactly
    the conjunction of the ATR pattern and the rounding pattern. -/
theorem buryat_expressible (x y : BuryatV) :
    buryatBanned x y ↔
      ¬ (buryatATR.Compatible x y ∧ buryatRound.Compatible x y) := by
  revert x y; decide

/-- Buryat well-formedness: harmonic for both patterns. -/
def buryatWellFormed (w : List BuryatV) : Prop :=
  buryatATR.Harmonic w ∧ buryatRound.Harmonic w

instance (w : List BuryatV) : Decidable (buryatWellFormed w) := by
  unfold buryatWellFormed; infer_instance

/-- The (9) forms as vowel skeletons: `ɔr-ɔːd` and `ɔr-ʊːl-aːd` are
    well-formed — the latter because the high causative transmits unroundedness
    to the perfective — while `*ɔr-aːd` and `*ɔr-ʊːl-ɔːd` are not. -/
example : buryatWellFormed [.oh, .oh] ∧ ¬ buryatWellFormed [.oh, .a] ∧
    buryatWellFormed [.oh, .uh, .a] ∧ ¬ buryatWellFormed [.oh, .uh, .oh] := by
  decide

/-! ### Yakut ((14), Table 34.5): harmonizing blockers -/

/-- The Yakut vowel tier `T = {a, ɨ, e, i, o, ö, u, ü}`. -/
inductive YakutV where
  | a | ih | e | i | o | oe | u | ue
  deriving DecidableEq, Repr

namespace YakutV

def front : YakutV → Bool
  | .e | .i | .oe | .ue => true
  | .a | .ih | .o | .u => false

def round : YakutV → Bool
  | .o | .oe | .u | .ue => true
  | .a | .ih | .e | .i => false

def high : YakutV → Bool
  | .ih | .i | .u | .ue => true
  | .a | .e | .o | .oe => false

end YakutV

/-- Table 34.5's bans: fronting disagreement anywhere; rounding disagreement
    between high vowels; a rounded non-high vowel after a high vowel; rounding
    disagreement after a non-high vowel. -/
def yakutBanned (x y : YakutV) : Prop :=
  x.front ≠ y.front ∨
    (x.high ∧ y.high ∧ x.round ≠ y.round) ∨
    (x.high ∧ ¬ y.high ∧ y.round) ∨
    (¬ x.high ∧ x.round ≠ y.round)

instance : DecidableRel yakutBanned := fun x y => by
  unfold yakutBanned; infer_instance

/-- Yakut's low vowels are harmonizing blockers ((14g)): rounding spreads
    from `o` to `u` but not from `u` to `o` — the icy-target configuration. -/
theorem yakut_asymmetric : yakutBanned .u .o ∧ ¬ yakutBanned .o .u := by decide

/-- Spot-checks against (14): `oɣo-lor`, `murum-u` licensed; `*tünnük-lör` banned. -/
example : ¬ yakutBanned .o .o ∧ ¬ yakutBanned .u .u ∧
    yakutBanned .ue .oe := by decide

end AksenovaEtAl2024
