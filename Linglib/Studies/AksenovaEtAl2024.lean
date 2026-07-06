/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Linglib.Phonology.Harmony.Basic

/-!
# Aksënova, Rawski, Graf & Heinz 2024: the computational power of harmonic forms

[aksenova-rawski-graf-heinz-2024] survey the subregular characterization of
harmony: strictly local grammars cannot express it (unbounded distance),
strictly piecewise grammars cannot express blocking, and tier-based strictly
local grammars capture both. Their §34.3.1 works out three double vowel
harmonies with the full TSL grammars printed (their Tables 34.3–34.5), showing
a single tier always suffices for double VH.

This study transcribes the three grammars featurally (the tables' banned-bigram
sets are their extensions) and stress-tests `Phonology.Harmony.Pattern` against
them:

* **Kirghiz** ((5), Table 34.3): frontness and rounding spread together over
  all vowels. Expressible — the grammar is exactly the conjunction of two
  `Pattern` compatibilities on the same tier (`kirghiz_two_patterns`).
* **Buryat** ((9), Table 34.4): ATR harmony over all vowels; rounding agreement
  among non-high vowels, blocked by high vowels. The blocking clause
  `*[+high][−high,+round]` is **asymmetric**, and `Pattern.Compatible` is
  symmetric — so no pattern, nor any conjunction of patterns, renders Buryat's
  grammar (`buryat_not_symmetric`, `buryat_no_pattern`).
* **Yakut** ((14), Table 34.5): fronting over all vowels; rounding spreads
  high→high and nonhigh→any, but not high→low — low vowels are harmonizing
  blockers (the icy-target class of `Phonology.Harmony.Participation`), and the
  ban `*[+high][−high,+round]` is again asymmetric (`yakut_asymmetric`).

The Buryat/Yakut findings are the stress-test payload: the pattern layer's
symmetric adjacent-compatibility semantics covers plain and double harmony with
symmetric blocking, but directional blocker-imposition requires the asymmetric
relation of the underlying forbidden-pairs machinery
(`Subregular.TSLGrammar.ofForbiddenPairs` takes an arbitrary `R`).

Vowel constructor names ASCII-ize the chapter's IPA: `ih` = ɨ, `oe` = ö,
`ue` = ü, `oh` = ɔ, `uh` = ʊ. The chapter's §34.3.4 tier-relation typology
(same/embedded/disjoint attested, partial overlap unattested) is not yet
formalized here. TODO: `TierRelation` classifier over Table 34.8's rows.
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

/-- Table 34.3's banned bigrams, featurally: any tier-adjacent pair disagreeing
    in fronting or rounding. -/
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

/-- Kirghiz's printed grammar is the conjunction of the two patterns'
    compatibilities: double harmony on a single tier, as the chapter says. -/
theorem kirghiz_two_patterns (x y : KirghizV) :
    kirghizBanned x y ↔
      ¬ (kirghizFront.Compatible x y ∧ kirghizRound.Compatible x y) := by
  revert x y; decide

/-- Spot-checks against Table 34.3's extension: `*ai` and `*oe` are banned,
    `üö` (agreeing in both features) is not. -/
example : kirghizBanned .a .i ∧ kirghizBanned .o .e ∧
    ¬ kirghizBanned .ue .oe := by decide

/-! ### Buryat ((9), Table 34.4): asymmetric blocking defeats symmetry -/

/-- The Buryat vowel tier `T = {a, e, ɔ, o, ʊ, u}` (transparent /i/ excluded). -/
inductive BuryatV where
  | a | e | oh | o | uh | u
  deriving DecidableEq, Repr

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

/-- Table 34.4's banned bigrams, featurally: ATR disagreement (`H_ATR`),
    rounding disagreement between non-high vowels (`H_r1`), and a rounded
    non-high vowel after a high vowel (`H_r2`). -/
def buryatBanned (x y : BuryatV) : Prop :=
  x.tense ≠ y.tense ∨
    (¬ x.high ∧ ¬ y.high ∧ x.round ≠ y.round) ∨
    (x.high ∧ ¬ y.high ∧ y.round)

instance : DecidableRel buryatBanned := fun x y => by
  unfold buryatBanned; infer_instance

/-- The `H_r2` clause is asymmetric: `*ʊɔ` is banned but `ɔʊ` is fine
    ((9b): the perfective no longer agrees in rounding across the high
    causative). -/
theorem buryat_asymmetric : buryatBanned .uh .oh ∧ ¬ buryatBanned .oh .uh := by
  decide

/-- No symmetric adjacency relation renders Buryat's grammar. -/
theorem buryat_not_symmetric (R : BuryatV → BuryatV → Prop)
    (hsymm : ∀ x y, R x y ↔ R y x) : ¬ ∀ x y, R x y ↔ buryatBanned x y := by
  intro h
  exact buryat_asymmetric.2 ((h _ _).mp ((hsymm _ _).mp ((h _ _).mpr
    buryat_asymmetric.1)))

/-- In particular no single `Pattern`'s incompatibility does
    (`Pattern.Compatible` is symmetric) — nor any conjunction of patterns,
    since symmetric relations are closed under conjunction. -/
theorem buryat_no_pattern (p : Pattern BuryatV Bool) :
    ¬ ∀ x y, ¬ p.Compatible x y ↔ buryatBanned x y :=
  buryat_not_symmetric _ fun _ _ => not_congr Pattern.compatible_comm

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

/-- Table 34.5's banned bigrams, featurally: fronting disagreement (`H_front`),
    rounding disagreement between high vowels (`H_r1`), a rounded low vowel
    after a high vowel (`H_r2`), and rounding disagreement after a non-high
    vowel (`H_r3`). -/
def yakutBanned (x y : YakutV) : Prop :=
  x.front ≠ y.front ∨
    (x.high ∧ y.high ∧ x.round ≠ y.round) ∨
    (x.high ∧ ¬ y.high ∧ y.round) ∨
    (¬ x.high ∧ x.round ≠ y.round)

instance : DecidableRel yakutBanned := fun x y => by
  unfold yakutBanned; infer_instance

/-- Yakut's low vowels are harmonizing blockers ((14g): `ojum-lar`, not
    `*ojum-lor`): rounding spreads from `o` to `u` but not from `u` to `o` —
    the icy-target configuration, and again asymmetric. -/
theorem yakut_asymmetric : yakutBanned .u .o ∧ ¬ yakutBanned .o .u := by decide

/-- Spot-checks against (14): `oɣo-lor` (rounding spreads low→low) and
    `murum-u` (high→high) are well-formed; `*tünnük-lör` ((14h)) is banned. -/
example : ¬ yakutBanned .o .o ∧ ¬ yakutBanned .u .u ∧
    yakutBanned .ue .oe := by decide

end AksenovaEtAl2024
