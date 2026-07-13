/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.OCP
import Linglib.Phonology.Autosegmental.NormalForm
import Linglib.Fragments.Laal.Prosody

/-!
# Lionnet (2022): The features and geometry of tone in Laal

[lionnet-2022]

Laal (isolate, southern Chad) has three contrastive tone heights H/M/L. Lionnet
argues for a subtonal analysis à la [yip-1980]/[pulleyblank-1986] (two register
features `[±upper]`, `[±raised]`) linked to a Tonal Root Node ([snider-2020]):
H = `[+upper, −raised]`, M = `[−upper, +raised]`, L = `[−upper, −raised]`, with
the fourth combination `[+upper, +raised]` the systematic gap. This featural
specification gives a unified account of the otherwise-puzzling Mid tone — its
exclusivity (`*MX/XM`) and its instability (M-lowering).

## What this formalizes

* §5.1 the featural analysis — the substrate `TRN.H/M/L` encode Lionnet's (51).
* §3 M-exclusivity (`*MX/XM`) over the attested stem melodies.
* §5.2 M-lowering as `[−raised]` assimilation (`subtonalAssimilate`): a `[−raised]`
  trigger (H or L) turns the only `[+raised]` tone, M, into L.
* §5.5 the ventive suffix as a floating `[−raised]` with `[upper]` from the root
  (`dockFloating`).
* §5.6 the `[+upper, +raised]` gap (Table-4 type-A system).
* §5.2 (ex. 53–55, 58) the **optional** OCP-`[raised]` merger — consuming the
  `OCP` fusion repair.

## What this does NOT formalize

* §6.1–6.3 base-pattern reduction, replacive full-tone spread, and high-tone
  spread (the full-TRN spreading/deletion processes), and the vowel-harmony
  patterns of §2 — these need the broader autosegmental spreading machinery.
* §7 the alternatives (tone-as-unit, M-as-zero).

## Honest scope notes

M-lowering proper is `[−raised]` *assimilation*, not OCP-merger; and `*MX/XM` is an
*agreement* constraint (`*[α raised][β raised]`), the opposite of the identity-OCP.
The `OCP` API is consumed only for the merger of (53–55)/(58), which
Lionnet presents explicitly as optional ("not necessary in the present analysis" /
"or fusion"). It is included because it is the merger face of the same OCP
principle whose prohibition face lives in `OCP`.
-/

namespace Lionnet2022Laal

open Tone
open Laal.Prosody

/-! ### The subtonal featural analysis (§5.1) -/

/-- Lionnet's featural analysis (ex. 51) as a map into the register-tier `TRN`
encoding: H = `[+upper, −raised]`, M = `[−upper, +raised]`, L = `[−upper, −raised]`. -/
def toneToTRN : Tone → TRN
  | .H => TRN.H
  | .M => TRN.M
  | .L => TRN.L

/-- The substrate `TRN.H/M/L` encode exactly Lionnet's (51) feature matrix. -/
theorem featural_analysis :
    TRN.H = ⟨some true, some false⟩ ∧
    TRN.M = ⟨some false, some true⟩ ∧
    TRN.L = ⟨some false, some false⟩ := ⟨rfl, rfl, rfl⟩

/-- The three tones are featurally distinct — the analysis distinguishes them. -/
theorem tones_distinct_as_TRN :
    (([Tone.H, Tone.M, Tone.L]).map toneToTRN).Nodup := by decide

/-- The minimal triplet (ex. 8) contrasts in tone alone: pairwise-distinct
melodies on one segmental frame. -/
theorem minimalTriplet_distinct_tones :
    (minimalTriplet.map (·.melody)).Nodup := by decide

/-! ### M-exclusivity: `*MX/XM` (§3) -/

/-- **M-exclusivity** (`*MX/XM`): in every attested stem melody, if M occurs then
the melody is *all* M — M never co-occurs with a different tone at stem level. -/
theorem M_exclusive :
    ∀ m ∈ attestedMelodies, Tone.M ∈ m → ∀ t ∈ m, t = Tone.M := by decide

/-! ### M-lowering as `[−raised]` assimilation (§5.2) -/

/-- M-lowering is `[−raised]` assimilation: an L trigger (`[−raised]`) spreads its
`[raised]` value onto M (the only `[+raised]` tone), turning it into L. -/
theorem mLowering_from_L : subtonalAssimilate .raised TRN.L TRN.M = TRN.L := by decide

/-- M-lowering from a `[−raised]` H trigger likewise turns M into L. -/
theorem mLowering_from_H : subtonalAssimilate .raised TRN.H TRN.M = TRN.L := by decide

/-- Only M is targeted: H is inert under `[−raised]` assimilation (already
`[−raised]`), explaining why H- and L-toned roots never lower. -/
theorem H_stable : subtonalAssimilate .raised TRN.L TRN.H = TRN.H := by decide

/-- L is likewise inert under `[−raised]` assimilation. -/
theorem L_stable : subtonalAssimilate .raised TRN.H TRN.L = TRN.L := by decide

/-! ### The ventive suffix (§5.5) -/

/-- The ventive suffix (ex. 60) is a floating `[−raised]` feature with `[upper]`
inherited from the root: `dockFloating .raised false`. It surfaces as H after a
`[+upper]` (H) root and as L after `[−upper]` (M or L) roots — the M-lowering
realisation `kárá`/`dàgà`/`jàrà`. -/
theorem ventive_after_H : dockFloating .raised false TRN.H = TRN.H := by decide
theorem ventive_after_M : dockFloating .raised false TRN.M = TRN.L := by decide
theorem ventive_after_L : dockFloating .raised false TRN.L = TRN.L := by decide

/-! ### The `[+upper, +raised]` gap (§5.6) -/

/-- The Laal tone inventory, as TRNs. -/
def laalToneInventory : List TRN := ([Tone.H, Tone.M, Tone.L]).map toneToTRN

/-- The fourth feature combination `[+upper, +raised]` (`TRN.superHigh`) is absent:
it is the systematic gap that makes Laal a Table-4 type-A system (§5.6). -/
theorem superHigh_is_the_gap : TRN.superHigh ∉ laalToneInventory := by decide

/-! ### The optional OCP-`[raised]` merger (§5.2, ex. 53–55, 58) -/

/-- Lionnet (ex. 54–55, 58) notes — but explicitly does *not* adopt — an optional
OCP-`[raised]` economy under which two adjacent identical `[−raised]` autosegments
fuse into one multiply-linked autosegment. When two adjacent tones are *fully*
identical, that fusion is `OCP.collapse`: two adjacent L tones collapse to
one. -/
theorem ocp_raised_merge_LL :
    OCP.collapse [TRN.L, TRN.L] = [TRN.L] := by decide

/-- OCP-`[raised]` is **tier-relative** ([chandlee-jardine-2019]): it constrains the
`[raised]`-projected tier (`IsCleanOn` reading `.raised`), not whole TRNs. H and L
are distinct *tones* but both `[−raised]`, so adjacent they violate OCP-`[raised]`
even though `[TRN.H, TRN.L]` is clean as a whole-TRN tier. -/
theorem ocp_raised_is_tier_relative :
    ¬ OCP.IsCleanOn (fun _ : TRN => True) (·.raised) [TRN.H, TRN.L] ∧
      OCP.IsClean [TRN.H, TRN.L] := by decide

/-- Under the optional economy, fusing adjacent identical `[raised]` autosegments
leaves the `[raised]`-projected tier OCP-clean — the faithful tier-relative reading
of Lionnet (ex. 54–55, 58), via the substrate retraction `collapse_clean`. The
merger face of the same OCP principle whose prohibition (TSL₂) face lives in
`OCP`. -/
theorem ocp_raised_merge_clean (tier : List TRN) :
    OCP.IsClean (OCP.collapse (tier.map (·.raised))) :=
  OCP.collapse_clean _

/-! ### The register-tier geometry on the multi-tier substrate (§5–§6)

[lionnet-2022]'s geometry (ex. 52) is a hub-and-spoke around the **Tonal Root Node**:
the `[±upper]` register tier, the `[±raised]` tier, and the mora (TBU) tier each
associate to the TRN. On the general substrate `Autosegmental.MultiAR` this is a
four-tier graph. Its point over the `TRN` *bundle* used above: each subtonal feature
is a tier of its own, so it can be manipulated **independently of the whole TRN** —
[lionnet-2022]'s *partial activity* (§5, e.g. `[−raised]` assimilation) — which a
bundled `TRN` record cannot structurally express. Whole-TRN operations (§6) act on
the TRN↔mora layer; both live on one object. -/

open Autosegmental

/-- The four Laal tone tiers: `[±upper]` register, `[±raised]`, the TRN, the mora. -/
abbrev laalTier : Fin 4 → Type := ![Option Bool, Option Bool, Unit, Unit]

/-- The tier words of a one-TRN M-toned form (`M = [−upper, +raised]`,
    [lionnet-2022] ex. 51). -/
def laalWords : ∀ i : Fin 4, List (laalTier i) :=
  Fin.cons [some false] (Fin.cons [some true] (Fin.cons [()] (Fin.cons [()] finZeroElim)))

/-- The hub-and-spoke links (ex. 52): register, `[raised]`, and mora each
    associate to the TRN. -/
def laalSpokes (i j : Fin 4) (p q : ℕ) : Prop :=
  ((i, j) = (0, 2) ∨ (i, j) = (1, 2) ∨ (i, j) = (2, 3)) ∧ p = 0 ∧ q = 0

instance (i j : Fin 4) (p q : ℕ) : Decidable (laalSpokes i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The M-toned form on the graph foundation. -/
def mForm : Representation (Sigma.fst : ((i : Fin 4) × laalTier i) → Fin 4) :=
  Representation.ofData laalWords laalSpokes

instance : Fintype mForm.obj.V :=
  inferInstanceAs (Fintype ((_ : Fin 4) × Fin _))

instance (v w : mForm.obj.V) : Decidable (mForm.obj.graph.edges.Adj v w) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (v w : mForm.obj.V) : Decidable (mForm.obj.graph.arcs.Adj v w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The form is planar — each spoke's single association is non-crossing, in
    the foundational path form of the NCC. -/
theorem mForm_planar : IsPlanar mForm.obj.graph := by
  unfold IsPlanar
  decide

/-- **Partial activity** (§5): delinking a feature acts on one tier-pair layer
    alone — here `[raised]`↔TRN, the pair `(1, 2)`. -/
def delink (L : Fin 4 → Fin 4 → ℕ → ℕ → Prop) (i₀ j₀ : Fin 4)
    (i j : Fin 4) (p q : ℕ) : Prop :=
  ¬ (i = i₀ ∧ j = j₀) ∧ L i j p q

/-- The M form with the subtonal `[−raised]` feature delinked. -/
def delinkRaised : Representation (Sigma.fst : ((i : Fin 4) × laalTier i) → Fin 4) :=
  Representation.ofData laalWords (delink laalSpokes 1 2)

/-- Delinking the subtonal `[−raised]` feature leaves the **whole-TRN** layer
    (TRN↔mora, tier-pair `(2, 3)`) untouched: partial activity is independent
    of full activity — the structural content of [lionnet-2022]'s
    subtonal-feature autonomy, impossible to state on a bundled `TRN`. -/
instance : Finite mForm.obj.V := inferInstanceAs (Finite ((_ : Fin 4) × Fin _))

instance : Finite delinkRaised.obj.V := inferInstanceAs (Finite ((_ : Fin 4) × Fin _))

theorem partial_indep_of_full (p q : ℕ) :
    delinkRaised.link 2 3 p q ↔ mForm.link 2 3 p q := by
  unfold delinkRaised mForm
  rw [Representation.link_ofData, Representation.link_ofData]
  simp [delink, laalSpokes]

/-- And it does remove the `[raised]`↔TRN association. -/
theorem delinkRaised_erases (p q : ℕ) : ¬ delinkRaised.link 1 2 p q := by
  unfold delinkRaised
  rw [Representation.link_ofData]
  rintro ⟨-, -, -, ⟨hne, -⟩ | ⟨-, h2, -⟩⟩
  · exact hne ⟨rfl, rfl⟩
  · rcases h2 with h2 | h2 | h2 <;> simp_all

end Lionnet2022Laal
