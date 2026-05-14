import Mathlib.Order.Basic
import Linglib.Core.Case.Basic
/-!
# Caha Containment Order on Case
@cite{caha-2009} @cite{mcfadden-2018}

The canonical order on `Core.Case`: state-of-the-art syntax
(configurational case + nanosyntactic spellout) assumes Caha's
containment as the default. Each case on the hierarchy literally
*contains* the representations of all cases below it:

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

Cases without a `containmentRank` (ERG, ABS, INST, COM, …) are silent —
incomparable with on-hierarchy cases under `≤`, except for reflexivity.
That silence is the theoretical content: Caha's hierarchy is silent on
those cases, and the `PartialOrder` structure preserves the silence.

Other orders (Blake's typological frequency in `Core/Case/Hierarchy.lean`,
per-language syncretism graphs) live as named `def`s used locally via
`letI` rather than as competing instances on `Case`.
-/

namespace Core
namespace Case

/-- Caha's containment rank (@cite{caha-2009}). Cases higher on the
    containment hierarchy have representations that include all lower cases.

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

    Returns `none` for cases not on the containment hierarchy
    (e.g., ERG/ABS in ergative systems, or minor cases whose containment
    structure is less well established).

    **Encoding caveat.** @cite{caha-2009} (10b), p. 10 gives the Universal
    Case sequence NOM-ACC-GEN-DAT-INST-COM (no LOC); the Russian-specific
    sequence (16) p. 12 inserts PREP between GEN and DAT. The encoding
    below — NOM=0, ACC=1, GEN=2, DAT=3, LOC=4, INST=none — matches
    neither verbatim; it is closer to Blake's typological hierarchy
    (@cite{blake-1994} §5.8, which Caha himself argues on p. 31 should
    coincide with his sequence). For Slavic 6-case inventories the
    encoding choice is verdict-equivalent; inventories with INST or COM
    *without* LOC may diverge. For paradigm-shape work that needs Caha's
    actual Slavic ordering, see `cahaSlavicRank` below. -/
def containmentRank : Case → Option Nat
  | .nom => some 0
  | .acc => some 1
  | .gen => some 2
  | .dat => some 3
  | .loc => some 4
  | _ => none

/-- Caha's Slavic-specific Case sequence (@cite{caha-2009} (16) p. 12 for
    Russian; (7) p. 238 confirms the same for Serbian): NOM – ACC – GEN –
    PREP/LOC – DAT – INS. Differs from `containmentRank` in placing LOC
    between GEN and DAT (not at top) and INST at the top (not
    off-hierarchy). Use this rank for paradigm-shape contiguity claims
    referencing Caha's Slavic data; use `containmentRank` for inventory
    downward-closure verdicts (where the choice is Slavic-equivalent).

    Returns `Fin 6` rather than `Option Nat`: all six cases are
    on-hierarchy in Caha's Slavic encoding; there are no off-hierarchy
    cases for the Slavic noun system. The `Option` is preserved for
    consistency with `containmentRank`'s API and to flag non-Slavic
    cases as not-in-the-Slavic-sequence. -/
def cahaSlavicRank : Case → Option (Fin 6)
  | .nom  => some 0
  | .acc  => some 1
  | .gen  => some 2
  | .loc  => some 3
  | .dat  => some 4
  | .inst => some 5
  | _     => none

/-- `cahaSlavicRank` and `containmentRank` agree on the four core cases
    (NOM=0, ACC=1, GEN=2 in both) and disagree on LOC/DAT/INST. The
    disagreement is deliberate: `containmentRank` is verdict-equivalent
    on Slavic inventories for downward-closure (`RespectsCahaContainment`),
    while `cahaSlavicRank` is needed for paradigm-shape contiguity claims
    that respect Caha's actual Slavic sequence. -/
theorem cahaSlavicRank_vs_containmentRank :
    cahaSlavicRank .nom = some 0 ∧ containmentRank .nom = some 0 ∧
    cahaSlavicRank .acc = some 1 ∧ containmentRank .acc = some 1 ∧
    cahaSlavicRank .gen = some 2 ∧ containmentRank .gen = some 2 ∧
    cahaSlavicRank .loc = some 3 ∧ containmentRank .loc = some 4 ∧
    cahaSlavicRank .dat = some 4 ∧ containmentRank .dat = some 3 ∧
    cahaSlavicRank .inst = some 5 ∧ containmentRank .inst = none := by
  decide

/-- Strict containment on Caha-rank Cases: both must have a rank, and the
    first's must be strictly smaller. False whenever either side is
    off-hierarchy. -/
def cahaLT (c₁ c₂ : Case) : Prop :=
  match containmentRank c₁, containmentRank c₂ with
  | some n, some m => n < m
  | _, _ => False

instance instDecidableCahaLT : DecidableRel cahaLT := fun c₁ c₂ => by
  unfold cahaLT; split <;> infer_instance

/-- The Caha containment order. `c₁ ≤ c₂` iff either they are equal, or
    `cahaLT c₁ c₂`. Off-hierarchy cases are reflexively `≤` themselves and
    incomparable with everything else. -/
def cahaLE (c₁ c₂ : Case) : Prop := c₁ = c₂ ∨ cahaLT c₁ c₂

instance : DecidableRel cahaLE := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

instance : LE Case := ⟨cahaLE⟩

instance (c₁ c₂ : Case) : Decidable (c₁ ≤ c₂) :=
  inferInstanceAs (Decidable (cahaLE c₁ c₂))

theorem cahaLE_refl (c : Case) : c ≤ c := Or.inl rfl

theorem cahaLT_trans {a b c : Case} : cahaLT a b → cahaLT b c → cahaLT a c := by
  unfold cahaLT
  cases ha : containmentRank a <;> cases hb : containmentRank b <;>
    cases hc : containmentRank c <;> simp_all
  exact lt_trans

theorem cahaLE_trans (a b c : Case) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  exact Or.inr (cahaLT_trans hab hbc)

theorem cahaLE_antisymm (a b : Case) : a ≤ b → b ≤ a → a = b := by
  intro hab hba
  rcases hab with rfl | hab
  · rfl
  rcases hba with rfl | hba
  · rfl
  exfalso
  exact absurd (cahaLT_trans hab hba) (by
    unfold cahaLT
    cases ha : containmentRank a <;> simp_all)

instance : Preorder Case where
  le_refl := cahaLE_refl
  le_trans _ _ _ := cahaLE_trans _ _ _

instance : PartialOrder Case where
  le_antisymm _ _ := cahaLE_antisymm _ _

/-- A case is **nonnominative** iff its representation contains ACC's, i.e.
    `(.acc : Case) ≤ c` in the Caha order. @cite{mcfadden-2018} argues this is
    the key natural class for stem allomorphy: a VI rule conditioned on
    `[ACC]` captures the NOM-vs-oblique split found cross-linguistically. -/
def IsNonnominative (c : Case) : Prop := (.acc : Case) ≤ c

instance (c : Case) : Decidable (IsNonnominative c) :=
  inferInstanceAs (Decidable ((.acc : Case) ≤ c))

/-- A case is **oblique** iff its representation contains GEN's, i.e.
    `(.gen : Case) ≤ c` in the Caha order. Per @cite{caha-2009}'s
    Unmarked-Dependent vs Oblique split, NOM/ACC are unmarked-dependent
    and GEN/DAT/LOC/INS/COM/etc. are oblique. Ergative-aligned ABS/ERG
    are off-hierarchy in `containmentRank` and so satisfy `¬ IsOblique`
    (consistent with their parallel-to-NOM/ACC structural status). -/
def IsOblique (c : Case) : Prop := (.gen : Case) ≤ c

instance (c : Case) : Decidable (IsOblique c) :=
  inferInstanceAs (Decidable ((.gen : Case) ≤ c))

/-- The four core McFadden-hierarchy cases stratify cleanly between
    non-oblique (NOM, ACC) and oblique (GEN, DAT). -/
theorem isOblique_split_core :
    ¬ IsOblique .nom ∧ ¬ IsOblique .acc ∧ IsOblique .gen ∧ IsOblique .dat := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Ergative-aligned ABS/ERG are not oblique under the Caha hierarchy
    (off-hierarchy → incomparable with GEN). This makes the predicate
    usable for SMSE 2019-style ergative paradigms (Wardaman, Khinalugh). -/
theorem isOblique_erg_abs_false :
    ¬ IsOblique .erg ∧ ¬ IsOblique .abs := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- § Sanity Chain: NOM < ACC < GEN < DAT < LOC
-- ============================================================================

theorem nom_le_acc : (.nom : Case) ≤ .acc :=
  Or.inr (show (0 : Nat) < 1 from Nat.lt_succ_self 0)
theorem acc_le_gen : (.acc : Case) ≤ .gen :=
  Or.inr (show (1 : Nat) < 2 from Nat.lt_succ_self 1)
theorem gen_le_dat : (.gen : Case) ≤ .dat :=
  Or.inr (show (2 : Nat) < 3 from Nat.lt_succ_self 2)
theorem dat_le_loc : (.dat : Case) ≤ .loc :=
  Or.inr (show (3 : Nat) < 4 from Nat.lt_succ_self 3)

/-- Off-hierarchy cases (ERG) are incomparable with on-hierarchy cases. -/
theorem erg_incomparable_nom : ¬ ((.erg : Case) ≤ .nom) := by
  rintro (h | h)
  · exact UD.Case.noConfusion h
  · exact (show False from h)

theorem nom_incomparable_erg : ¬ ((.nom : Case) ≤ .erg) := by
  rintro (h | h)
  · exact UD.Case.noConfusion h
  · exact (show False from h)

end Case
end Core
