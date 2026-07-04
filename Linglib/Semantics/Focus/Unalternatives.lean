/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.Minimal
import Linglib.Semantics.Focus.Control

/-!
# Unalternative Semantics

Focus marking without [F]-features ([buring-2015],
[assmann-etal-2023]): constructions directly constrain the focal
targets they can realize.

* **Morphosyntactic** ([assmann-etal-2023] §2): a construction focally
  marks exactly one constituent; No Projection lets it realize any
  focus within that constituent, and Blocking preempts it wherever a
  strictly more specific marking would do. `Usable` packages both;
  `usable_iff_minimal` identifies it with minimality among inventory
  covers.
* **Prosodic** ([buring-2015]): a branching node's metrical pattern
  restricts targets pointwise. `weakBanned` (his Weak Restriction)
  bans targets that vary the weak daughter over its alternative domain
  while the strong daughter stays at its ordinary value;
  `strongAllowed` (his Strong Restriction) allows only targets varying
  the accented daughter non-trivially. Both are `Set.seq` images of
  `AltMeaning.aSet` — Hamblin application with one side held at its
  ordinary value — so the prosodic calculus runs through the same
  applicative as the Roothian engine (`AltMeaning.aSet_seq`).

`licensedFocusValue` is the pipeline connector: the composable targets
minus the banned ones. At propositional type its values are
`PropFocusValue`s, the focus values [rooth-1992]'s squiggle consumes —
the metrical structure derives the focus value that F-marking
stipulates (`Antecedent.Admits.of_licensed`).
-/

namespace Semantics.Focus

/-! ### Morphosyntactic focal marking -/

section Marking

variable {C : Type*} [PartialOrder C] {inv : List C} {m f : C}

/-- A focally marked constituent is usable for focus `f`
([assmann-etal-2023] §2.2–2.3): it is in the language's inventory,
`f` lies within it (No Projection), and no strictly more specific
inventory constituent also covers `f` (Blocking). -/
def Usable (inv : List C) (m f : C) : Prop :=
  m ∈ inv ∧ f ≤ m ∧ ∀ m' ∈ inv, f ≤ m' → m' ≤ m → m' = m

instance [DecidableEq C] [DecidableLE C] : Decidable (Usable inv m f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Usability is minimality among inventory covers of the focus. -/
theorem usable_iff_minimal :
    Usable inv m f ↔ Minimal (fun c => c ∈ inv ∧ f ≤ c) m := by
  constructor
  · rintro ⟨hm, hf, hmin⟩
    exact ⟨⟨hm, hf⟩, fun b ⟨hb, hfb⟩ hbm => (hmin b hb hfb hbm) ▸ le_rfl⟩
  · rintro ⟨⟨hm, hf⟩, hmin⟩
    exact ⟨hm, hf, fun m' hm' hfm' hm'm =>
      le_antisymm hm'm (hmin ⟨hm', hfm'⟩ hm'm)⟩

end Marking

/-! ### Prosodic focal restrictions -/

section Prosodic

open Alternatives

variable {W α β : Type*}

/-- Weak Restriction ([buring-2015]): under the default weak–strong
pattern, the banned focal targets vary the weak (function) daughter
over its alternative domain while the strong daughter stays at its
ordinary value. -/
def weakBanned (dw : AltMeaning (α → β)) (ds : AltMeaning α) : Set β :=
  dw.aSet.seq {ds.oValue}

/-- Strong Restriction ([buring-2015]): under prosodic reversal, the
allowed focal targets vary the accented (function) daughter
non-trivially while the deaccented daughter stays at its ordinary
value. -/
def strongAllowed (dm : AltMeaning (α → β)) (ds : AltMeaning α) :
    Set β :=
  (dm.aSet \ {dm.oValue}).seq {ds.oValue}

/-- Reversal allows only targets that the default bans. -/
theorem strongAllowed_subset_weakBanned (dm : AltMeaning (α → β))
    (ds : AltMeaning α) : strongAllowed dm ds ⊆ weakBanned dm ds :=
  Set.seq_mono Set.sdiff_subset subset_rfl

/-- The focal targets a metrical configuration licenses: everything
the daughters compose to, minus the banned targets. At `β := Set W`
this is a `PropFocusValue W` — the focus value the prosody derives. -/
def licensedFocusValue (dw : AltMeaning (α → β)) (ds : AltMeaning α) :
    Set β :=
  dw.aSet.seq ds.aSet \ weakBanned dw ds

theorem licensedFocusValue_subset_seq (dw : AltMeaning (α → β))
    (ds : AltMeaning α) :
    licensedFocusValue dw ds ⊆ dw.aSet.seq ds.aSet :=
  Set.sdiff_subset

theorem disjoint_licensedFocusValue_weakBanned
    (dw : AltMeaning (α → β)) (ds : AltMeaning α) :
    Disjoint (licensedFocusValue dw ds) (weakBanned dw ds) :=
  Set.disjoint_sdiff_left

/-- With a Given strong daughter the default pattern licenses
nothing: the ban swallows the whole composition. The deaccenting
imperative — prominence must shift off given material
([schwarzschild-1999], [buring-2016]) — derived from the Weak
Restriction plus [kratzer-selkirk-2020]'s (46) Givenness. -/
theorem licensedFocusValue_eq_empty_of_given
    {dw : AltMeaning (α → β)} {ds : AltMeaning α}
    (h : ds.Given ds.oValue) :
    licensedFocusValue dw ds = ∅ := by
  unfold licensedFocusValue weakBanned
  rw [show ds.aSet = {ds.oValue} from h]
  exact sdiff_self

/-- Prosodic restriction only strengthens admission: an antecedent the
licensed focus value admits is admitted by the unrestricted Hamblin
composition — [rooth-1992]'s fip against the prosodically derived
focus value. -/
theorem Antecedent.Admits.of_licensed {a : Antecedent W}
    {dw : AltMeaning (α → Set W)} {ds : AltMeaning α}
    (h : a.Admits (licensedFocusValue dw ds)) :
    a.Admits (dw.aSet.seq ds.aSet) :=
  h.mono Set.sdiff_subset

end Prosodic

end Semantics.Focus
