/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.Minimal
import Mathlib.Order.Preorder.Chain
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
  `WithAlternatives.alternatives` — Hamblin application with one side held at its
  ordinary value — so the prosodic calculus runs through the same
  applicative as the Roothian engine (`WithAlternatives.alternatives_seq`).

`licensedFocusValue` is the pipeline connector: the composable targets
minus the banned ones. At propositional type its values are
`PropFocusValue`s, the focus values [rooth-1992]'s squiggle consumes —
the metrical structure derives the focus value that F-marking
stipulates (`Antecedent.Admits.of_licensed`).
-/

namespace Focus

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

/-- A usable marking realizes every focus between the focus and the marked constituent: the
foci a marking is syncretic for form a continuous stretch of the tree. -/
theorem Usable.of_le (h : Usable inv m f) {g : C} (hfg : f ≤ g) (hgm : g ≤ m) : Usable inv m g :=
  ⟨h.1, hgm, fun m' hm' hgm' hm'm => h.2.2 m' hm' (hfg.trans hgm') hm'm⟩

/-- When the constituents containing a focus form a chain — in a tree — its usable marking is
unique. -/
theorem Usable.unique {m' : C} (hchain : IsChain (· ≤ ·) (Set.Ici f)) (h : Usable inv m f)
    (h' : Usable inv m' f) : m = m' := by
  rcases eq_or_ne m m' with rfl | hne
  · rfl
  rcases hchain h.2.1 h'.2.1 hne with hmm' | hm'm
  · exact h'.2.2 m h.1 h.2.1 hmm'
  · exact (h.2.2 m' h'.1 h'.2.1 hm'm).symm

end Marking

/-! ### Prosodic focal restrictions -/

section Prosodic


variable {W α β : Type*}

/-- Weak Restriction ([buring-2015] (4)): under the default weak–strong
pattern, the banned focal targets vary the weak (function) daughter
*non-trivially* while the strong daughter stays at its ordinary value.
The weak daughter's own ordinary value is subtracted, so a node never
excludes its literal meaning — the revision [buring-2015] makes to the
preliminary rule (1), which lacked the subtraction. -/
def weakBanned (dw : WithAlternatives (α → β)) (ds : WithAlternatives α) : Set β :=
  (dw.alternatives \ {dw.ordinary}).seq {ds.ordinary}

/-- Strong Restriction ([buring-2015]): under prosodic reversal, the
allowed focal targets vary the accented (function) daughter
non-trivially while the deaccented daughter stays at its ordinary
value. -/
def strongAllowed (dm : WithAlternatives (α → β)) (ds : WithAlternatives α) :
    Set β :=
  (dm.alternatives \ {dm.ordinary}).seq {ds.ordinary}

/-- Reversal allows exactly the targets the default bans: the two metrical patterns of a branching
node divide its focal targets between them. -/
theorem strongAllowed_eq_weakBanned (dm : WithAlternatives (α → β))
    (ds : WithAlternatives α) : strongAllowed dm ds = weakBanned dm ds := rfl

/-- The focal targets a metrical configuration licenses: everything
the daughters compose to, minus the banned targets. At `β := Set W`
this is a `PropFocusValue W` — the focus value the prosody derives. -/
def licensedFocusValue (dw : WithAlternatives (α → β)) (ds : WithAlternatives α) :
    Set β :=
  dw.alternatives.seq ds.alternatives \ weakBanned dw ds

theorem licensedFocusValue_subset_seq (dw : WithAlternatives (α → β))
    (ds : WithAlternatives α) :
    licensedFocusValue dw ds ⊆ dw.alternatives.seq ds.alternatives :=
  Set.sdiff_subset

theorem disjoint_licensedFocusValue_weakBanned
    (dw : WithAlternatives (α → β)) (ds : WithAlternatives α) :
    Disjoint (licensedFocusValue dw ds) (weakBanned dw ds) :=
  Set.disjoint_sdiff_left

/-- Prosodic restriction only strengthens admission: an antecedent the
licensed focus value admits is admitted by the unrestricted Hamblin
composition — [rooth-1992]'s fip against the prosodically derived
focus value. -/
theorem Antecedent.Admits.of_licensed {a : Antecedent W}
    {dw : WithAlternatives (α → Set W)} {ds : WithAlternatives α}
    (h : a.Admits (licensedFocusValue dw ds)) :
    a.Admits (dw.alternatives.seq ds.alternatives) :=
  h.mono Set.sdiff_subset

end Prosodic

end Focus
