import Mathlib.Data.List.Chain
import Linglib.Semantics.Plurality.Basic
import Linglib.Semantics.Plurality.Cumulativity

/-!
# Reciprocal Predicates

Substrate for the reciprocal-meaning typology. The six interpretation
schemes originate in [langendoen-1978] (Strong Reciprocity SR,
Intermediate Reciprocity IR, Weak Reciprocity WR), Kański 1987 (bib
entry pending; Inclusive Alternative Ordering IAO), Fiengo & Lasnik
1973 (bib entry pending; Partitioned Strong Reciprocity PartSR), and
[dalrymple-et-al-1998] (the **Alternative** variants SAR/IAR plus
One-way Weak Reciprocity OWR as a methodological waypoint between WR
and IAO). DKMPK 1998 organises them along two axes — **quantification
strength** (∀∀ / ∃-chain / ∃∃) and **directionality** (one-way vs
alternative `R x y ∨ R y x`) — and proposes the **Strongest Meaning
Hypothesis** (SMH): interpretation selects the strongest scheme
consistent with context. The substrate here exposes the six schemes,
the entailment lattice between the bivalent versions, and a bridge to
`Cumulativity.Cumulative` for WR. SMH itself is left as a Todo.

## Main declarations

* `ReciprocalScheme` — the six-cell typology, named.
* `StrongReciprocity` — every distinct pair satisfies `R`.
* `PartitionedStrongReciprocity` — there is a partition of `X` such
  that SR holds within each cell.
* `IntermediateReciprocity` — every distinct pair is connected by an
  `R`-chain.
* `WeakReciprocity` — every member is `R`-related to a distinct other
  *in both directions*.
* `OneWayWeakReciprocity` — only the first direction of WR.
* `InclusiveAlternativeOrdering` — every member participates in `R`
  either as subject or as object of a distinct other.
* `strong_imp_weak`, `weak_imp_oneWay`, `oneWay_imp_inclusiveAlternative`,
  `strong_imp_inclusiveAlternative` — the entailment lattice
  ([beck-2001] eq 28 right-hand spine).
* `weakReciprocity_iff_cumulative_strict` — WR factors through
  `Cumulative` of the strict-distinct relation (Beck eq 120 /
  [sternefeld-1998] eq 26b, bivalent collapse).

## Implementation notes

The standard DKMPK / Langendoen 1978 form of WR requires both
`∃y ∈ X. y ≠ x ∧ R x y` AND `∃y ∈ X. y ≠ x ∧ R y x` for each
`x ∈ X` — i.e., each member must be both an `R`-subject and an
`R`-object of some distinct other. The single-conjunct version (here:
`OneWayWeakReciprocity`) is empirically too weak; it's named after
Sabato & Winter 2005's terminology.

`IntermediateReciprocity` uses `List.IsChain` on a list of atoms in `X`
to express "connected by an `R`-chain"; `PartitionedStrongReciprocity`
uses `Finset (Finset α)` for the partition witness.

## Todo

* Strong/Weak/Intermediate **Alternative** schemes (`R y x ∨ R x y`
  variants): SAR, IAR.
* Strongest Meaning Hypothesis as an interpretation operator selecting
  among schemes given context.
* Add bib entries: Kański 1987, Fiengo & Lasnik 1973, Sabato & Winter
  2005.
-/

namespace Semantics.Plurality.Reciprocal

open Semantics.Plurality
open Semantics.Plurality.Cumulativity

variable {A : Type*}

/-- The six reciprocal interpretation schemes. SR/IR/WR originate in
    [langendoen-1978]; IAO in Kański 1987 (bib entry pending);
    Partitioned SR in Fiengo & Lasnik 1973 (bib entry pending); the
    **Alternative** variants (SAR, IAR) in [dalrymple-et-al-1998]. -/
inductive ReciprocalScheme where
  | strong                  -- Strong Reciprocity (SR)
  | partitionedStrong       -- Partitioned Strong Reciprocity (PartSR)
  | intermediate            -- Intermediate Reciprocity (IR)
  | weak                    -- Weak Reciprocity (WR)
  | oneWayWeak              -- One-way Weak Reciprocity (OWR)
  | inclusiveAlternative    -- Inclusive Alternative Ordering (IAO)
  deriving DecidableEq, Repr

/-! ### Strong Reciprocity -/

/-- **Strong Reciprocity**: every distinct pair in `X` satisfies `R`.
    "The students all know each other": every student knows every
    other student. -/
def StrongReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, y ≠ x → R x y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (StrongReciprocity R X) := by
  unfold StrongReciprocity; infer_instance

/-! ### Partitioned Strong Reciprocity -/

/-- **Partitioned Strong Reciprocity** (Fiengo & Lasnik 1973, bib entry
    pending): there is a partition of `X` such that SR holds within
    each cell. "The men are hitting each other" can be true if the men
    team up in pairs that stand in the hit-relation. -/
def PartitionedStrongReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ PART : Finset (Finset A),
    (∀ Y ∈ PART, Y ⊆ X) ∧
    (∀ a ∈ X, ∃ Y ∈ PART, a ∈ Y) ∧
    (∀ Y ∈ PART, ∀ x ∈ Y, ∀ y ∈ Y, y ≠ x → R x y)

/-! ### Intermediate Reciprocity -/

/-- **Intermediate Reciprocity** (Langendoen 1978): any two distinct
    members of `X` are connected by an `R`-chain through `X`. "Five
    Boston pitchers sat alongside each other": each pitcher has an
    `R`-chain to every other pitcher.

    Uses `List.Chain'` over a non-empty list of `X`-elements whose head
    is `x` and whose last element is `y`. -/
def IntermediateReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, y ≠ x →
    ∃ chain : List A, chain.head? = some x ∧ chain.getLast? = some y ∧
      (∀ z ∈ chain, z ∈ X) ∧ chain.IsChain R

/-! ### Weak Reciprocity -/

/-- **Weak Reciprocity** (Langendoen 1978; DKMPK 1998): every member of
    `X` is `R`-related to at least one distinct other member **in both
    directions** — as `R`-subject and as `R`-object. "The boys are
    stacked on top of each other": each boy has *some* other boy on
    top of him AND is on top of *some* other boy.

    Definitionally identical to `Cumulative (R ∧ ≠) X X` (see
    `weakReciprocity_iff_cumulative_strict`). -/
def WeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y) ∧ (∀ y ∈ X, ∃ x ∈ X, R x y ∧ x ≠ y)

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (WeakReciprocity R X) := by
  unfold WeakReciprocity; infer_instance

/-! ### One-way Weak Reciprocity -/

/-- **One-way Weak Reciprocity** (Sabato & Winter 2005 terminology):
    only the first direction of WR is required. "The pirates are
    staring at each other" — pirate 6 is not stared at by anybody, but
    everyone stares at someone. -/
def OneWayWeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (OneWayWeakReciprocity R X) := by
  unfold OneWayWeakReciprocity; infer_instance

/-! ### Inclusive Alternative Ordering -/

/-- **Inclusive Alternative Ordering** (Kański 1987, bib entry pending):
    each member of `X` participates in `R` as either first or second
    argument of a distinct other. "The plates are stacked on top of
    each other" — each plate is on top of one or has one on top of
    itself. -/
def InclusiveAlternativeOrdering (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, x ≠ y ∧ (R x y ∨ R y x)

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (InclusiveAlternativeOrdering R X) := by
  unfold InclusiveAlternativeOrdering; infer_instance

/-! ### Entailment lattice (Beck 2001 eq 28, right-hand spine) -/

/-- Strong Reciprocity entails Weak Reciprocity, on pluralities of
    cardinality ≥ 2 (so a distinct witness exists). -/
theorem strong_imp_weak [DecidableEq A]
    (R : A → A → Prop) (X : Finset A)
    (hcard : 2 ≤ X.card) (hSR : StrongReciprocity R X) :
    WeakReciprocity R X := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hSR x hx y hy hyx, hyx.symm⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hSR y hy x hx hyx.symm, hyx⟩

/-- Weak Reciprocity entails One-way Weak Reciprocity (projection on
    the first conjunct). -/
theorem weak_imp_oneWay (R : A → A → Prop) (X : Finset A)
    (hWR : WeakReciprocity R X) : OneWayWeakReciprocity R X :=
  hWR.1

/-- One-way Weak Reciprocity entails Inclusive Alternative Ordering. -/
theorem oneWay_imp_inclusiveAlternative (R : A → A → Prop) (X : Finset A)
    (hOWR : OneWayWeakReciprocity R X) :
    InclusiveAlternativeOrdering R X := by
  intro x hx
  obtain ⟨y, hy, hRxy, hxy⟩ := hOWR x hx
  exact ⟨y, hy, hxy, Or.inl hRxy⟩

/-- Composition: SR entails IAO via the right-hand spine
    `SR → WR → OWR → IAO`. -/
theorem strong_imp_inclusiveAlternative [DecidableEq A]
    (R : A → A → Prop) (X : Finset A) (hcard : 2 ≤ X.card)
    (hSR : StrongReciprocity R X) :
    InclusiveAlternativeOrdering R X :=
  oneWay_imp_inclusiveAlternative R X
    (weak_imp_oneWay R X (strong_imp_weak R X hcard hSR))

/-! ### Cumulativity bridge -/

/-- **Weak Reciprocity factors through `Cumulative`**: Beck-Sauerland's
    `**` applied to the strict-distinct verb relation
    `λ a b. R a b ∧ a ≠ b` on `(X, X)` recovers Weak Reciprocity
    definitionally. This is the substrate-level form of
    [beck-2001] eq 120 / [sternefeld-1998] eq 26b (bivalent
    collapse). The Beck/Sternefeld trivalent disagreement is invisible
    here — both reduce to the same proposition under bivalent
    encoding. -/
theorem weakReciprocity_iff_cumulative_strict
    (R : A → A → Prop) (X : Finset A) :
    WeakReciprocity R X ↔
    Cumulative (fun a b => R a b ∧ a ≠ b) X X := Iff.rfl

/-- Forward weakening: WR truth conditions entail bare
    `Cumulative R X X` (dropping the strict-distinct conjunct). This
    is *strictly weaker* than either Beck eq 120 or Sternefeld eq 26b,
    both of which keep the distinctness clause inside the relation
    argument. -/
theorem weakReciprocity_imp_cumulative
    (R : A → A → Prop) (X : Finset A)
    (hWR : WeakReciprocity R X) :
    Cumulative R X X := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hRxy, _⟩ := hWR.1 x hx
    exact ⟨y, hy, hRxy⟩
  · intro y hy
    obtain ⟨x, hx, hRxy, _⟩ := hWR.2 y hy
    exact ⟨x, hx, hRxy⟩

/-! ### Configurational typology

The event-configuration typology of [evans-et-al-2011b] and
[majid-et-al-2011]: six shapes of mutual relation (strong, pairwise,
chain, radial, melee, ring) used in the video-stimulus elicitation
studies. Each is rendered as an exact-extension condition on `(R, X)` —
the relation coincides with the named configuration — so symmetry and
participant-exhaustiveness are theorems rather than stipulations, and
the shapes plug into the entailment lattice above: pairwise strengthens
to `PartitionedStrongReciprocity`, ring yields `OneWayWeakReciprocity`,
chain and radial yield `InclusiveAlternativeOrdering`, and melee is
definitionally the failure of `InclusiveAlternativeOrdering` (some
activity, but not everyone participates). The strong configuration is
`StrongReciprocity` itself. -/

/-- `y` immediately follows `x` in `l`. -/
def Consecutive (l : List A) (x y : A) : Prop := (x, y) ∈ l.zip l.tail

private lemma consecutive_cons {a : A} {l : List A} {x y : A}
    (h : Consecutive l x y) : Consecutive (a :: l) x y := by
  cases l with
  | nil => simp [Consecutive] at h
  | cons b t => exact List.mem_cons_of_mem _ h

private lemma consecutive_mem {l : List A} {x y : A} (h : Consecutive l x y) :
    x ∈ l ∧ y ∈ l :=
  ⟨(List.of_mem_zip h).1, List.mem_of_mem_tail (List.of_mem_zip h).2⟩

private lemma consecutive_ne {l : List A} (hnd : l.Nodup) {x y : A}
    (h : Consecutive l x y) : x ≠ y := by
  induction l with
  | nil => simp [Consecutive] at h
  | cons a t ih =>
    cases t with
    | nil => simp [Consecutive] at h
    | cons b t' =>
      have h' : (x, y) = (a, b) ∨ Consecutive (b :: t') x y := by
        simpa [Consecutive] using h
      rcases h' with heq | h'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        intro hab
        apply (List.nodup_cons.mp hnd).1
        rw [hab]
        exact List.mem_cons_self ..
      · exact ih (List.nodup_cons.mp hnd).2 h'

private lemma consecutive_asymm {l : List A} (hnd : l.Nodup) {x y : A}
    (hxy : Consecutive l x y) : ¬ Consecutive l y x := by
  induction l with
  | nil => simp [Consecutive] at hxy
  | cons a t ih =>
    cases t with
    | nil => simp [Consecutive] at hxy
    | cons b t' =>
      intro hyx
      have hxy' : (x, y) = (a, b) ∨ Consecutive (b :: t') x y := by
        simpa [Consecutive] using hxy
      have hyx' : (y, x) = (a, b) ∨ Consecutive (b :: t') y x := by
        simpa [Consecutive] using hyx
      rcases hxy' with heq | hxy'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rcases hyx' with heq' | hyx'
        · obtain ⟨h1, -⟩ := Prod.mk.inj heq'
          apply (List.nodup_cons.mp hnd).1
          rw [← h1]
          exact List.mem_cons_self ..
        · exact (List.nodup_cons.mp hnd).1 (consecutive_mem hyx').2
      · rcases hyx' with heq' | hyx'
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq'
          exact (List.nodup_cons.mp hnd).1 (consecutive_mem hxy').2
        · exact ih (List.nodup_cons.mp hnd).2 hxy' hyx'

private lemma getLast?_mem : ∀ {l : List A} {x : A}, l.getLast? = some x → x ∈ l
  | [], _, h => by simp at h
  | [a], x, h => by
    obtain rfl : a = x := by simpa using h
    simp
  | _ :: b :: t, x, h => by
    rw [List.getLast?_cons_cons] at h
    exact List.mem_cons_of_mem _ (getLast?_mem h)

private lemma mem_consecutive_or_getLast {l : List A} {x : A} (hx : x ∈ l) :
    (∃ y, Consecutive l x y) ∨ l.getLast? = some x := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    cases t with
    | nil =>
      right
      obtain rfl := List.mem_singleton.mp hx
      simp
    | cons b t' =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Or.inl ⟨b, by simp [Consecutive]⟩
      · rcases ih hx' with ⟨y, hy⟩ | hlast
        · exact Or.inl ⟨y, consecutive_cons hy⟩
        · right; rw [List.getLast?_cons_cons]; exact hlast

private lemma getLast?_consecutive : ∀ {l : List A}, 2 ≤ l.length →
    ∀ {x : A}, l.getLast? = some x → ∃ y, Consecutive l y x
  | [], hlen, _, _ => by simp at hlen
  | [_], hlen, _, _ => by simp at hlen
  | [a, b], _, x, hx => by
    obtain rfl : b = x := by simpa using hx
    exact ⟨a, by simp [Consecutive]⟩
  | a :: b :: c :: t, _, x, hx => by
    rw [List.getLast?_cons_cons] at hx
    obtain ⟨y, hy⟩ :=
      getLast?_consecutive (by simp only [List.length_cons]; omega) hx
    exact ⟨y, consecutive_cons hy⟩

/-- `R` is symmetric within `X`: every realized pair is mutual. -/
def PairSymmetricOn (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, R x y → R y x

/-- **Pairwise configuration** ([majid-et-al-2011]): the participants
    split into two-member cells, and `R` holds exactly within cells
    ("The people at the dinner party were married to one another"). -/
def PairwiseConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ P : Finset (Finset A),
    (∀ c ∈ P, c.card = 2 ∧ c ⊆ X) ∧
    (∀ a ∈ X, ∃ c ∈ P, a ∈ c) ∧
    (∀ x y, R x y ↔ ∃ c ∈ P, x ∈ c ∧ y ∈ c ∧ x ≠ y)

/-- **Chain configuration** ([majid-et-al-2011]): the participants form
    a line and `R` holds exactly between adjacent members, directed
    ("The graduating students followed one another up onto the stage"). -/
def ChainConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ (∀ z, z ∈ l ↔ z ∈ X) ∧ 2 ≤ l.length ∧
    ∀ x y, R x y ↔ Consecutive l x y

/-- **Ring configuration** ([majid-et-al-2011]): a chain whose last
    member acts on the first ("The children chased each other round in
    a ring"). -/
def RingConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ (∀ z, z ∈ l ↔ z ∈ X) ∧ 3 ≤ l.length ∧
    ∀ x y, R x y ↔
      (Consecutive l x y ∨ (l.getLast? = some x ∧ l.head? = some y))

/-- **Radial configuration** ([majid-et-al-2011]): one central
    participant acts (asymmetrically) on each of the others ("The
    teacher and her pupils intimidated one another"). -/
def RadialConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ c ∈ X, 2 ≤ X.card ∧ ∀ x y, R x y ↔ (x = c ∧ y ∈ X ∧ y ≠ c)

/-- **Melee configuration** ([majid-et-al-2011]): multiple asymmetrical
    interactions without full saturation ("The drunks in the pub were
    punching one another") — some activity, but participation fails to
    be exhaustive, i.e. even `InclusiveAlternativeOrdering` (the weakest
    scheme in the lattice above) fails. -/
def MeleeConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  (∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ R x y) ∧ ¬ InclusiveAlternativeOrdering R X

/-! #### Symmetry theorems -/

/-- Strong reciprocity is symmetric on its plurality. -/
theorem StrongReciprocity.pairSymmetricOn {R : A → A → Prop} {X : Finset A}
    (h : StrongReciprocity R X) : PairSymmetricOn R X := by
  intro x hx y hy hR
  by_cases hxy : x = y
  · exact hxy ▸ hR
  · exact h y hy x hx hxy

/-- The pairwise configuration is symmetric: partners are mutual. -/
theorem PairwiseConfig.pairSymmetricOn {R : A → A → Prop} {X : Finset A}
    (h : PairwiseConfig R X) : PairSymmetricOn R X := by
  obtain ⟨P, -, -, hiff⟩ := h
  intro x _ y _ hR
  obtain ⟨c, hc, hxc, hyc, hne⟩ := (hiff x y).mp hR
  exact (hiff y x).mpr ⟨c, hc, hyc, hxc, hne.symm⟩

/-- The chain configuration is not symmetric: followers are not
    followed back ([majid-et-al-2011]'s directed line). -/
theorem ChainConfig.not_pairSymmetricOn {R : A → A → Prop} {X : Finset A}
    (h : ChainConfig R X) : ¬ PairSymmetricOn R X := by
  obtain ⟨l, hnd, hmem, hlen, hiff⟩ := h
  obtain - | ⟨a, - | ⟨b, t⟩⟩ := l
  · simp at hlen
  · simp at hlen
  · intro hsym
    have hcons : Consecutive (a :: b :: t) a b := by simp [Consecutive]
    have haX : a ∈ X := (hmem a).mp (consecutive_mem hcons).1
    have hbX : b ∈ X := (hmem b).mp (consecutive_mem hcons).2
    exact consecutive_asymm hnd hcons
      ((hiff b a).mp (hsym a haX b hbX ((hiff a b).mpr hcons)))

/-- The ring configuration is not symmetric (for genuine rings of three
    or more): the cycle is directed. -/
theorem RingConfig.not_pairSymmetricOn {R : A → A → Prop} {X : Finset A}
    (h : RingConfig R X) : ¬ PairSymmetricOn R X := by
  obtain ⟨l, hnd, hmem, hlen, hiff⟩ := h
  obtain - | ⟨a, - | ⟨b, - | ⟨c, t⟩⟩⟩ := l
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · intro hsym
    have hcons : Consecutive (a :: b :: c :: t) a b := by simp [Consecutive]
    have haX : a ∈ X := (hmem a).mp (consecutive_mem hcons).1
    have hbX : b ∈ X := (hmem b).mp (consecutive_mem hcons).2
    rcases (hiff b a).mp
        (hsym a haX b hbX ((hiff a b).mpr (Or.inl hcons))) with hba | ⟨hlast, -⟩
    · exact consecutive_asymm hnd hcons hba
    · rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at hlast
      exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
        (getLast?_mem hlast)

/-- The radial configuration is not symmetric: the center acts on the
    periphery, never conversely ([majid-et-al-2011]). -/
theorem RadialConfig.not_pairSymmetricOn [DecidableEq A]
    {R : A → A → Prop} {X : Finset A}
    (h : RadialConfig R X) : ¬ PairSymmetricOn R X := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  obtain ⟨y, hy, hyc⟩ := X.exists_mem_ne hcard c
  intro hsym
  exact hyc ((hiff y c).mp
    (hsym c hc y hy ((hiff c y).mpr ⟨rfl, hy, hyc⟩))).1

/-! #### Exhaustiveness theorems

Participant-exhaustiveness is `InclusiveAlternativeOrdering` — the
weakest scheme in the lattice. Every configuration except melee entails
it (the strong configuration via `strong_imp_inclusiveAlternative`);
melee denies it by definition. -/

/-- Everyone at a pairwise event has a partner. -/
theorem PairwiseConfig.inclusiveAlternativeOrdering [DecidableEq A]
    {R : A → A → Prop} {X : Finset A}
    (h : PairwiseConfig R X) : InclusiveAlternativeOrdering R X := by
  obtain ⟨P, hcells, hcover, hiff⟩ := h
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hcover x hx
  have h2 : c.card = 2 := (hcells c hc).1
  obtain ⟨y, hyc, hyx⟩ := c.exists_mem_ne (by omega) x
  exact ⟨y, (hcells c hc).2 hyc, hyx.symm,
    Or.inl ((hiff x y).mpr ⟨c, hc, hxc, hyc, hyx.symm⟩)⟩

/-- Everyone in a chain follows or is followed. -/
theorem ChainConfig.inclusiveAlternativeOrdering
    {R : A → A → Prop} {X : Finset A}
    (h : ChainConfig R X) : InclusiveAlternativeOrdering R X := by
  obtain ⟨l, hnd, hmem, hlen, hiff⟩ := h
  intro x hx
  rcases mem_consecutive_or_getLast ((hmem x).mpr hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, (hmem y).mp (consecutive_mem hy).2,
      consecutive_ne hnd hy, Or.inl ((hiff x y).mpr hy)⟩
  · obtain ⟨y, hy⟩ := getLast?_consecutive hlen hlast
    exact ⟨y, (hmem y).mp (consecutive_mem hy).1,
      (consecutive_ne hnd hy).symm, Or.inr ((hiff y x).mpr hy)⟩

/-- Everyone in a ring chases someone: the ring configuration yields
    `OneWayWeakReciprocity` (which a chain does not — its last member
    acts on nobody). -/
theorem RingConfig.oneWayWeak {R : A → A → Prop} {X : Finset A}
    (h : RingConfig R X) : OneWayWeakReciprocity R X := by
  obtain ⟨l, hnd, hmem, hlen, hiff⟩ := h
  intro x hx
  rcases mem_consecutive_or_getLast ((hmem x).mpr hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, (hmem y).mp (consecutive_mem hy).2,
      (hiff x y).mpr (Or.inl hy), consecutive_ne hnd hy⟩
  · obtain - | ⟨a, t⟩ := l
    · simp at hlen
    · refine ⟨a, (hmem a).mp (List.mem_cons_self ..),
        (hiff x a).mpr (Or.inr ⟨hlast, rfl⟩), fun hxa => ?_⟩
      obtain - | ⟨b, t'⟩ := t
      · simp at hlen
      · rw [hxa, List.getLast?_cons_cons] at hlast
        exact (List.nodup_cons.mp hnd).1 (getLast?_mem hlast)

/-- The ring configuration participates everyone. -/
theorem RingConfig.inclusiveAlternativeOrdering
    {R : A → A → Prop} {X : Finset A}
    (h : RingConfig R X) : InclusiveAlternativeOrdering R X :=
  oneWay_imp_inclusiveAlternative R X h.oneWayWeak

/-- Radial events participate everyone: the center acts on each
    peripheral member. -/
theorem RadialConfig.inclusiveAlternativeOrdering [DecidableEq A]
    {R : A → A → Prop} {X : Finset A}
    (h : RadialConfig R X) : InclusiveAlternativeOrdering R X := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  intro x hx
  by_cases hxc : x = c
  · subst hxc
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hyx.symm, Or.inl ((hiff x y).mpr ⟨rfl, hy, hyx⟩)⟩
  · exact ⟨c, hc, hxc, Or.inr ((hiff c x).mpr ⟨rfl, hx, hxc⟩)⟩

/-! #### Lattice connections -/

/-- The pairwise configuration realizes Partitioned Strong Reciprocity:
    the pairing is the partition witness. -/
theorem PairwiseConfig.partitionedStrong {R : A → A → Prop} {X : Finset A}
    (h : PairwiseConfig R X) : PartitionedStrongReciprocity R X := by
  obtain ⟨P, hcells, hcover, hiff⟩ := h
  exact ⟨P, fun Y hY => (hcells Y hY).2, hcover,
    fun Y hY x hx y hy hne => (hiff x y).mpr ⟨Y, hY, hx, hy, hne.symm⟩⟩

end Semantics.Plurality.Reciprocal
