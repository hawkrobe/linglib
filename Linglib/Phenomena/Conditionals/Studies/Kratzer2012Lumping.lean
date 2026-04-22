import Linglib.Theories.Semantics.Conditionals.PremiseSemantic

/-!
# @cite{kratzer-2012} §5.4.3 — Lumping blocks spurious counterfactuals

Minimal formalization of @cite{kratzer-2012}'s apple-buying
counterfactual example (Ch. 5, §5.4.1–§5.4.3, pp. 127–129)
demonstrating that the Crucial Set's lumping-closure clause prevents
the spurious counterfactual prediction that the naive
maximal-consistent-extension semantics gives.

## What Kratzer's text actually argues

Kratzer's examples (10a)/(10b) on p. 128 are **MIGHT-counterfactuals**:
"If Paula weren't buying a pound of apples, the Atlantic Ocean *might*
be drying up." The §5.4.2 maximal-consistent-extension semantics
predicts these true (since `pa ∨ ad` plus `¬pa` consistently forces
`ad`); §5.4.3 introduces lumping to block this prediction.

**This file formalizes the would-CF analog** (the same structural
argument applied to `wouldCF` rather than `mightCF`), which is also
blocked by the same lumping mechanism. The would-CF analog is what
falls out cleanly from the present operator API; a parallel mightCF
formalization is left for future work (the `mightCF`/`wouldCF` duality
is not yet proven — see `PremiseSemantic.mightCF_iff_not_wouldCF_compl`,
currently a `sorry`-marked TODO).

## Scenario

Three worlds (and one partial situation):

- `actual` — Paula is buying apples; Atlantic is fine; moon is fine.
  This is `w₀` in @cite{kratzer-2012} §5.4.1.
- `noApplesQuiet` — Paula is not buying apples; Atlantic is fine;
  moon is fine. (A "boring counterfactual" world; the witness that
  forces `wouldCF` to come out false.)
- `atlantic` — Paula is not buying apples; Atlantic is drying.
  (A counterfactual world where the spurious prediction would land.)
- `sA` — a partial situation supporting just "Paula buys apples"
  (`sA ≤ actual`).

## Propositions

- `pa` (= @cite{kratzer-2012} (9a)): "Paula is buying apples"
- `ad` ("Atlantic is drying", contradicting (9b))
- `paOrAd` (= @cite{kratzer-2012} (9d)): `pa ∨ ad` (the disjunction)

## The lumping fact (§5.4.3, p. 129, verbatim claim)

> "every situation where Paula is buying a pound of apples or the
> Atlantic Ocean is drying up is a situation where Paula is buying a
> pound of apples. Hence (9a) is lumped by (9d) in our world."

We prove `Lumps paOrAd pa actual`: at the actual world, every part
where `paOrAd` holds also has `pa` hold (since the `ad` disjunct has
no truth-makers in any part of `actual`).

## The argument

**Without lumping**, a maximal consistent extension of `{¬pa} ∪ Fw₀`
can include `paOrAd` while excluding `pa`. Combined with `¬pa` this
forces `ad` (since `paOrAd ∧ ¬pa → ad` classically).

**With lumping**, the Crucial Set's closure clause requires that if
`paOrAd ∈ A` then `pa ∈ A` (since `Lumps paOrAd pa w₀`). But `pa`
contradicts `¬pa`. So `paOrAd` is excluded from any consistent
lumping-closed subset containing `¬pa`.

The headline theorem `not_wouldCF_notPa_ad` is then derived from the
exact equality `crucialSet_notPa_eq_singleton`
(`CrucialSet Fw₀ actual notPa = {{notPa}}`) plus
`follows_notPa_ad_fails` (which `noApplesQuiet` witnesses).

## Caveat: the Base Set is technically inadmissible

`Fw₀ = {pa, paOrAd}` violates @cite{kratzer-2012}'s **Non-Redundancy**
admissibility clause (p. 132): "A set of propositions is redundant if
it contains propositions p and q such that p ≠ q and `p ∩ W ⊆ q ∩ W`."
Here `pa ⊆ paOrAd` everywhere, so `Fw₀` is redundant. A more careful
formalization would replace `paOrAd` with a non-accidental
generalization (cf. §5.5) whose lumping behavior is the same. The
present minimal demo is enough to exhibit the lumping-closure
mechanism but should not be taken as endorsing a Kratzer-admissible
Base Set.

Other admissibility conditions we do not check:
- (ii) Persistence: holds trivially here (each proposition is
  parthood-upward-closed by construction)
- (iii) Cognitive Viability: per @cite{kratzer-2012} p. 133, "the big
  unknown" — out of scope for formal semantics
- (v) Completeness: `⋂ Fw₀ = pa = {sA, actual}` does not contain
  "all and only worlds indistinguishable from `actual`," so this
  also fails — fixable but orthogonal to the lumping argument

## On the discriminating contrast: Paula vs. switches

The lumping CF is *not the only* operator that gets the right answer
on the Paula scenario. `Theories/Semantics/Conditionals/Counterfactual.universalCounterfactual`
(Lewis/Stalnaker minimal-change) also blocks the spurious prediction
on Paula, because the closest `notPa`-world to `actual` under any
sensible similarity ordering is `noApplesQuiet` (one switch flipped),
not `atlantic` (two switches flipped). So Paula isn't where the
discriminating power of lumping lives.

The actual target of Kratzer's §5.4 complaint is the
**naive maximal-consistent-extension premise semantics** — the
pre-lumping Kratzer 1981 algebra extended with the disjunctive
proposition `paOrAd`. That predecessor allows constructing a maximal
consistent extension of `{notPa} ∪ Fw₀` that includes `paOrAd` while
excluding `pa`, forcing `ad`. Lumping (the Crucial Set's closure
clause) prevents this construction. To formally exhibit the contrast,
linglib would need to formalize the maximal-consistent-extension
operator separately and prove it predicts `ad` on this scenario.
That's out of scope here.

The discriminating power of lumping vs. closest-worlds semantics shows
up not on Paula but on @cite{ciardelli-zhang-champollion-2018}'s
two-switches scenario (where the closest-worlds account is
empirically falsified) — see cross-references below.

## Cross-references

- `Phenomena/Conditionals/Studies/CiardelliZhangChampollion2018.lean`:
  the open question of whether the lumping CF inherits CZC's switches
  falsification. This file is the first concrete `wouldCF`
  instantiation, providing the template for a future situation-semantic
  switches model.

## Scope

This is the minimal demonstration: 4 indices, 2 propositions in the
Base Set, one antecedent, one consequent. A full formalization with
all five propositions (9a–9e), the moon variant (10b), and an
admissibility-respecting Base Set is left as future work, as is the
still-life painting variant from §5.2.
-/

namespace Phenomena.Conditionals.Studies.Kratzer2012Lumping

open Core.IntensionalLogic
open Core.IntensionalLogic.Lumping (Lumps IsConsistent IsCompatible Follows)
open Semantics.Conditionals.PremiseSemantic

/-! ## The minimal Paula scenario -/

/-- The four indices: three worlds and one partial situation. -/
inductive Sit where
  /-- The actual world `w₀`: Paula buys apples; Atlantic fine. -/
  | actual
  /-- A counterfactual world: no Paula apples; Atlantic fine. -/
  | noApplesQuiet
  /-- A counterfactual world: no Paula apples; Atlantic dries. -/
  | atlantic
  /-- Partial situation supporting just "Paula buys apples". -/
  | sA
  deriving Repr, DecidableEq

/-- Parthood: `sA ≤ actual` (sA is a part of the actual world); all
    other indices are only ≤ themselves. Marked `@[reducible]` so that
    `s ≤ t` (via the `PartialOrder` instance below) unfolds eagerly to
    this disjunction in `rcases`-style case analysis. -/
@[reducible]
protected def Sit.le (a b : Sit) : Prop :=
  a = b ∨ (a = .sA ∧ b = .actual)

instance : PartialOrder Sit where
  le := Sit.le
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | ⟨rfl, rfl⟩
    · exact hbc
    · rcases hbc with rfl | ⟨hba, _⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · cases hba
  le_antisymm a b hab hba := by
    rcases hab with rfl | ⟨rfl, rfl⟩
    · rfl
    · rcases hba with hh | ⟨hh, _⟩ <;> cases hh

/-- Helper: `s ≤ t` in `Sit` iff `s = t` or `(s, t) = (sA, actual)`. -/
theorem Sit.le_iff {s t : Sit} :
    s ≤ t ↔ s = t ∨ (s = .sA ∧ t = .actual) := Iff.rfl

/-! ## The frame and propositions -/

/-- The minimal `SituationFrame`: a single dummy entity, the four-index
    `Sit` type with the parthood ordering above. (Kratzer's argument
    doesn't depend on entities; we provide a one-element entity domain
    for the `Frame` interface.) -/
def paulaSituationFrame : SituationFrame where
  Entity := Unit
  Index := Sit
  order := inferInstance

/-! ### Propositions

These are sets of indices in `paulaSituationFrame`. The key claim is
that they are *persistent* (closed upward under parthood) and have
the lumping properties Kratzer's argument requires. -/

/-- "Paula is buying apples" — supported in `actual` and in the
    partial situation `sA` that is its part. -/
def pa : Set paulaSituationFrame.Index := {.sA, .actual}

/-- "The Atlantic is drying" — true only at the `atlantic` world. -/
def ad : Set paulaSituationFrame.Index := {.atlantic}

/-- "Paula is buying apples or the Atlantic is drying" — the
    disjunction (= @cite{kratzer-2012} (9d)). -/
def paOrAd : Set paulaSituationFrame.Index := pa ∪ ad

/-- "Paula is not buying apples" — the antecedent of our
    counterfactual. True at `noApplesQuiet`, `atlantic`, and trivially
    at any other index where `pa` fails (here, none). -/
def notPa : Set paulaSituationFrame.Index := {.noApplesQuiet, .atlantic}

/-! ## The lumping fact -/

/-- **The central lumping claim** (@cite{kratzer-2012}, p. 129):
    `paOrAd` lumps `pa` at the actual world. Every part of `actual`
    where the disjunction holds also has `pa` hold, because the `ad`
    disjunct has no truth-makers in any part of `actual`. -/
theorem lumps_paOrAd_pa_actual : Lumps paOrAd pa Sit.actual := by
  refine ⟨?_, ?_⟩
  · -- (i): paOrAd holds at actual
    show Sit.actual ∈ paOrAd
    left; right; rfl
  · -- (ii): every part of actual where paOrAd holds also has pa hold
    intro s hs _
    rcases hs with rfl | ⟨rfl, _⟩
    · -- s = actual
      show Sit.actual ∈ pa
      right; rfl
    · -- s = sA
      show Sit.sA ∈ pa
      left; rfl

/-- The reverse direction also holds (`pa` is reflexively a sublumper
    of itself, and `paOrAd ⊇ pa` extensionally). -/
theorem lumps_pa_paOrAd_actual : Lumps pa paOrAd Sit.actual := by
  refine ⟨?_, ?_⟩
  · show Sit.actual ∈ pa; right; rfl
  · intro s _ hpa
    -- s ∈ pa → s ∈ paOrAd via Set.subset_union_left
    exact Or.inl hpa

/-! ## Base Set and Crucial Set computation -/

/-- A minimal Base Set for the actual world: just `pa` and `paOrAd`.
    A fuller formalization would also include "Atlantic isn't drying"
    and "moon isn't falling", but the lumping argument turns on `pa`
    and `paOrAd` alone. -/
def Fw₀ : Set (Set paulaSituationFrame.Index) := {pa, paOrAd}

/-- The Crucial Set for antecedent `notPa` at the actual world is
    *just* the singleton `{notPa}`. Any subset that contains `paOrAd`
    is forced by lumping closure to also contain `pa`, which then
    contradicts `notPa` — so neither `paOrAd` nor `pa` can be
    consistently added to a lumping-closed subset of `Fw₀ ∪ {notPa}`
    that contains `notPa`. -/
theorem crucialSet_notPa_singleton :
    {notPa} ∈ CrucialSet (F := paulaSituationFrame) Fw₀ Sit.actual notPa := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- {notPa} ⊆ insert notPa Fw₀
    intro x hx; rcases hx with rfl; exact Set.mem_insert _ _
  · -- notPa ∈ {notPa}
    rfl
  · -- IsConsistent {notPa}: ∃ world where notPa holds
    refine ⟨Sit.noApplesQuiet, ?_, ?_⟩
    · -- noApplesQuiet ∈ Worlds (i.e., is maximal in Sit)
      intro s' hs'
      rcases hs' with rfl | ⟨h, _⟩
      · exact Or.inl rfl
      · cases h
    · -- ∀ p ∈ {notPa}, noApplesQuiet ∈ p
      intro p hp; rcases hp with rfl
      show Sit.noApplesQuiet ∈ notPa
      left; rfl
  · -- Lumping closure: ∀ q ∈ {notPa}, ∀ r ∈ Fw₀, Lumps q r actual → r ∈ {notPa}
    intro q hq r hr hLump
    rcases hq with rfl
    -- hLump : Lumps notPa r actual.
    -- But notPa fails at actual (since pa holds there), so the
    -- "holds at w" condition of Lumps fails — contradiction.
    have h_actual_in_notPa : Sit.actual ∈ notPa := hLump.holds
    -- notPa = {noApplesQuiet, atlantic}; actual is in neither.
    rcases h_actual_in_notPa with hh | hh <;> cases hh

/-! ## The wouldCF prediction

The `wouldCF` truth condition is `∀ A ∈ CrucialSet, ∃ A' ⊇ A in
CrucialSet, Follows A' q`. We prove `CrucialSet Fw₀ actual notPa = {{notPa}}`
exactly (not just `∋ {notPa}`), which collapses the would-CF prediction
to `Follows {notPa} ad` — and that fails at `noApplesQuiet`. -/

/-- Helper: any set containing both `pa` and `notPa` is inconsistent
    (intersects no world in `paulaSituationFrame.Worlds`). -/
private theorem not_isConsistent_of_pa_and_notPa
    {A : Set (Set paulaSituationFrame.Index)}
    (hpa : pa ∈ A) (hnotPa : notPa ∈ A) :
    ¬ IsConsistent (F := paulaSituationFrame) A := by
  rintro ⟨w', _, hwall⟩
  have h_w_pa : w' ∈ pa := hwall pa hpa
  have h_w_notPa : w' ∈ notPa := hwall notPa hnotPa
  -- pa = {sA, actual}; notPa = {noApplesQuiet, atlantic}; intersection empty.
  rcases h_w_pa with rfl | rfl <;>
    rcases h_w_notPa with hh | hh <;> cases hh

/-- **The Crucial Set is exactly `{{notPa}}`.** The lumping-closure
    clause forces any consistent member containing `paOrAd` to also
    contain `pa`, which then contradicts `notPa`. So the only consistent
    lumping-closed subset of `Fw₀ ∪ {notPa}` containing `notPa` is
    `{notPa}` itself. -/
theorem crucialSet_notPa_eq_singleton :
    CrucialSet (F := paulaSituationFrame) Fw₀ Sit.actual notPa
      = { {notPa} } := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨crucialSet_notPa_singleton, ?_⟩
  intro A hA
  apply Set.eq_of_subset_of_subset
  · -- A ⊆ {notPa}: every member of A equals notPa
    intro x hx
    -- x ∈ A ⊆ insert notPa Fw₀ = {notPa, pa, paOrAd}
    rcases hA.subset_insert hx with rfl | hxFw
    · exact Set.mem_singleton _
    · exfalso
      -- Either x = pa directly, or x = paOrAd (then pa ∈ A by lumping closure).
      have hpa_in_A : pa ∈ A := by
        rcases hxFw with rfl | hxPaOrAd
        · exact hx
        · rcases hxPaOrAd with rfl
          exact hA.lumping_closed paOrAd hx pa (Or.inl rfl)
            lumps_paOrAd_pa_actual
      exact not_isConsistent_of_pa_and_notPa hpa_in_A
        hA.antecedent_mem hA.consistent
  · -- {notPa} ⊆ A: notPa ∈ A by the antecedent_mem clause
    intro x hx
    rcases hx with rfl
    exact hA.antecedent_mem

/-- The spurious-prediction-blocking direction: at `noApplesQuiet`,
    the consequent `ad` fails — so the only candidate Crucial Set
    member `{notPa}` does NOT logically imply `ad`. -/
theorem follows_notPa_ad_fails :
    ¬ Follows (F := paulaSituationFrame) {notPa} ad := by
  intro h
  have h_world : Sit.noApplesQuiet ∈ paulaSituationFrame.Worlds := by
    intro s' hs'
    rcases hs' with rfl | ⟨hh, _⟩
    · exact Or.inl rfl
    · cases hh
  have h_notPa : Sit.noApplesQuiet ∈ notPa := Or.inl rfl
  have h_inter : Sit.noApplesQuiet ∈ ⋂₀ ({notPa} : Set (Set Sit)) := by
    intro p hp; rcases hp with rfl; exact h_notPa
  have h_ad : Sit.noApplesQuiet ∈ ad := h ⟨h_world, h_inter⟩
  -- ad = {atlantic}; noApplesQuiet ≠ atlantic.
  cases h_ad

/-- **Headline theorem**: the @cite{kratzer-2012} §5.4.4 lumping CF
    correctly blocks the spurious prediction "if Paula weren't buying
    apples, the Atlantic would be drying" (`wouldCF` returns false).

    Proof: by `crucialSet_notPa_eq_singleton`, the only Crucial Set
    member is `{notPa}`, and the only `{notPa}`-superset in the (now
    singleton) Crucial Set is `{notPa}` itself. The would-CF prediction
    therefore reduces to `Follows {notPa} ad`, which
    `follows_notPa_ad_fails` shows is false. -/
theorem not_wouldCF_notPa_ad :
    ¬ wouldCF (F := paulaSituationFrame) Fw₀ Sit.actual notPa ad := by
  intro hwould
  obtain ⟨A', hA'_in, _, hFollows⟩ :=
    hwould {notPa} crucialSet_notPa_singleton
  rw [crucialSet_notPa_eq_singleton] at hA'_in
  rcases hA'_in with rfl
  exact follows_notPa_ad_fails hFollows

end Phenomena.Conditionals.Studies.Kratzer2012Lumping
