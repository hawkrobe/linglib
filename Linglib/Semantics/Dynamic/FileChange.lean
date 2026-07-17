import Linglib.Semantics.Dynamic.Partial
import Linglib.Semantics.Dynamic.State

/-!
# File Change Semantics
[heim-1982] [heim-1983]

[heim-1982]'s file change potentials over referential information
states: `FCP W V M` is `CCP.Partial` at the possibility type — the
partiality effect of `Dynamic/Partial.lean` over the root states of
`Dynamic/State.lean`. A file *is* an information state: its cards are
the familiar referents, `Dom(F)` the shared domain of a uniform file.
Presupposition is `Part`-definedness (`CCP.Partial.admits`, Heim's
"F admits φ"), so the Novelty and Familiarity Conditions are genuine
definedness conditions; sequencing and its monoid laws are `PFun.comp`'s
(`PFun.comp_assoc`, `PFun.id_comp`, `PFun.comp_id`).

The assertive update is *consistent merge* (the `State` monoid's `*`,
[kamp-vangenabith-reyle-2011] Def. 26): [heim-1983]'s revised atomic
rule (18), which filters where the input already defines the atom's
cards (rule (13), `atomVar_eq_of_familiar`) and extends where it does
not (`atomVar_eq_of_novel`) — per point, so atoms are total and
appropriateness ((15)) lives on `indef`/`def_`, as in the paper.
Principle (A) in its general form is ascent in informativeness
(`le_ofState`); set-shrinking eliminativity is its familiar face.

Negation keeps the points of `F` that do not *subsist* in the
scope's update — the no-verifying-extension clause, generalizing
[heim-1983]'s world-only `s \ s[φ]` (`CCP.Partial.neg`): on a uniform
stratum the two coincide (`neg_eq_partial_neg`), so the 1983 clauses are
the referent-free shadow of the 1982 ones.

## Main definitions

- `FCP`: file change potentials —
  `CCP.Partial (Possibility W V (Part M))`.
- `FCP.ofState`: assertive update as consistent merge; `FCP.atomW`,
  `FCP.atomVar`, `FCP.atomVar2` are its instances at proposition
  states.
- `FCP.neg`, `FCP.cond`: negation as non-subsistence; *if* as `¬(φ ∧ ¬ψ)`.
- `FCP.indef`, `FCP.def_`: the Novelty and Familiarity Conditions as
  `Part.assert` guards on `State.randomAssign` and identity.
- `FCP.trueIn`, `FCP.falseIn`, `FCP.supports`, `FCP.fcpEntails`: truth
  criterion (C) (Ch. III §3.2) and dynamic entailment.

## Main results

- `admits_def_`, `admits_indef`: the Familiarity and Novelty Conditions
  are exactly definedness.
- `le_ofState`: Principle (A) — updates only add information.
- `atomW_eq`, `atomVar_eq_of_familiar`, `atomVar_eq_of_novel`: the
  filtering and extending regimes of the merge-based atom (rules (13)
  and (18)).
- `neg_eq_partial_neg`: on a uniform stratum, non-subsistence negation
  is [heim-1983]'s set-difference negation.
-/

namespace DynamicSemantics

/-- A file change potential ([heim-1982], Ch. III): a partial update of
referential information states — `CCP.Partial` at the possibility type.
Partiality is presupposition (`CCP.Partial.admits`); Heim's files number
their cards, `V := ℕ`. -/
abbrev FCP (W V M : Type*) := CCP.Partial (Possibility W V (Part M))

namespace FCP

variable {W V M : Type*}

/-- Card `x` in `F` refers to `m`: every point assigns `m` to `x`
(Ch. III §2.3). -/
def refersTo (F : State W V M) (x : V) (m : M) : Prop :=
  ∀ p ∈ F, m ∈ p.assignment x

/-- Assertive update by a state: consistent merge ([heim-1983]'s revised
atomic rule (18), which is [kamp-vangenabith-reyle-2011] Def. 26's
consistent merge, the `State` monoid's `*`) — each input point pairs
with every compatible point of
`A`, filtering where their domains overlap and extending where `A`
defines more. Total: appropriateness ((15), the Novelty/Familiarity
Condition) lives on `indef`/`def_`, as in the paper. -/
def ofState (A : State W V M) : FCP W V M :=
  fun F => Part.some (Set.lubs F A)

/-- Principle (A), general form: assertive update ascends in
informativeness — `State.left_le_mul`. Set-shrinking eliminativity is
its familiar-regime shadow (`atomVar_eq_of_familiar`); on novel
referents the update extends rather than shrinks. -/
theorem le_ofState (A : State W V M) {F F' : State W V M}
    (h : F' ∈ ofState A F) : F ≤ F' := by
  obtain rfl := Part.mem_some_iff.mp h
  exact State.left_le_mul

/-- Atomic predicate on the world: merge with the empty-domain
proposition state. -/
def atomW (pred : W → Prop) : FCP W V M :=
  ofState {q | q.domain = ∅ ∧ pred q.world}

/-- Atomic predicate at card `x`: merge with the `{x}`-domain
proposition state. Familiar `x` filters (rule (13)); novel `x` extends
(rule (18)) — per point, so partially familiar files update
pointwise. -/
def atomVar (pred : M → Prop) (x : V) : FCP W V M :=
  ofState {q | q.domain = {x} ∧ ∃ m ∈ q.assignment x, pred m}

/-- Binary atomic predicate at `x` and `y`. -/
def atomVar2 (pred : M → M → Prop) (x y : V) : FCP W V M :=
  ofState {q | q.domain = {x, y} ∧ ∃ m ∈ q.assignment x,
    ∃ m' ∈ q.assignment y, pred m m'}

/-- Negation: keep the points of `F` that do not subsist in the scope's
update — the no-verifying-extension clause, as non-subsistence.
Referents introduced inside the scope are trapped. Undefined when the
scope is. -/
def neg (φ : FCP W V M) : FCP W V M :=
  fun F => (φ F).map fun F' => {p ∈ F | p ∉ lowerClosure F'}

/-- Conditional: `F + [if φ then ψ] = F + [¬(φ ∧ ¬ψ)]` — Heim's analysis
of conditionals as negated conjunctions. -/
def cond (φ ψ : FCP W V M) : FCP W V M :=
  neg (φ.seq (neg ψ))

/-- Indefinite introduction: defined only if `x` is novel (the Novelty
Condition — no point defines it); then introduce `x` by random
assignment and update with the body. Indefinites don't quantify — they
open a new file card. [heim-1991] later derives novelty from Maximize
Presupposition rather than stipulating it; the guard here is the
original (15). -/
def indef [DecidableEq V] (x : V) (body : FCP W V M) : FCP W V M :=
  fun F => Part.assert (∀ p ∈ F, ¬(p.assignment x).Dom) fun _ =>
    body (State.randomAssign F x)

/-- Definite reference: defined only if `x` is familiar (the Familiarity
Condition); the card is already established, so the file passes through
to the body. -/
def def_ (x : V) (body : FCP W V M) : FCP W V M :=
  fun F => Part.assert (Familiar F x) fun _ => body F

/-! ### Truth and entailment (Ch. III §3) -/

/-- Truth criterion (C) (Ch. III §3.2): `φ` is true w.r.t. `F` iff
`F + φ` is defined and consistent. Existential quantification is built
into truth itself — indefinites need no existential closure. -/
def trueIn (F : State W V M) (φ : FCP W V M) : Prop :=
  ∃ F' ∈ φ F, F'.Nonempty

/-- `φ` is false w.r.t. `F` iff `F + φ` is defined but absurd. -/
def falseIn (F : State W V M) (φ : FCP W V M) : Prop :=
  ∃ F' ∈ φ F, ¬F'.Nonempty

/-- `F` supports `φ` iff updating changes nothing — the dynamic notion
of entailment, stronger than `trueIn`. -/
def supports (F : State W V M) (φ : FCP W V M) : Prop :=
  φ F = Part.some F

/-- `φ` semantically entails `ψ` iff every defined update with `φ`
supports `ψ`. -/
def fcpEntails (φ ψ : FCP W V M) : Prop :=
  ∀ F : State W V M, ∀ F' ∈ φ F, supports F' ψ

/-- Truth implies definedness. -/
theorem trueIn_admits {F : State W V M} {φ : FCP W V M}
    (h : trueIn F φ) : φ.admits F :=
  let ⟨F', hF', _⟩ := h
  Part.dom_iff_mem.mpr ⟨F', hF'⟩

/-- Support implies truth for consistent files. -/
theorem supports_trueIn {F : State W V M} {φ : FCP W V M}
    (hsup : supports F φ) (hcons : F.Nonempty) : trueIn F φ :=
  ⟨F, by rw [hsup]; exact Part.mem_some F, hcons⟩

/-- Support is idempotent: if `F` supports `φ`, updating twice is the
same as once. -/
theorem supports_idempotent {F : State W V M} {φ : FCP W V M}
    (h : supports F φ) : φ.seq φ F = φ F := by
  show (φ F).bind φ = φ F
  rw [h]
  exact (Part.bind_some _ _).trans h

/-! ### Admittance -/

/-- The Novelty Condition is definedness: an indefinite is defined iff
its card is novel and the body is defined on the extended file. -/
theorem admits_indef [DecidableEq V] (x : V) (body : FCP W V M)
    (F : State W V M) :
    (indef x body).admits F ↔
      ∃ _ : ∀ p ∈ F, ¬(p.assignment x).Dom,
        (body (F.randomAssign x)).Dom := by
  exact Iff.rfl

/-- **The Familiarity Condition is definedness** ((15)): a definite is
defined iff its card is familiar (and the body is defined). -/
theorem admits_def_ (x : V) (body : FCP W V M) (F : State W V M) :
    (def_ x body).admits F ↔ ∃ _ : Familiar F x, (body F).Dom := by
  exact Iff.rfl

/-! ### The two regimes: filtering and extension

The merge-based atom has rule (13) as its familiar face and rule (18)'s
domain extension as its novel face, per point; `⊆`-eliminativity holds
exactly on the familiar face, while Principle (A) in general is
`le_ofState`. -/

/-- World atoms filter, unconditionally: merging with an empty-domain
proposition state eliminates the points at incompatible worlds. -/
theorem atomW_eq (pred : W → Prop) (F : State W V M) :
    atomW pred F = Part.some {p ∈ F | pred p.world} := by
  refine congrArg Part.some (Set.ext fun r => ⟨?_, ?_⟩)
  · intro hr
    obtain ⟨p, hp, q, ⟨hqdom, hqpred⟩, hpq, rfl⟩ := State.mem_mul.mp hr
    have hqle : q ≤ p := ⟨(Possibility.compat_iff.mp hpq).1.symm, fun v e he =>
      absurd (Part.dom_iff_mem.mpr ⟨e, he⟩)
        (Set.eq_empty_iff_forall_notMem.mp hqdom v)⟩
    rw [le_antisymm (Possibility.union_le le_rfl hqle) Possibility.le_union_left]
    exact ⟨hp, (Possibility.compat_iff.mp hpq).1.symm ▸ hqpred⟩
  · rintro ⟨hr, hpred⟩
    exact State.mem_mul.mpr ⟨r, hr, Possibility.bot r.world,
      ⟨Possibility.domain_bot, hpred⟩, .of_le le_rfl Possibility.bot_le,
      Possibility.union_bot.symm⟩

/-- Rule (13), the familiar regime: at a familiar card the atom
filters — and in particular is eliminative. -/
theorem atomVar_eq_of_familiar (pred : M → Prop) (x : V)
    {F : State W V M} (hfam : Familiar F x) :
    atomVar pred x F =
      Part.some {p ∈ F | ∃ m ∈ p.assignment x, pred m} := by
  refine congrArg Part.some (Set.ext fun r => ⟨?_, ?_⟩)
  · intro hmem
    obtain ⟨p, hp, q, ⟨hqdom, m, hqx, hpred⟩, hpq, rfl⟩ := State.mem_mul.mp hmem
    obtain ⟨hw, hag⟩ := Possibility.compat_iff.mp hpq
    obtain ⟨m₀, hpx⟩ := Part.dom_iff_mem.mp (hfam p hp)
    have hqle : q ≤ p := ⟨hw.symm, fun v e he => by
      have hveq : v = x := hqdom.subset (Part.dom_iff_mem.mpr ⟨e, he⟩)
      subst hveq
      exact (Part.mem_unique he hqx).trans (hag v m₀ m hpx hqx).symm ▸ hpx⟩
    rw [le_antisymm (Possibility.union_le le_rfl hqle) Possibility.le_union_left]
    exact ⟨hp, m₀, hpx, hag x m₀ m hpx hqx ▸ hpred⟩
  · rintro ⟨hr, m, hrx, hpred⟩
    have hqle : (⟨r.world, fun v => ⟨v = x, fun _ => m⟩⟩ : Possibility W V (Part M)) ≤ r :=
      ⟨rfl, fun v e he => by obtain ⟨rfl, rfl⟩ := he; exact hrx⟩
    refine State.mem_mul.mpr ⟨r, hr, ⟨r.world, fun v => ⟨v = x, fun _ => m⟩⟩,
      ⟨Set.ext fun v => Iff.rfl, m, ⟨rfl, rfl⟩, hpred⟩,
      Possibility.compat_iff.mpr ⟨rfl, fun v e e' he he' => ?_⟩, ?_⟩
    · obtain ⟨rfl, rfl⟩ := he'
      exact Part.mem_unique he hrx
    · exact (le_antisymm (Possibility.union_le le_rfl hqle)
        Possibility.le_union_left).symm

/-- Rule (18), the novel regime: at a novel card the atom extends each
point with every witness — random assignment then filtering, in one
step. The indefinite needs no extra content clause; `indef` adds only
the Novelty guard. -/
theorem atomVar_eq_of_novel [DecidableEq V] (pred : M → Prop) (x : V)
    {F : State W V M} (hnov : ∀ p ∈ F, ¬(p.assignment x).Dom) :
    atomVar pred x F = Part.some
      {p ∈ State.randomAssign F x | ∃ m ∈ p.assignment x, pred m} := by
  refine congrArg Part.some (Set.ext fun r => ⟨?_, ?_⟩)
  · intro hmem
    obtain ⟨p, hp, q, ⟨hqdom, m, hqx, hpred⟩, hpq, rfl⟩ := State.mem_mul.mp hmem
    have huq : p.union q = p.update x (Part.some m) :=
      Possibility.ext rfl (funext fun v => by
        by_cases hv : v = x
        · subst hv
          simp [Part.eq_none_iff'.mpr (hnov p hp), Part.eq_some_iff.mpr hqx]
        · have hqv : q.assignment v = ⊥ :=
            Part.eq_none_iff'.mpr fun hd => hv (hqdom.subset hd)
          simp [hqv, Function.update_of_ne hv])
    rw [huq]
    exact ⟨⟨p, hp, m, rfl⟩, m, by simp [Possibility.update], hpred⟩
  · rintro ⟨hmem, m, hrx, hpred⟩
    obtain ⟨p, hp, m', rfl⟩ := hmem
    obtain rfl : m = m' := by
      simpa [Possibility.update] using hrx
    refine State.mem_mul.mpr ⟨p, hp, ⟨p.world, fun v => ⟨v = x, fun _ => m⟩⟩,
      ⟨Set.ext fun v => Iff.rfl, m, ⟨rfl, rfl⟩, hpred⟩,
      Possibility.compat_iff.mpr ⟨rfl, fun v e e' he he' => ?_⟩, ?_⟩
    · obtain ⟨rfl, rfl⟩ := he'
      exact absurd (Part.dom_iff_mem.mpr ⟨e, he⟩) (hnov p hp)
    · refine Possibility.ext rfl (funext fun v => ?_)
      by_cases hv : v = x
      · subst hv
        have hqx : (⟨v = v, fun _ => m⟩ : Part M) = Part.some m :=
          Part.eq_some_iff.mpr ⟨rfl, rfl⟩
        simp [Part.eq_none_iff'.mpr (hnov p hp), hqx]
      · have hqv : (⟨v = x, fun _ => m⟩ : Part M) = ⊥ :=
          Part.eq_none_iff'.mpr fun hd => hv hd
        simp [hqv, Function.update_of_ne hv]

/-- World atoms are eliminative (the familiar face of Principle (A)). -/
theorem atomW_eliminative (pred : W → Prop) {F F' : State W V M}
    (h : F' ∈ atomW pred F) : F' ⊆ F := by
  rw [atomW_eq] at h
  obtain rfl := Part.mem_some_iff.mp h
  exact fun p hp => hp.1

/-- Variable atoms are eliminative at familiar cards. -/
theorem atomVar_eliminative (pred : M → Prop) (x : V)
    {F F' : State W V M}
    (hfam : Familiar F x) (h : F' ∈ atomVar pred x F) : F' ⊆ F := by
  rw [atomVar_eq_of_familiar pred x hfam] at h
  obtain rfl := Part.mem_some_iff.mp h
  exact fun p hp => hp.1

/-- Negation is eliminative. -/
theorem neg_eliminative (φ : FCP W V M) {F F' : State W V M}
    (h : F' ∈ neg φ F) : F' ⊆ F := by
  obtain ⟨G, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact fun p hp => hp.1

/-! ### The referent-free shadow -/

/-- On a uniform stratum, non-subsistence negation is [heim-1983]'s
set-difference negation (`CCP.Partial.neg`): with every referent shared,
a point subsists in the update exactly when it survives into it. The
1983 clauses are the referent-free shadow of the 1982 ones. -/
theorem neg_eq_partial_neg [DecidableEq V] {X : Finset V}
    {φ : FCP W V M} {F : State W V M} (hF : State.UniformAt X F)
    (hφ : ∀ F' ∈ φ F, State.UniformAt X F') :
    neg φ F = CCP.Partial.neg φ F := by
  refine Part.ext' Iff.rfl fun h₁ h₂ => ?_
  show ({p ∈ (F : Set (Possibility W V (Part M))) | p ∉ lowerClosure ((φ F).get h₁)} : Set _) =
    (F : Set (Possibility W V (Part M))) \ (φ F).get h₁
  ext p
  exact and_congr_right fun hp => not_congr
    (State.mem_lowerClosure_iff (hφ _ (Part.get_mem _)) (hF p hp))

end FCP

end DynamicSemantics
