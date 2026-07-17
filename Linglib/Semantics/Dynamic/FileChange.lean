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

The assertive update is *consistent merge* (`State.merge`,
[kamp-vangenabith-reyle-2011] Def. 26): [heim-1983]'s revised atomic
rule (18), which filters where the input already defines the atom's
cards (rule (13), `atomVar_eq_of_familiar`) and extends where it does
not (`atomVar_eq_of_novel`) — per point, so atoms are total and
appropriateness ((15)) lives on `indef`/`def_`, as in the paper.
Principle (A) in its general form is ascent in informativeness
(`infoLe_ofState`); set-shrinking eliminativity is its familiar face.

Negation keeps the points of `F` that do not *subsist* (`≺`) in the
scope's update — the no-verifying-extension clause, generalizing
[heim-1983]'s world-only `s \ s[φ]` (`CCP.Partial.neg`): on a uniform
stratum the two coincide (`neg_eq_partial_neg`), so the 1983 clauses are
the referent-free shadow of the 1982 ones.

## Main definitions

- `FCP`: file change potentials —
  `CCP.Partial (Possibility W V (Option M))`.
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
- `infoLe_ofState`: Principle (A) — updates only add information.
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
abbrev FCP (W V M : Type*) := CCP.Partial (Possibility W V (Option M))

namespace FCP

variable {W V M : Type*}

/-- Card `x` in `F` refers to `m`: every point assigns `m` to `x`
(Ch. III §2.3). -/
def refersTo (F : State W V M) (x : V) (m : M) : Prop :=
  ∀ p ∈ F, p.assignment x = some m

/-- Assertive update by a state: consistent merge ([heim-1983]'s revised
atomic rule (18), which is [kamp-vangenabith-reyle-2011] Def. 26's
`State.merge`) — each input point pairs with every compatible point of
`A`, filtering where their domains overlap and extending where `A`
defines more. Total: appropriateness ((15), the Novelty/Familiarity
Condition) lives on `indef`/`def_`, as in the paper. -/
def ofState (A : State W V M) : FCP W V M :=
  fun F => Part.some (State.merge F A)

/-- Principle (A), general form: assertive update ascends in
informativeness — `merge_infoLe`'s left leg. Set-shrinking
eliminativity is its familiar-regime shadow (`atomVar_eq_of_familiar`);
on novel referents the update extends rather than shrinks. -/
theorem infoLe_ofState (A : State W V M) {F F' : State W V M}
    (h : F' ∈ ofState A F) : F ⊑ F' := by
  obtain rfl := Part.mem_some_iff.mp h
  exact infoLe_merge_left F A

/-- Atomic predicate on the world: merge with the empty-domain
proposition state. -/
def atomW (pred : W → Prop) : FCP W V M :=
  ofState {q | q.domain = ∅ ∧ pred q.world}

/-- Atomic predicate at card `x`: merge with the `{x}`-domain
proposition state. Familiar `x` filters (rule (13)); novel `x` extends
(rule (18)) — per point, so partially familiar files update
pointwise. -/
def atomVar (pred : M → Prop) (x : V) : FCP W V M :=
  ofState {q | q.domain = {x} ∧ ∃ m, q.assignment x = some m ∧ pred m}

/-- Binary atomic predicate at `x` and `y`. -/
def atomVar2 (pred : M → M → Prop) (x y : V) : FCP W V M :=
  ofState {q | q.domain = {x, y} ∧ ∃ m m', q.assignment x = some m ∧
    q.assignment y = some m' ∧ pred m m'}

/-- Negation: keep the points of `F` that do not subsist in the scope's
update — the no-verifying-extension clause, as non-subsistence.
Referents introduced inside the scope are trapped. Undefined when the
scope is. -/
def neg (φ : FCP W V M) : FCP W V M :=
  fun F => (φ F).map fun F' => {p ∈ F | ¬ p ≺ F'}

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
  fun F => Part.assert (∀ p ∈ F, p.assignment x = none) fun _ =>
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
  rw [h, Part.bind_some, h]

/-! ### Admittance -/

/-- The Novelty Condition is definedness: an indefinite is defined iff
its card is novel and the body is defined on the extended file. -/
theorem admits_indef [DecidableEq V] (x : V) (body : FCP W V M)
    (F : State W V M) :
    (indef x body).admits F ↔
      ∃ _ : ∀ p ∈ F, p.assignment x = none,
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
`infoLe_ofState`. -/

/-- World atoms filter, unconditionally: merging with an empty-domain
proposition state eliminates the points at incompatible worlds. -/
theorem atomW_eq (pred : W → Prop) (F : State W V M) :
    atomW pred F = Part.some {p ∈ F | pred p.world} := by
  refine congrArg Part.some (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨p, hp, q, ⟨hqdom, hqpred⟩, hpq, rfl⟩
    have hqnone : ∀ v, q.assignment v = none := fun v =>
      Option.not_isSome_iff_eq_none.mp fun hs =>
        Set.eq_empty_iff_forall_notMem.mp hqdom v hs
    have huq : p.union q = p :=
      Possibility.ext rfl (funext fun v => by
        simp [Possibility.union, hqnone v])
    rw [huq]
    exact ⟨hp, hpq.1.symm ▸ hqpred⟩
  · rintro ⟨hr, hpred⟩
    refine ⟨r, hr, ⟨r.world, fun _ => none⟩,
      ⟨Set.ext fun v => by simp [Possibility.domain], hpred⟩,
      ⟨rfl, fun _ _ _ _ h => by simp at h⟩, ?_⟩
    exact Possibility.ext rfl (funext fun v => by simp [Possibility.union])

/-- Rule (13), the familiar regime: at a familiar card the atom
filters — and in particular is eliminative. -/
theorem atomVar_eq_of_familiar [DecidableEq V] (pred : M → Prop) (x : V)
    {F : State W V M} (hfam : Familiar F x) :
    atomVar pred x F =
      Part.some {p ∈ F | ∃ m, p.assignment x = some m ∧ pred m} := by
  refine congrArg Part.some (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨p, hp, q, ⟨hqdom, m, hqx, hpred⟩, hpq, rfl⟩
    have hqnone : ∀ v, v ≠ x → q.assignment v = none := fun v hv =>
      Option.not_isSome_iff_eq_none.mp fun hs => hv (by
        have : v ∈ q.domain := hs
        rwa [hqdom] at this)
    obtain ⟨m₀, hpx⟩ := Option.ne_none_iff_exists'.mp (hfam p hp)
    have huq : p.union q = p :=
      Possibility.ext rfl (funext fun v => by
        by_cases hv : v = x
        · subst hv; simp [Possibility.union, hpx]
        · simp [Possibility.union, hqnone v hv])
    rw [huq]
    exact ⟨hp, m₀, hpx, by rw [hpq.2 x m₀ m hpx hqx]; exact hpred⟩
  · rintro ⟨hr, m, hrx, hpred⟩
    refine ⟨r, hr, ⟨r.world, fun v => if v = x then some m else none⟩,
      ⟨Set.ext fun v => by by_cases hv : v = x <;>
        simp [Possibility.domain, hv], m, by simp, hpred⟩,
      ⟨rfl, fun v e e' he he' => ?_⟩, ?_⟩
    · have he2 : (if v = x then some m else none) = some e' := he'
      by_cases hv : v = x
      · rw [if_pos hv] at he2
        rw [hv, hrx] at he
        exact (Option.some_inj.mp he).symm.trans (Option.some_inj.mp he2)
      · rw [if_neg hv] at he2
        simp at he2
    · refine Possibility.ext rfl (funext fun v => ?_)
      by_cases hv : v = x
      · subst hv; simp [Possibility.union, hrx]
      · simp [Possibility.union, hv]

/-- Rule (18), the novel regime: at a novel card the atom extends each
point with every witness — random assignment then filtering, in one
step. The indefinite needs no extra content clause; `indef` adds only
the Novelty guard. -/
theorem atomVar_eq_of_novel [DecidableEq V] (pred : M → Prop) (x : V)
    {F : State W V M} (hnov : ∀ p ∈ F, p.assignment x = none) :
    atomVar pred x F = Part.some
      {p ∈ State.randomAssign F x |
        ∃ m, p.assignment x = some m ∧ pred m} := by
  refine congrArg Part.some (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨p, hp, q, ⟨hqdom, m, hqx, hpred⟩, hpq, rfl⟩
    have hqnone : ∀ v, v ≠ x → q.assignment v = none := fun v hv =>
      Option.not_isSome_iff_eq_none.mp fun hs => hv (by
        have : v ∈ q.domain := hs
        rwa [hqdom] at this)
    have huq : p.union q = p.update x (some m) :=
      Possibility.ext rfl (funext fun v => by
        by_cases hv : v = x
        · subst hv; simp [Possibility.union, Possibility.update,
            hnov p hp, hqx]
        · simp [Possibility.union, Possibility.update, hqnone v hv, hv])
    rw [huq]
    exact ⟨⟨p, hp, m, rfl⟩, m, by simp, hpred⟩
  · rintro ⟨hmem, m, hrx, hpred⟩
    obtain ⟨p, hp, m', rfl⟩ := hmem
    simp only [Possibility.update_assignment, Function.update_self] at hrx
    obtain rfl := (Option.some_inj.mp hrx).symm
    refine ⟨p, hp, ⟨p.world, fun v => if v = x then some m else none⟩,
      ⟨Set.ext fun v => by by_cases hv : v = x <;>
        simp [Possibility.domain, hv], m, by simp, hpred⟩,
      ⟨rfl, fun v e e' he he' => ?_⟩, ?_⟩
    · have he2 : (if v = x then some m else none) = some e' := he'
      by_cases hv : v = x
      · rw [hv, hnov p hp] at he
        simp at he
      · rw [if_neg hv] at he2
        simp at he2
    · refine Possibility.ext (by simp [Possibility.union]) (funext fun v => ?_)
      by_cases hv : v = x
      · rw [hv]
        simp [Possibility.union, Possibility.update, hnov p hp]
      · simp [Possibility.union, Possibility.update, hv]

/-- World atoms are eliminative (the familiar face of Principle (A)). -/
theorem atomW_eliminative (pred : W → Prop) {F F' : State W V M}
    (h : F' ∈ atomW pred F) : F' ⊆ F := by
  rw [atomW_eq] at h
  obtain rfl := Part.mem_some_iff.mp h
  exact fun p hp => hp.1

/-- Variable atoms are eliminative at familiar cards. -/
theorem atomVar_eliminative [DecidableEq V] (pred : M → Prop) (x : V)
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
  show {p ∈ F | ¬ p ≺ (φ F).get h₁} = F \ (φ F).get h₁
  ext p
  simp only [Set.mem_sep_iff, Set.mem_sdiff]
  exact and_congr_right fun hp => not_congr
    (State.subsists_iff_mem (hφ _ (Part.get_mem _)) (hF p hp))

end FCP

end DynamicSemantics
