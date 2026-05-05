import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Lemmas

/-!
# Block-Structured Witnesses for Pumping-Lemma Arguments

A `BlockWitness symbols p` is the string `s₀ᵖ s₁ᵖ ⋯ sₙ₋₁ᵖ` formed by
concatenating one block of length `p` per symbol in `symbols`. Such witnesses
are the standard test strings for non-context-freeness arguments via the
CFL pumping lemma.

Three downstream consumers in `Linglib.Core.Computability.NonContextFree`
share this substrate: `anbncndn`, `anbnc`, and `ambncmdn`.

## API

**Structure and counting:**
* `BlockWitness symbols p` — the witness construction.
* `length_eq`, `length_take` — size arithmetic.
* `split_at` — clean decomposition at any block boundary.
* `filter_count` — counts of in-alphabet symbols (each = `p`, by `Nodup`).
* `mem_iff` — membership characterization.

**Position bridge and adjacency:**
* `getElem?_eq` — the foundational position-to-symbol bridge:
  `(BlockWitness symbols p)[i]? = symbols[i / p]?`.
* `not_both_in_vxy` — the **adjacency lemma**: in any decomposition
  `BlockWitness symbols p = u ++ vxy ++ z` with `|vxy| ≤ p`, two symbols
  at block-index distance `≥ 2` cannot both appear in `vxy`. Used by every
  per-alphabet `not_X_and_Y_in_vxy` consumer in `NonContextFree.lean` as a
  one-line invocation with `(by decide)` discharging the `Nodup` and
  index-distance hypotheses.
-/

universe u

variable {α : Type u}

/-- A block-structured witness: concatenates one block of length `p` per
    symbol in `symbols`. -/
def BlockWitness (symbols : List α) (p : Nat) : List α :=
  symbols.flatMap (fun s => List.replicate p s)

namespace BlockWitness

@[simp] theorem nil (p : Nat) : BlockWitness ([] : List α) p = [] := rfl

@[simp] theorem cons (s : α) (ss : List α) (p : Nat) :
    BlockWitness (s :: ss) p = List.replicate p s ++ BlockWitness ss p := by
  simp [BlockWitness, List.flatMap_cons]

@[simp] theorem zero (symbols : List α) :
    BlockWitness symbols 0 = [] := by
  induction symbols with
  | nil => rfl
  | cons _ _ ih => simp [cons, ih]

theorem length_eq (symbols : List α) (p : Nat) :
    (BlockWitness symbols p).length = symbols.length * p := by
  induction symbols with
  | nil => simp
  | cons s ss ih =>
    rw [cons, List.length_append, List.length_replicate, ih, List.length_cons,
        Nat.succ_mul, Nat.add_comm]

/-- The witness splits cleanly at any block boundary. -/
theorem split_at (symbols : List α) (p i : Nat) :
    BlockWitness symbols p =
      BlockWitness (symbols.take i) p ++ BlockWitness (symbols.drop i) p := by
  induction symbols generalizing i with
  | nil => simp
  | cons s ss ih =>
    cases i with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, List.drop_succ_cons, cons, cons, ih, List.append_assoc]

theorem length_take (symbols : List α) (p : Nat) {i : Nat}
    (hi : i ≤ symbols.length) :
    (BlockWitness (symbols.take i) p).length = i * p := by
  rw [length_eq, List.length_take, min_eq_left hi]

/-- Filter count: each in-alphabet symbol contributes exactly `p`; absent
    symbols contribute 0. Requires `symbols.Nodup` so blocks don't merge. -/
theorem filter_count [DecidableEq α]
    {symbols : List α} (hnd : symbols.Nodup) (p : Nat) (s : α) :
    ((BlockWitness symbols p).filter (· == s)).length =
      if s ∈ symbols then p else 0 := by
  induction symbols with
  | nil => simp
  | cons t ts ih =>
    rw [cons, List.filter_append, List.length_append,
        List.filter_replicate]
    have hnd' : ts.Nodup := hnd.of_cons
    have ht_notin : t ∉ ts := List.Nodup.notMem hnd
    rw [ih hnd']
    by_cases hst : s = t
    · subst hst
      simp [ht_notin]
    · have hbeq : (t == s) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => hst h.symm
      simp only [hbeq, List.length_nil, List.mem_cons]
      have : ¬ (s = t) := hst
      simp [this]

/-- A symbol appears in `BlockWitness symbols p` iff it's in `symbols`
    (and `p ≥ 1`). -/
theorem mem_iff [DecidableEq α] {symbols : List α} {p : Nat}
    (hp : p ≥ 1) (s : α) :
    s ∈ BlockWitness symbols p ↔ s ∈ symbols := by
  induction symbols with
  | nil => simp
  | cons t ts ih =>
    rw [cons, List.mem_append, List.mem_cons, ih]
    constructor
    · rintro (h | h)
      · left; exact List.eq_of_mem_replicate h
      · right; exact h
    · rintro (rfl | h)
      · left; exact List.mem_replicate.mpr ⟨Nat.one_le_iff_ne_zero.mp hp, rfl⟩
      · right; exact h

/-- **Position bridge.** The character at position `i` in `BlockWitness symbols p`
    is `symbols[i / p]`: the symbol whose block contains position `i`. Stated
    with `[?]` (optional indexing) so the equation holds for all `i` —
    out-of-range positions yield `none` on both sides.

    This is the foundational position-vs-symbol bridge that makes
    locality arguments trivial: any structural fact about which symbols
    can appear at which positions reduces to integer division on the
    block-length `p`. -/
theorem getElem?_eq {symbols : List α} {p : Nat} (hp : 0 < p) (i : Nat) :
    (BlockWitness symbols p)[i]? = symbols[i / p]? := by
  induction symbols generalizing i with
  | nil => simp [BlockWitness]
  | cons s rest ih =>
    rw [cons]
    by_cases hi : i < p
    · -- i is in the first block
      have hi_len : i < (List.replicate p s).length := by
        rw [List.length_replicate]; exact hi
      rw [List.getElem?_append_left hi_len, List.getElem?_replicate]
      have hp_ne : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp
      simp [hp_ne, hi]
      have hdiv : i / p = 0 := Nat.div_eq_of_lt hi
      rw [hdiv]; rfl
    · -- i ≥ p; look up in the rest
      push Not at hi
      have hi_len : (List.replicate p s).length ≤ i := by
        rw [List.length_replicate]; exact hi
      rw [List.getElem?_append_right hi_len, List.length_replicate, ih]
      -- Goal: rest[(i - p) / p]? = (s :: rest)[i / p]?
      -- (i - p) / p = i / p - 1, and (s :: rest)[i / p]? = rest[i / p - 1]? for i / p ≥ 1
      have hdiv_ge : i / p ≥ 1 := Nat.one_le_div_iff hp |>.mpr hi
      have hsub : (i - p) / p = i / p - 1 := by
        rw [Nat.div_eq_sub_div hp hi, Nat.add_sub_cancel]
      rw [hsub]
      -- (s :: rest)[i / p]? for i / p = k+1 = rest[k]?
      have hdiv_eq : i / p = (i / p - 1) + 1 := by omega
      conv_rhs => rw [hdiv_eq]
      rfl

/-- Substring access: in `u ++ vxy ++ z`, position `|u| + k` (for `k < |vxy|`)
    accesses `vxy[k]`. Used to lift in-substring positions to in-witness
    positions. -/
private theorem getElem?_substring {β : Type*}
    {u vxy z : List β} {k : Nat} (hk : k < vxy.length) :
    (u ++ vxy ++ z)[u.length + k]? = vxy[k]? := by
  rw [List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hk]

/-- Helper: in a `Nodup` list, the optional getter is injective on `some` values. -/
private theorem Nodup.getElem?_inj {l : List α} (h : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi_lt, hi_eq⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj_lt, hj_eq⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff h).mp (hi_eq.trans hj_eq.symm)

/-- **Adjacency lemma.** Two symbols at block-index distance `≥ 2` cannot
    both appear in any `vxy` of length `≤ p` arising from a decomposition
    `BlockWitness symbols p = u ++ vxy ++ z`.

    Proof: each occurrence of `s` (resp. `t`) in `vxy` corresponds to a
    position in `[|u|, |u| + |vxy|)` whose block index (`pos / p`) equals
    `i` (resp. `j`) by `Nodup`. The two positions differ by less than
    `|vxy| ≤ p`, so their block indices differ by at most 1 — contradicting
    `j ≥ i + 2`. -/
theorem not_both_in_vxy [DecidableEq α]
    {symbols : List α} (hnd : symbols.Nodup) {p : Nat}
    {s t : α} {i j : Nat}
    (hi : symbols[i]? = some s)
    (hj : symbols[j]? = some t)
    (hij : j ≥ i + 2)
    {u vxy z : List α}
    (hw : BlockWitness symbols p = u ++ vxy ++ z)
    (hvxy : vxy.length ≤ p) :
    ¬ (s ∈ vxy ∧ t ∈ vxy) := by
  intro ⟨hs, ht⟩
  -- p = 0 case: witness is empty, so vxy = [], hence vacuously no s ∈ vxy
  by_cases hp : p = 0
  · subst hp
    rw [zero] at hw
    have : vxy = [] := by
      have hlen := congr_arg List.length hw.symm
      simp only [List.length_nil, List.length_append] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [this] at hs; exact List.not_mem_nil hs
  have hp : 0 < p := Nat.pos_of_ne_zero hp
  -- Positions of s and t within vxy
  have hks : vxy.idxOf s < vxy.length := List.idxOf_lt_length_iff.mpr hs
  have hkt : vxy.idxOf t < vxy.length := List.idxOf_lt_length_iff.mpr ht
  set ks := vxy.idxOf s
  set kt := vxy.idxOf t
  have hvxy_s : vxy[ks]? = some s := List.getElem?_idxOf hs
  have hvxy_t : vxy[kt]? = some t := List.getElem?_idxOf ht
  -- Lift to witness positions
  have hbw_s : (BlockWitness symbols p)[u.length + ks]? = some s := by
    rw [hw, getElem?_substring hks]; exact hvxy_s
  have hbw_t : (BlockWitness symbols p)[u.length + kt]? = some t := by
    rw [hw, getElem?_substring hkt]; exact hvxy_t
  -- Apply position bridge
  have hsym_s : symbols[(u.length + ks) / p]? = some s := by
    rw [← getElem?_eq hp]; exact hbw_s
  have hsym_t : symbols[(u.length + kt) / p]? = some t := by
    rw [← getElem?_eq hp]; exact hbw_t
  -- By Nodup, the position must equal the canonical index
  have hi_eq : (u.length + ks) / p = i := Nodup.getElem?_inj hnd hsym_s hi
  have hj_eq : (u.length + kt) / p = j := Nodup.getElem?_inj hnd hsym_t hj
  -- Position arithmetic: |ks - kt| < p, so |i - j| ≤ 1, contradicting hij
  -- Without loss of generality, ks ≤ kt (the symmetric case is identical)
  -- Position arithmetic: |kt - ks| < p ⇒ block indices differ by ≤ 1, contra hij
  rcases Nat.lt_or_ge kt ks with h | h
  · -- kt < ks ⇒ (u.length + kt) / p ≤ (u.length + ks) / p ⇒ j ≤ i, contra j ≥ i + 2
    have : (u.length + kt) / p ≤ (u.length + ks) / p := Nat.div_le_div_right (by omega)
    omega
  · -- ks ≤ kt ⇒ kt - ks < p ⇒ (u.length+kt) ≤ (u.length+ks) + p ⇒ /p ≤ +1
    have h_le : u.length + kt ≤ u.length + ks + p := by omega
    have h_div : (u.length + kt) / p ≤ (u.length + ks + p) / p := Nat.div_le_div_right h_le
    rw [Nat.add_div_right _ hp] at h_div
    omega

end BlockWitness
