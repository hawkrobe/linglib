import Linglib.Theories.Semantics.BSML.Defs
import Linglib.Theories.Semantics.BSML.Properties
import Linglib.Theories.Semantics.BSML.Bisimulation
import Linglib.Core.Logic.Bilateral.Defs
import Linglib.Core.Logic.Team.Algebra
import Linglib.Core.Logic.Team.Closure

/-!
# State-based Modal Logics for Free Choice — Aloni, Anttila & Yang 2024

@cite{aloni-anttila-yang-2024}

Formalisation of two extensions of BSML introduced in
@cite{aloni-anttila-yang-2024} (Notre Dame J. Formal Logic 65(4), 2024):

* `BSMLOr` — BSML extended with the **global disjunction** `⨼`
  (Definition 2.1; written `∨∨` in some sources).
* `BSMLEmpty` — BSML extended with the **emptiness operator** `⊘`
  (Definition 2.1).

Both extend BSML's `BSMLModel` (worlds + accessibility + valuation) and
inherit the bilateral support/anti-support semantics. The new connectives
are characterised by Fact 2.7 in the paper:

| Logic     | Has `NE` | Has `⨼` | Downward-closed     | Union-closed   |
|-----------|----------|---------|---------------------|----------------|
| BSML      | yes      | no      | when NE-free        | always         |
| BSMLOr    | yes      | yes     | when NE-free        | when ⨼-free    |
| BSMLEmpty | yes      | no      | when NE-free        | always         |

The "when NE-free" / "when ⨼-free" entries express Fact 2.7's universal
statement uniformly across all three logics — NE is the only obstruction
to downward closure; `⨼` is the only obstruction to union closure.

The closure-property classification matches the audit's family-axis
insight: each extension occupies a different cell of the
(`IsLowerSet`, `SupClosed`, `⊥ ∈ ·`) profile lattice.

## Main declarations

* `BSMLOr.Formula` / `BSMLEmpty.Formula` — syntax (Definition 2.1).
* `BSMLOr.eval` / `BSMLEmpty.eval` — bilateral semantics (Definition 2.3),
  parametric in polarity.
* `BSMLOr.support` / `BSMLOr.antiSupport` (and the `BSMLEmpty` analogues)
  — convenience abbreviations.
* `BSMLOr.isBilateral` / `BSMLEmpty.isBilateral` — instances of
  `Core.Logic.Bilateral.IsBilateral`, reusing the BSML substrate.
* `BSMLEmpty.supClosed_support` — union-closure of BSML⊘ formulas
  (Fact 2.7; the second-consumer evidence that BSML's substrate
  generalises).
* `BSMLOr.ofBSML` / `BSMLEmpty.ofBSML` — embedding `BSMLFormula` into each
  extension, preserving semantics (`eval_ofBSML` theorems).

## Implementation notes

The paper's BSML includes `⊥` (weak contradiction) as a primitive, whereas
linglib's `BSMLFormula` (Aloni 2022) does not (the original defines
`⊥ := p ∧ ¬p`). The extension formula types here include `⊥` to match
@cite{aloni-anttila-yang-2024}; the embedding `BSMLFormula → Formula`
therefore has no preimage for `⊥`.

`BSMLOr`'s global disjunction `⨼` is the team-semantic *inquisitive
disjunction* — the support clause is propositional disjunction at the
team level, in contrast to `disj`'s split-existential. Crucially, `⨼` is
the *only* BSML-family connective that breaks union closure (Fact 2.7,
proof in @cite{aloni-anttila-yang-2024}).

`BSMLEmpty`'s emptiness operator `⊘φ` is supported when `s ⊨ φ` *or*
`s = ∅`. It is essentially a restricted `⨼`: `⊘φ ≡ φ ⨼ ⊥`. But since
BSMLEmpty omits `⨼`, union closure is preserved.

## Todo

* §3.2 Expressive-completeness theorems — BSMLOr is expressively complete
  for bisimulation-invariant state properties; BSMLEmpty for the
  union-closed ∩ bisimulation-invariant fragment. The bisim-invariance
  half is done (Theorem 3.8 above for both BSMLOr and BSMLEmpty); the
  converse direction requires Hintikka formulas for states (Definition
  3.10) and finite atom sets. See @cite{anttila-2025} Chapter 3.
* §4 Natural-deduction axiomatisations for each of BSML, BSMLOr,
  BSMLEmpty. Soundness + completeness theorems; @cite{anttila-2025}
  Chapter 4 has the updated proofs.
* Free-choice prediction theorem: state the narrow-scope FC inference
  `[◇(p ∨ q)]⁺ ⊨ ◇p ∧ ◇q` (and the analogous cancellation under
  negation, Example (2) of the paper) over BSMLEmpty. Requires extending
  `BSML/Enrichment.lean`'s `[·]⁺` to target `BSMLEmpty.Formula`.
  Currently the file formalises the vehicle (syntax + semantics) but
  never fires the gun (FC prediction).
* Fact 2.5 (negation normal form) and Fact 2.8 (ML embedding) — provable
  but not load-bearing for the closure-property story.
* `BSMLOr`-specific theorem: `supClosed_support_of_isGDFree` (Fact 2.7
  second part — ⨼-free fragment is union-closed). Requires defining the
  `isGDFree` predicate over `BSMLOr.Formula`.
-/

namespace AloniAnttilaYang2024

variable {W W' : Type*} [DecidableEq W] [Fintype W] [DecidableEq W'] [Fintype W']
variable {Atom : Type*}

open Semantics.BSML (BSMLModel BSMLFormula StateBisim WorldBisim)

/-! ### BSMLOr — BSML with global disjunction `⨼` -/

namespace BSMLOr

/-- BSMLOr syntax (Definition 2.1 of @cite{aloni-anttila-yang-2024}):
    BSML extended with the global disjunction `gdisj` (`⨼`). The `bot`
    constructor is `⊥` (weak contradiction), included as a primitive in
    the AAY-2024 presentation. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Weak contradiction `⊥`: supported only by the empty team. -/
  | bot
  /-- Non-emptiness atom: team is non-empty. -/
  | ne
  /-- Bilateral negation: swap support/anti-support. -/
  | neg (φ : Formula Atom)
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Tensor disjunction (split). -/
  | disj (φ ψ : Formula Atom)
  /-- Global disjunction `⨼`: propositional disjunction at the team level. -/
  | gdisj (φ ψ : Formula Atom)
  /-- Possibility modal `◇`. -/
  | poss (φ : Formula Atom)
  deriving Repr

/-- Bilateral evaluation for BSMLOr (Definition 2.3 of
    @cite{aloni-anttila-yang-2024}). `eval M true φ t` is support;
    `eval M false φ t` is anti-support. Negation flips polarity. -/
def eval (M : BSMLModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,        t => ∀ w ∈ t, M.val p w = true
  | false, .atom p,        t => ∀ w ∈ t, M.val p w = false
  | true,  .bot,           t => t = ∅
  | false, .bot,           _ => True
  | true,  .ne,            t => t.Nonempty
  | false, .ne,            t => t = ∅
  | true,  .neg ψ,         t => eval M false ψ t
  | false, .neg ψ,         t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,    t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                                  Core.Logic.Team.splitsAs t t₁ t₂ ∧
                                  eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂
  | true,  .disj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                                  Core.Logic.Team.splitsAs t t₁ t₂ ∧
                                  eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂,    t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .gdisj ψ₁ ψ₂,   t => eval M true ψ₁ t ∨ eval M true ψ₂ t
  | false, .gdisj ψ₁ ψ₂,   t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,        t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s
  | false, .poss ψ,        t => ∀ w ∈ t, eval M false ψ (M.access w)

/-- Support: positive evaluation. -/
abbrev support (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

@[simp] lemma support_neg (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_bot (M : BSMLModel W Atom) (t : Finset W) :
    support M (.bot : Formula Atom) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_ne (M : BSMLModel W Atom) (t : Finset W) :
    support M (.ne : Formula Atom) t ↔ t.Nonempty := Iff.rfl

@[simp] lemma support_conj (M : BSMLModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_disj (M : BSMLModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

@[simp] lemma support_gdisj (M : BSMLModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.gdisj φ ψ) t ↔ support M φ t ∨ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_gdisj (M : BSMLModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.gdisj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

/-- `BSMLOr`'s `support`/`antiSupport` form a paraconsistent bilateral
    logic under `Formula.neg`. -/
theorem isBilateral (M : BSMLModel W Atom) :
    Core.Logic.Bilateral.IsBilateral
      (support M) (antiSupport M) Formula.neg :=
  Core.Logic.Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

/-! ### Modal depth and bisim invariance for BSMLOr (Theorem 3.8) -/

/-- Modal depth of a `BSMLOr.Formula`: `bot`, atoms, `ne` are 0; `neg`
    preserves depth; `conj`, `disj`, `gdisj` take the max; `poss`
    increments. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .bot => 0
  | .ne => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .gdisj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-- **Theorem 3.8 of @cite{aloni-anttila-yang-2024} for BSMLOr**: if
    `s ⇌_k s'` and `φ : Formula Atom` has modal depth `≤ k`, then
    `eval M b φ s ↔ eval M' b φ s'` for both polarities. -/
theorem bisim_invariant_eval (φ : Formula Atom) :
    ∀ {k : ℕ}, φ.modalDepth ≤ k →
    ∀ {M : BSMLModel W Atom} {M' : BSMLModel W' Atom}
      {s : Finset W} {s' : Finset W'},
    StateBisim k M s M' s' →
    ∀ b : Bool, eval M b φ s ↔ eval M' b φ s' := by
  induction φ with
  | atom p =>
    intro k _ M M' s s' hbisim b
    cases b <;>
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        rw [← hbw.val_eq]; exact h w hw
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        rw [hbw.val_eq]; exact h w' hw'
  | bot =>
    intro k _ M M' s s' hbisim b
    cases b
    · exact ⟨fun _ => trivial, fun _ => trivial⟩
    · exact hbisim.eq_empty_iff
  | ne =>
    intro k _ M M' s s' hbisim b
    cases b
    · exact hbisim.eq_empty_iff
    · exact hbisim.nonempty_iff
  | neg ψ ih =>
    intro k hd M M' s s' hbisim b
    cases b
    · exact ih hd hbisim true
    · exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k := le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k := le_trans (le_max_right _ _) hd
    cases b
    · -- antiSupport (conj): split-existential, use splitPreserve
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt false).mp h₁,
               (ih₂ hd₂ hbu false).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm false).mpr h₁
        · exact (ih₂ hd₂ hbu.symm false).mpr h₂
    · -- support (conj) = support ψ₁ ∧ support ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mp h₁, (ih₂ hd₂ hbisim true).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mpr h₁, (ih₂ hd₂ hbisim true).mpr h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k := le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k := le_trans (le_max_right _ _) hd
    cases b
    · -- antiSupport (disj) = antiSupport ψ₁ ∧ antiSupport ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mp h₁, (ih₂ hd₂ hbisim false).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mpr h₁, (ih₂ hd₂ hbisim false).mpr h₂⟩
    · -- support (disj): split-existential, use splitPreserve
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt true).mp h₁,
               (ih₂ hd₂ hbu true).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm true).mpr h₁
        · exact (ih₂ hd₂ hbu.symm true).mpr h₂
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    -- NEW CASE for BSMLOr: support .gdisj = support ψ₁ ∨ support ψ₂ (team-level),
    -- antiSupport .gdisj = antiSupport ψ₁ ∧ antiSupport ψ₂.
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k := le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k := le_trans (le_max_right _ _) hd
    cases b
    · -- antiSupport: ∧, use IH for both halves
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mp h₁, (ih₂ hd₂ hbisim false).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mpr h₁, (ih₂ hd₂ hbisim false).mpr h₂⟩
    · -- support: ∨, use IH on each disjunct
      constructor
      · rintro (h | h)
        · exact Or.inl ((ih₁ hd₁ hbisim true).mp h)
        · exact Or.inr ((ih₂ hd₂ hbisim true).mp h)
      · rintro (h | h)
        · exact Or.inl ((ih₁ hd₁ hbisim true).mpr h)
        · exact Or.inr ((ih₂ hd₂ hbisim true).mpr h)
  | poss ψ ih =>
    intro k hd M M' s s' hbisim b
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      cases k with
      | zero => exact absurd hd (by simp [Formula.modalDepth])
      | succ k => exact ⟨k, rfl⟩
    have hdψ : ψ.modalDepth ≤ k := by
      have := hd
      simp only [Formula.modalDepth] at this
      omega
    cases b
    · -- antiSupport (poss ψ): ∀ w ∈ s, antiSupport ψ (M.access w)
      constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        exact (ih hdψ hbw.accessStateBisim false).mp (h w hw)
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        exact (ih hdψ hbw.accessStateBisim false).mpr (h w' hw')
    · -- support (poss ψ): existential sub-team transported via image_subset
      constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        obtain ⟨t, htsub, htne, htsupp⟩ := h w hw
        obtain ⟨t', ht'sub, ht'ne, htbisim⟩ :=
          hbw.accessStateBisim.exists_image_subset htsub
        exact ⟨t', ht'sub, ht'ne htne, (ih hdψ htbisim true).mp htsupp⟩
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        obtain ⟨t', ht'sub, ht'ne, ht'supp⟩ := h w' hw'
        obtain ⟨t, htsub, htne, htbisim⟩ :=
          hbw.accessStateBisim.symm.exists_image_subset ht'sub
        exact ⟨t, htsub, htne ht'ne, (ih hdψ htbisim.symm true).mpr ht'supp⟩

end BSMLOr

/-! ### BSMLEmpty — BSML with emptiness operator `⊘` -/

namespace BSMLEmpty

/-- BSMLEmpty syntax (Definition 2.1 of @cite{aloni-anttila-yang-2024}):
    BSML extended with the emptiness operator `empt` (`⊘`). -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  /-- Weak contradiction `⊥`. -/
  | bot
  /-- Non-emptiness atom. -/
  | ne
  | neg (φ : Formula Atom)
  | conj (φ ψ : Formula Atom)
  | disj (φ ψ : Formula Atom)
  /-- Emptiness operator `⊘φ`: supported when `s ⊨ φ` or `s = ∅`. -/
  | empt (φ : Formula Atom)
  | poss (φ : Formula Atom)
  deriving Repr

/-- Bilateral evaluation for BSMLEmpty. The `empt` clause is:
    `support .empt φ s ↔ support φ s ∨ s = ∅` (Definition 2.3). -/
def eval (M : BSMLModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,        t => ∀ w ∈ t, M.val p w = true
  | false, .atom p,        t => ∀ w ∈ t, M.val p w = false
  | true,  .bot,           t => t = ∅
  | false, .bot,           _ => True
  | true,  .ne,            t => t.Nonempty
  | false, .ne,            t => t = ∅
  | true,  .neg ψ,         t => eval M false ψ t
  | false, .neg ψ,         t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,    t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                                  Core.Logic.Team.splitsAs t t₁ t₂ ∧
                                  eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂
  | true,  .disj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                                  Core.Logic.Team.splitsAs t t₁ t₂ ∧
                                  eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂,    t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .empt ψ,        t => eval M true ψ t ∨ t = ∅
  | false, .empt ψ,        t => eval M false ψ t
  | true,  .poss ψ,        t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s
  | false, .poss ψ,        t => ∀ w ∈ t, eval M false ψ (M.access w)

abbrev support (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

abbrev antiSupport (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

@[simp] lemma support_neg (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_bot (M : BSMLModel W Atom) (t : Finset W) :
    support M (.bot : Formula Atom) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_ne (M : BSMLModel W Atom) (t : Finset W) :
    support M (.ne : Formula Atom) t ↔ t.Nonempty := Iff.rfl

@[simp] lemma support_conj (M : BSMLModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_disj (M : BSMLModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

@[simp] lemma support_empt (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.empt φ) t ↔ support M φ t ∨ t = ∅ := Iff.rfl

@[simp] lemma antiSupport_empt (M : BSMLModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.empt φ) t ↔ antiSupport M φ t := Iff.rfl

theorem isBilateral (M : BSMLModel W Atom) :
    Core.Logic.Bilateral.IsBilateral
      (support M) (antiSupport M) Formula.neg :=
  Core.Logic.Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

/-! ### Fact 2.7: BSMLEmpty is union-closed -/

/-- Joint sup-closure for both polarities of BSMLEmpty. The structure
    mirrors `Semantics.BSML.support_and_antiSupport_unionClosed` — every
    clause in BSMLEmpty's `eval` preserves binary union, including the new
    `empt` clause: support of `⊘φ` is `support φ ∨ s = ∅`, which is
    preserved by binary union because the `s = ∅` case forces both
    sub-teams empty, and the `support φ` case uses the IH. -/
private theorem support_and_antiSupport_supClosed
    (φ : Formula Atom) (M : BSMLModel W Atom) :
    (∀ s t : Finset W, support M φ s → support M φ t → support M φ (s ∪ t)) ∧
    (∀ s t : Finset W, antiSupport M φ s → antiSupport M φ t →
                       antiSupport M φ (s ∪ t)) := by
  induction φ with
  | atom p =>
    refine ⟨?_, ?_⟩
    · intro s t hs ht w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hs w h
      · exact ht w h
    · intro s t hs ht w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hs w h
      · exact ht w h
  | bot =>
    refine ⟨?_, ?_⟩
    · intro s t hs ht
      show s ∪ t = ∅
      rw [hs, ht]; simp
    · intro _ _ _ _; trivial
  | ne =>
    refine ⟨?_, ?_⟩
    · intro s t hs _ht
      exact hs.mono Finset.subset_union_left
    · intro s t hs ht
      show s ∪ t = ∅
      rw [hs, ht]; simp
  | neg ψ ih =>
    have ⟨ihs, iha⟩ := ih
    exact ⟨iha, ihs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨ihs₁, iha₁⟩ := ih₁
    have ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s t ⟨hs₁, hs₂⟩ ⟨ht₁, ht₂⟩
      exact ⟨ihs₁ s t hs₁ ht₁, ihs₂ s t hs₂ ht₂⟩
    · intro s t ⟨s₁, s₂, hsplit_s, ha_s₁, ha_s₂⟩ ⟨t₁, t₂, hsplit_t, ha_t₁, ha_t₂⟩
      refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ?_, ?_⟩
      · show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
        have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact iha₁ s₁ t₁ ha_s₁ ha_t₁
      · exact iha₂ s₂ t₂ ha_s₂ ha_t₂
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨ihs₁, iha₁⟩ := ih₁
    have ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s t ⟨s₁, s₂, hsplit_s, hs_s₁, hs_s₂⟩ ⟨t₁, t₂, hsplit_t, hs_t₁, hs_t₂⟩
      refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ?_, ?_⟩
      · show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
        have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact ihs₁ s₁ t₁ hs_s₁ hs_t₁
      · exact ihs₂ s₂ t₂ hs_s₂ hs_t₂
    · intro s t ⟨ha_s₁, ha_s₂⟩ ⟨ha_t₁, ha_t₂⟩
      exact ⟨iha₁ s t ha_s₁ ha_t₁, iha₂ s t ha_s₂ ha_t₂⟩
  | empt ψ ih =>
    have ⟨ihs, iha⟩ := ih
    refine ⟨?_, ?_⟩
    · intro s t hs ht
      rcases hs with hs | hs
      · rcases ht with ht | ht
        · exact Or.inl (ihs s t hs ht)
        · subst ht; simpa using Or.inl hs
      · subst hs
        rcases ht with ht | ht
        · simpa using Or.inl ht
        · subst ht; simp
    · intro s t hs ht; exact iha s t hs ht
  | poss ψ _ih =>
    refine ⟨?_, ?_⟩
    · intro s t hs ht w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hs w h
      · exact ht w h
    · intro s t hs ht w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hs w h
      · exact ht w h

/-- **Fact 2.7 (BSMLEmpty portion)**: every BSMLEmpty formula has
    sup-closed support. Direct evidence that the team-semantics substrate
    generalises from BSML to BSML⊘ without changes — the substrate's
    payoff at a second logic. -/
theorem supClosed_support (M : BSMLModel W Atom) (φ : Formula Atom) :
    SupClosed { t : Finset W | support M φ t } :=
  fun _ ha _ hb => (support_and_antiSupport_supClosed φ M).1 _ _ ha hb

/-! ### Modal depth and bisim invariance for BSMLEmpty (Theorem 3.8) -/

/-- Modal depth of a `BSMLEmpty.Formula`: `bot`, atoms, `ne` are 0;
    `neg` and `empt` preserve depth; `conj`, `disj` take the max; `poss`
    increments. (`empt`/`⊘` does not contain a modal operator.) -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .bot => 0
  | .ne => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .empt ψ => ψ.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-- **Theorem 3.8 of @cite{aloni-anttila-yang-2024} for BSMLEmpty**: if
    `s ⇌_k s'` and `φ : Formula Atom` has modal depth `≤ k`, then
    `eval M b φ s ↔ eval M' b φ s'` for both polarities. -/
theorem bisim_invariant_eval (φ : Formula Atom) :
    ∀ {k : ℕ}, φ.modalDepth ≤ k →
    ∀ {M : BSMLModel W Atom} {M' : BSMLModel W' Atom}
      {s : Finset W} {s' : Finset W'},
    StateBisim k M s M' s' →
    ∀ b : Bool, eval M b φ s ↔ eval M' b φ s' := by
  induction φ with
  | atom p =>
    intro k _ M M' s s' hbisim b
    cases b <;>
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        rw [← hbw.val_eq]; exact h w hw
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        rw [hbw.val_eq]; exact h w' hw'
  | bot =>
    intro k _ M M' s s' hbisim b
    cases b
    · exact ⟨fun _ => trivial, fun _ => trivial⟩
    · exact hbisim.eq_empty_iff
  | ne =>
    intro k _ M M' s s' hbisim b
    cases b
    · exact hbisim.eq_empty_iff
    · exact hbisim.nonempty_iff
  | neg ψ ih =>
    intro k hd M M' s s' hbisim b
    cases b
    · exact ih hd hbisim true
    · exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k := le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k := le_trans (le_max_right _ _) hd
    cases b
    · constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt false).mp h₁,
               (ih₂ hd₂ hbu false).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm false).mpr h₁
        · exact (ih₂ hd₂ hbu.symm false).mpr h₂
    · constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mp h₁, (ih₂ hd₂ hbisim true).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mpr h₁, (ih₂ hd₂ hbisim true).mpr h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k := le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k := le_trans (le_max_right _ _) hd
    cases b
    · constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mp h₁, (ih₂ hd₂ hbisim false).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mpr h₁, (ih₂ hd₂ hbisim false).mpr h₂⟩
    · constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt true).mp h₁,
               (ih₂ hd₂ hbu true).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm true).mpr h₁
        · exact (ih₂ hd₂ hbu.symm true).mpr h₂
  | empt ψ ih =>
    -- NEW CASE for BSMLEmpty: support .empt = support ψ ∨ s = ∅,
    -- antiSupport .empt = antiSupport ψ.
    intro k hd M M' s s' hbisim b
    cases b
    · -- antiSupport: just antiSupport ψ, use IH directly
      exact ih hd hbisim false
    · -- support: support ψ ∨ s = ∅. The Or is preserved if both
      -- disjuncts are preserved. support ψ by IH; s = ∅ ↔ s' = ∅ under bisim.
      constructor
      · rintro (h | h)
        · exact Or.inl ((ih hd hbisim true).mp h)
        · right
          apply Finset.eq_empty_of_forall_notMem
          intro w' hw'
          obtain ⟨w, hw, _⟩ := hbisim.2 w' hw'
          exact absurd hw (h ▸ Finset.notMem_empty w)
      · rintro (h | h)
        · exact Or.inl ((ih hd hbisim true).mpr h)
        · right
          apply Finset.eq_empty_of_forall_notMem
          intro w hw
          obtain ⟨w', hw', _⟩ := hbisim.1 w hw
          exact absurd hw' (h ▸ Finset.notMem_empty w')
  | poss ψ ih =>
    intro k hd M M' s s' hbisim b
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      cases k with
      | zero => exact absurd hd (by simp [Formula.modalDepth])
      | succ k => exact ⟨k, rfl⟩
    have hdψ : ψ.modalDepth ≤ k := by
      have := hd
      simp only [Formula.modalDepth] at this
      omega
    cases b
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        exact (ih hdψ hbw.accessStateBisim false).mp (h w hw)
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        exact (ih hdψ hbw.accessStateBisim false).mpr (h w' hw')
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        obtain ⟨t, htsub, htne, htsupp⟩ := h w hw
        obtain ⟨t', ht'sub, ht'ne, htbisim⟩ :=
          hbw.accessStateBisim.exists_image_subset htsub
        exact ⟨t', ht'sub, ht'ne htne, (ih hdψ htbisim true).mp htsupp⟩
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        obtain ⟨t', ht'sub, ht'ne, ht'supp⟩ := h w' hw'
        obtain ⟨t, htsub, htne, htbisim⟩ :=
          hbw.accessStateBisim.symm.exists_image_subset ht'sub
        exact ⟨t, htsub, htne ht'ne, (ih hdψ htbisim.symm true).mpr ht'supp⟩

end BSMLEmpty

/-! ### Embeddings: BSMLFormula ↪ extension formulas -/

/-- Embed a BSML formula into BSMLOr by inclusion of constructors. -/
def BSMLOr.ofBSML : BSMLFormula Atom → BSMLOr.Formula Atom
  | .atom p     => .atom p
  | .ne         => .ne
  | .neg ψ      => .neg (ofBSML ψ)
  | .conj ψ₁ ψ₂ => .conj (ofBSML ψ₁) (ofBSML ψ₂)
  | .disj ψ₁ ψ₂ => .disj (ofBSML ψ₁) (ofBSML ψ₂)
  | .poss ψ     => .poss (ofBSML ψ)

/-- Embed a BSML formula into BSMLEmpty. -/
def BSMLEmpty.ofBSML : BSMLFormula Atom → BSMLEmpty.Formula Atom
  | .atom p     => .atom p
  | .ne         => .ne
  | .neg ψ      => .neg (ofBSML ψ)
  | .conj ψ₁ ψ₂ => .conj (ofBSML ψ₁) (ofBSML ψ₂)
  | .disj ψ₁ ψ₂ => .disj (ofBSML ψ₁) (ofBSML ψ₂)
  | .poss ψ     => .poss (ofBSML ψ)

/-- The embedding `BSMLFormula → BSMLOr.Formula` preserves bilateral
    evaluation: BSMLOr is a faithful extension of BSML. -/
theorem BSMLOr.eval_ofBSML (M : BSMLModel W Atom) (b : Bool)
    (φ : BSMLFormula Atom) (t : Finset W) :
    BSMLOr.eval M b (BSMLOr.ofBSML φ) t ↔ Semantics.BSML.eval M b φ t := by
  induction φ generalizing b t with
  | atom p => cases b <;> rfl
  | ne => cases b <;> rfl
  | neg ψ ih =>
    cases b <;> simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval, ih]
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · -- antiSupport conj: split-existential, IH applied to both halves
      simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval]
      constructor
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ false t₁).mp h₁, (ih₂ false t₂).mp h₂⟩
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ false t₁).mpr h₁, (ih₂ false t₂).mpr h₂⟩
    · simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval, ih₁, ih₂]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval, ih₁, ih₂]
    · simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval]
      constructor
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ true t₁).mp h₁, (ih₂ true t₂).mp h₂⟩
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ true t₁).mpr h₁, (ih₂ true t₂).mpr h₂⟩
  | poss ψ ih =>
    cases b
    · simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval]
      constructor
      · intro h w hw; exact (ih false (M.access w)).mp (h w hw)
      · intro h w hw; exact (ih false (M.access w)).mpr (h w hw)
    · simp only [BSMLOr.ofBSML, BSMLOr.eval, Semantics.BSML.eval]
      constructor
      · intro h w hw
        obtain ⟨s, hsub, hne, hsupp⟩ := h w hw
        exact ⟨s, hsub, hne, (ih true s).mp hsupp⟩
      · intro h w hw
        obtain ⟨s, hsub, hne, hsupp⟩ := h w hw
        exact ⟨s, hsub, hne, (ih true s).mpr hsupp⟩

/-- The embedding `BSMLFormula → BSMLEmpty.Formula` preserves bilateral
    evaluation. -/
theorem BSMLEmpty.eval_ofBSML (M : BSMLModel W Atom) (b : Bool)
    (φ : BSMLFormula Atom) (t : Finset W) :
    BSMLEmpty.eval M b (BSMLEmpty.ofBSML φ) t ↔ Semantics.BSML.eval M b φ t := by
  induction φ generalizing b t with
  | atom p => cases b <;> rfl
  | ne => cases b <;> rfl
  | neg ψ ih =>
    cases b <;> simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval, ih]
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval]
      constructor
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ false t₁).mp h₁, (ih₂ false t₂).mp h₂⟩
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ false t₁).mpr h₁, (ih₂ false t₂).mpr h₂⟩
    · simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval, ih₁, ih₂]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval, ih₁, ih₂]
    · simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval]
      constructor
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ true t₁).mp h₁, (ih₂ true t₂).mp h₂⟩
      · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
        exact ⟨t₁, t₂, hsplit, (ih₁ true t₁).mpr h₁, (ih₂ true t₂).mpr h₂⟩
  | poss ψ ih =>
    cases b
    · simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval, ih]
    · simp only [BSMLEmpty.ofBSML, BSMLEmpty.eval, Semantics.BSML.eval]
      constructor
      · intro h w hw
        obtain ⟨s, hsub, hne, hsupp⟩ := h w hw
        exact ⟨s, hsub, hne, (ih true s).mp hsupp⟩
      · intro h w hw
        obtain ⟨s, hsub, hne, hsupp⟩ := h w hw
        exact ⟨s, hsub, hne, (ih true s).mpr hsupp⟩

end AloniAnttilaYang2024
