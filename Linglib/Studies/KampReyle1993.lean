import Linglib.Semantics.Dynamic.DRS.Dynamics
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Kamp & Reyle (1993): From Discourse to Logic
[kamp-reyle-1993]

K&R's worked examples, evaluated through the faithful model-theoretic DRS core
(`Semantics/Dynamic/DRS/`). Each truth-condition is a theorem about the substrate
denotation `DRS.trueRel` (Muskens's relational truth, equivalently `DRS.Realize`),
not a local re-implementation.

## Examples

1. **Existential persistence**: "A man walked in. He sat down." The indefinite's
   discourse referent persists across sentences — `∃ e, man e ∧ walked-in e ∧
   sat-down e` (`persistence_tc`).
2. **Donkey anaphora**: "If a farmer owns a donkey, he beats it." The `⇒`
   verification clause (K&R's Chapter 2 conditional semantics) yields the
   **universal** reading — `∀ farmer-donkey owning pairs, beats`
   (`donkey_universal_reading`). The antecedent's referents are universally
   bound and remain accessible in the consequent.
3. **Negation blocks anaphora**: "A man didn't walk in. *He…" — a referent
   introduced under negation is inaccessible (`negation_tc`).
4. **Subordination/accessibility** (Def. 1.4.10/1.4.11): the antecedent and
   consequent boxes are subordinate to the donkey DRS, the consequent to the
   antecedent — the geometry licensing donkey anaphora.

## Notes

`decide` handles the *structural* facts (subordination, the concrete model); the
truth-conditions are *semantic* claims over arbitrary models, hence proved by
unfolding the verifying-embedding/relational semantics. The merging lemma the
original tested per-example (`reduce_sound`) is now the single substrate theorem
`DRS.toRel_merge`; there is no `.seq` syntax (sequencing *is* `DRS.merge`), so the
compositional-vs-merged equalities are definitional and not re-stated here.
-/

open FirstOrder FirstOrder.Language

namespace KampReyle1993

/-- The relation symbols of the worked examples. -/
inductive KRRel : ℕ → Type
  | man : KRRel 1 | walkedIn : KRRel 1 | satDown : KRRel 1
  | farmer : KRRel 1 | donkey : KRRel 1 | woman : KRRel 1
  | owns : KRRel 2 | beats : KRRel 2 | adores : KRRel 2

/-- The first-order language of the examples (no functions). -/
def krLang : Language := ⟨fun _ => Empty, KRRel⟩

open DRT

variable {M : Type*} [krLang.Structure M]

/-- `RelMap` with the language pinned (a relation symbol alone does not determine
`L`). Lets truth-conditions read as `rm .farmer ![e]`. -/
abbrev rm {n} (R : krLang.Relations n) (x : Fin n → M) : Prop := Structure.RelMap R x

/-! ### Existential persistence -/

/-- "A¹ man walked in. He₁ sat down." — `[u₁ | man u₁, walked-in u₁, sat-down u₁]`. -/
def persistence : DRS krLang ℕ :=
  .mk {1} [.rel .man (![1]), .rel .walkedIn (![1]), .rel .satDown (![1])]

/-- The indefinite's referent persists: truth is existential over a single entity
that is a man, walked in, and sat down. -/
theorem persistence_tc (a : ℕ → M) :
    DRS.trueRel persistence a ↔ ∃ e : M, rm .man ![e] ∧ rm .walkedIn ![e] ∧ rm .satDown ![e] := by
  simp only [DRS.trueRel_iff, persistence, DRS.toRel_mk, Condition.holdsAll_cons,
    Condition.holdsAll_nil, Condition.holds_rel, vecArg₁, and_true]
  constructor
  · rintro ⟨a', _, hm, hw, hs⟩; exact ⟨a' 1, hm, hw, hs⟩
  · rintro ⟨e, hm, hw, hs⟩
    refine ⟨Function.update a 1 e, fun x hx => ?_, ?_, ?_, ?_⟩
    · simp only [Finset.mem_singleton] at hx; exact Function.update_of_ne hx _ _
    · simpa [Function.update_self] using hm
    · simpa [Function.update_self] using hw
    · simpa [Function.update_self] using hs

/-! ### Donkey anaphora (universal reading) -/

/-- The antecedent box `[u₁ u₂ | farmer u₁, donkey u₂, owns u₁ u₂]`. -/
def donkeyAnte : DRS krLang ℕ :=
  .mk {1, 2} [.rel .farmer (![1]), .rel .donkey (![2]), .rel .owns (![1, 2])]
/-- The consequent box `[ | beats u₁ u₂]` (introduces no referents). -/
def donkeyCons : DRS krLang ℕ := .mk ∅ [.rel .beats (![1, 2])]
/-- "If a¹ farmer owns a² donkey, he₁ beats it₂." — `[ | donkeyAnte ⇒ donkeyCons]`. -/
def donkey : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyCons]

/-- The donkey universal reading: the `⇒` verification clause (K&R's Chapter 2
conditional semantics) makes the antecedent's existentials universal — every
owning farmer-donkey pair satisfies `beats`. The empty-universe consequent
reuses the antecedent's values (the anaphora). -/
theorem donkey_universal_reading (a : ℕ → M) :
    DRS.trueRel donkey a ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  simp only [DRS.trueRel_iff, donkey, donkeyAnte, donkeyCons, DRS.toRel_mk,
    Condition.holdsAll_cons, Condition.holdsAll_nil, Condition.holds_imp, Condition.holds_rel,
    vecArg₁, vecArg₂, and_true]
  constructor
  · rintro ⟨a', _, himp⟩ e₁ e₂ ⟨hf, hd, ho⟩
    set v' := Function.update (Function.update a' 1 e₁) 2 e₂ with hv'
    have h1 : v' 1 = e₁ := by simp [hv', Function.update_of_ne, Function.update_self]
    have h2 : v' 2 = e₂ := by simp [hv', Function.update_self]
    obtain ⟨v'', hag, hb⟩ := himp v' ⟨fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [hv', Function.update_of_ne hx.1, Function.update_of_ne hx.2],
      by rw [h1]; exact hf, by rw [h2]; exact hd, by rw [h1, h2]; exact ho⟩
    simpa [hag 1 (by simp), hag 2 (by simp), h1, h2] using hb
  · intro hall
    exact ⟨a, fun _ _ => rfl, fun v' ⟨_, hf, hd, ho⟩ =>
      ⟨v', fun _ _ => rfl, hall (v' 1) (v' 2) ⟨hf, hd, ho⟩⟩⟩

/-! ### Negation blocks anaphora -/

/-- "A¹ man didn't walk in." — `[ | ¬[u₁ | man u₁, walked-in u₁]]`. -/
def negInner : DRS krLang ℕ := .mk {1} [.rel .man (![1]), .rel .walkedIn (![1])]
def negation : DRS krLang ℕ := .mk ∅ [.neg negInner]

/-- Under negation, truth is the *non-existence* of a verifying man — the referent
is bound inside the negation and inaccessible to any continuation. -/
theorem negation_tc (a : ℕ → M) :
    DRS.trueRel negation a ↔ ¬ ∃ e : M, rm .man ![e] ∧ rm .walkedIn ![e] := by
  simp only [DRS.trueRel_iff, negation, negInner, DRS.toRel_mk, Condition.holdsAll_cons,
    Condition.holdsAll_nil, Condition.holds_neg, Condition.holds_rel, vecArg₁, and_true]
  constructor
  · rintro ⟨a', _, hneg⟩ ⟨e, hm, hw⟩
    exact hneg ⟨Function.update a' 1 e, fun x hx => by
        simp only [Finset.mem_singleton] at hx; exact Function.update_of_ne hx _ _,
      by simpa [Function.update_self] using hm, by simpa [Function.update_self] using hw⟩
  · intro hneg
    exact ⟨a, fun _ _ => rfl, fun ⟨a'', _, hm, hw⟩ => hneg ⟨a'' 1, hm, hw⟩⟩

/-! ### Subordination geometry (Def. 1.4.10/1.4.11) -/

/-- The antecedent box is directly subordinate to the donkey DRS. -/
theorem donkey_antecedent_subordinate : DirectlySubordinate donkeyAnte donkey :=
  .impAnte (c := donkeyCons) (by simp [donkey, DRS.conditions])

/-- The consequent box is directly subordinate to the *antecedent* — the `⇒`
asymmetry that makes the antecedent's referents accessible in the consequent. -/
theorem donkey_consequent_subordinate : DirectlySubordinate donkeyCons donkeyAnte :=
  .impCons (show Condition.imp donkeyAnte donkeyCons ∈ donkey.conditions by
    simp [donkey, DRS.conditions])

/-! ### Model evaluation: donkey true in a concrete model

A two-element domain where farmer `0` owns and beats donkey `1`. -/

instance : krLang.Structure (Fin 2) where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args => args 0 = 0
    | 1, .donkey => fun args => args 0 = 1
    | 2, .owns => fun args => args 0 = 0 ∧ args 1 = 1
    | 2, .beats => fun args => args 0 = 0 ∧ args 1 = 1
    | _, _ => fun _ => False

/-- The donkey conditional is true in this model: the only owning pair is `(0,1)`,
which `beats` holds of. -/
theorem donkey_true_in_model (a : ℕ → Fin 2) : DRS.trueRel donkey a := by
  rw [donkey_universal_reading]
  rintro e₁ e₂ ⟨hf, hd, _⟩
  exact ⟨hf, hd⟩

end KampReyle1993
