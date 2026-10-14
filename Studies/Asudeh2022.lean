module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.List.Count
public import Mathlib.Logic.Equiv.Defs
public import Linglib.Data.Examples.Asudeh2022

/-!
# Asudeh (2022): Glue Semantics

In Glue Semantics a word contributes *meaning constructors*, lambda terms paired with formulas
of the implicational fragment of linear logic, and a sentence means what a proof of its clause
from these premises computes, implication elimination being function application and
introduction abstraction. Linear logic lacks weakening and contraction, so a proof uses each
premise exactly once, but keeps commutativity, so word order does not constrain composition.
Asudeh's examples follow: Finnish *Join vettä* and English *I drank water* spread the same three
premises over two and three words, and *Everybody loves somebody* has one syntactic structure
but two proofs, one per scope reading.

## Main statements

* `Term.Linear.rename_perm`, `Term.eval_rename`: reordering the premises of a linear proof keeps
  it linear and keeps its meaning.
* `Term.not_linear_weaken`, `Term.Linear.not_linear_contract`: a proof that leaves a premise
  unused, or lets one premise stand for two, is not linear.
* `finnish_english`: the Finnish and English sentences instantiate the same premises.
* `surface_eval`, `inverse_eval`, `readings_differ`: the two proofs of *Everybody loves
  somebody* mean its two scope readings, which come apart.

## Implementation notes

* A proof is an intrinsically typed λ-term over a list of premises, whose positions its
  variables name; `Term.Linear` counts the uses of each premise and hypothesis, and the
  structural rules are renamings of positions.
* The quantifiers' scope variable `∀S` is instantiated to the clause, as in the paper's proofs.

## References

* [asudeh-2022]
* [girard-1987]
* [klein-sag-1985]
* [kaplan-bresnan-1982]
-/

@[expose] public section

namespace Asudeh2022

/-! ### Proofs as linear terms -/

/-- Formulas of the implicational fragment of linear logic over instantiated atoms. -/
inductive GlueTy (α : Type*)
  | atom (a : α)
  | lolli (A B : GlueTy α)
  deriving DecidableEq, Repr

infixr:25 " ⊸ " => GlueTy.lolli

variable {α : Type*}

/-- A proof from a list of premises, as a λ-term. A variable names a position of the list,
    application is implication elimination, and abstraction discharges a hypothesis appended to
    the list. -/
inductive Term : List (GlueTy α) → GlueTy α → Type _
  | var {Γ : List (GlueTy α)} (n : ℕ) {T : GlueTy α} (h : Γ[n]? = some T) : Term Γ T
  | app {Γ : List (GlueTy α)} {A B : GlueTy α} : Term Γ (A ⊸ B) → Term Γ A → Term Γ B
  | lam {Γ : List (GlueTy α)} (A : GlueTy α) {B : GlueTy α} : Term (Γ ++ [A]) B → Term Γ (A ⊸ B)

/-- The positions a proof uses, with repetition. -/
def Term.uses {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → List ℕ
  | .var n _ => [n]
  | .app f a => f.uses ++ a.uses
  | .lam _ b => b.uses

/-- Every hypothesis is used exactly once. -/
def Term.HypLinear {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → Prop
  | .var _ _ => True
  | .app f a => f.HypLinear ∧ a.HypLinear
  | .lam _ b => b.uses.count Γ.length = 1 ∧ b.HypLinear

instance Term.decHypLinear {Γ : List (GlueTy α)} {T : GlueTy α} :
    (t : Term Γ T) → Decidable t.HypLinear
  | .var _ _ => isTrue trivial
  | .app f a => @instDecidableAnd _ _ (decHypLinear f) (decHypLinear a)
  | .lam _ b => @instDecidableAnd _ _ inferInstance (decHypLinear b)

/-- A proof is linear if it uses every premise and every hypothesis exactly once. -/
def Term.Linear {Γ : List (GlueTy α)} {T : GlueTy α} (t : Term Γ T) : Prop :=
  (∀ i < Γ.length, t.uses.count i = 1) ∧ t.HypLinear

instance {Γ : List (GlueTy α)} {T : GlueTy α} (t : Term Γ T) : Decidable t.Linear :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Curry–Howard evaluation -/

variable (D : α → Type)

/-- The type of meanings a formula pairs with. -/
def GlueTy.denote : GlueTy α → Type
  | .atom a => D a
  | .lolli A B => A.denote → B.denote

/-- Meanings for the premises of a list. -/
inductive Env : List (GlueTy α) → Type _
  | nil : Env []
  | cons {T : GlueTy α} {Γ : List (GlueTy α)} : T.denote D → Env Γ → Env (T :: Γ)

variable {D}

/-- The meaning at a position. -/
def Env.get : {Γ : List (GlueTy α)} → Env D Γ → (n : ℕ) → {T : GlueTy α} →
    Γ[n]? = some T → T.denote D
  | _, .cons v _, 0, _, h => (Option.some.inj h) ▸ v
  | _, .cons _ ρ, n + 1, _, h => ρ.get n h

/-- The meanings extended by one, for a hypothesis. -/
def Env.snoc {T : GlueTy α} : {Γ : List (GlueTy α)} → Env D Γ → T.denote D → Env D (Γ ++ [T])
  | _, .nil, v => .cons v .nil
  | _, .cons u ρ, v => .cons u (ρ.snoc v)

theorem Env.get_congr {Γ : List (GlueTy α)} (ρ : Env D Γ) {n m : ℕ} {T : GlueTy α} (e : n = m)
    (h : Γ[n]? = some T) (h' : Γ[m]? = some T) : ρ.get n h = ρ.get m h' := by
  subst e; rfl

theorem Env.get_snoc_of_lt {A B : GlueTy α} : ∀ {Γ : List (GlueTy α)} (ρ : Env D Γ)
    (v : A.denote D) {n : ℕ} (_ : n < Γ.length) (h : (Γ ++ [A])[n]? = some B)
    (h' : Γ[n]? = some B), (ρ.snoc v).get n h = ρ.get n h'
  | _, .cons _ _, _, 0, _, _, _ => rfl
  | _, .cons _ ρ, v, n + 1, hn, h, h' => get_snoc_of_lt ρ v (by simpa using hn) h h'

theorem Env.get_snoc_of_eq {A : GlueTy α} : ∀ {Γ : List (GlueTy α)} (ρ : Env D Γ)
    (v : A.denote D) {n : ℕ} (_ : n = Γ.length) (h : (Γ ++ [A])[n]? = some A),
    (ρ.snoc v).get n h = v
  | _, .nil, _, 0, _, _ => rfl
  | _, .cons _ ρ, v, n + 1, hn, h => get_snoc_of_eq ρ v (by simpa using hn) h

/-- The meaning a proof assembles, applying for each elimination and abstracting for each
    introduction. -/
def Term.eval {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → Env D Γ → T.denote D
  | .var n h, ρ => ρ.get n h
  | .app f a, ρ => f.eval ρ (a.eval ρ)
  | .lam _ b, ρ => fun v ↦ b.eval (ρ.snoc v)

/-! ### Structural rules

Weakening, contraction and commutativity act on a proof by renaming the positions of its
premises. Commutativity preserves linearity and meaning; weakening and contraction destroy
linearity, so every premise is used exactly once. Asudeh takes this resource sensitivity to do
the work of Klein and Sag's bounded closure and of Kaplan and Bresnan's Completeness and
Coherence. -/

/-- Under a binder, a renaming `f` of `m` premises into `m'` extends to the hypotheses past the
    premises, which shift to follow the new ones. -/
def liftPos (m m' : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ := if n < m then f n else n - m + m'

theorem liftPos_liftPos (m m' : ℕ) (f : ℕ → ℕ) :
    liftPos (m + 1) (m' + 1) (liftPos m m' f) = liftPos m m' f := by
  funext n; simp only [liftPos]; split_ifs <;> omega

variable {Γ Γ' : List (GlueTy α)} {f : ℕ → ℕ}

private theorem lt_length_of_rename (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) {n : ℕ}
    (hn : n < Γ.length) : f n < Γ'.length :=
  (List.getElem?_eq_some_iff.1 (hf n _ (List.getElem?_eq_getElem hn))).1

theorem liftPos_getElem? (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) (A : GlueTy α) :
    ∀ n B, (Γ ++ [A])[n]? = some B →
      (Γ' ++ [A])[liftPos Γ.length Γ'.length f n]? = some B := by
  intro n B h
  unfold liftPos
  split_ifs with hn
  · rw [List.getElem?_append_left hn] at h
    rw [List.getElem?_append_left (lt_length_of_rename hf hn)]
    exact hf n B h
  · rw [List.getElem?_append_right (by omega)] at h
    rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel]

/-- Rename the premises of a proof along a map of positions that preserves their formulas. -/
def Term.rename : {Γ Γ' : List (GlueTy α)} → (f : ℕ → ℕ) →
    (∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) → {T : GlueTy α} → Term Γ T → Term Γ' T
  | _, _, f, hf, _, .var n h => .var (f n) (hf n _ h)
  | _, _, f, hf, _, .app s a => .app (s.rename f hf) (a.rename f hf)
  | Γ, Γ', f, hf, _, .lam A b =>
    .lam A (b.rename (liftPos Γ.length Γ'.length f) (liftPos_getElem? hf A))

theorem Term.uses_rename (f : ℕ → ℕ) (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B)
    {T : GlueTy α} (t : Term Γ T) :
    (t.rename f hf).uses = t.uses.map (liftPos Γ.length Γ'.length f) := by
  induction t generalizing Γ' f with
  | var n h => simp [rename, uses, liftPos, (List.getElem?_eq_some_iff.1 h).1]
  | app s a ihs iha => simp [rename, uses, ihs, iha]
  | lam A b ih =>
    simp only [rename, uses, ih, List.length_append, List.length_singleton, liftPos_liftPos]

theorem Term.HypLinear.rename (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) {T : GlueTy α}
    {t : Term Γ T} (ht : t.HypLinear) : (t.rename f hf).HypLinear := by
  induction t generalizing Γ' f with
  | var => trivial
  | app s a ihs iha => exact ⟨ihs hf ht.1, iha hf ht.2⟩
  | @lam Γ A B b ih =>
    refine ⟨?_, ih _ ht.2⟩
    simp only [uses_rename, List.length_append, List.length_singleton, liftPos_liftPos]
    rw [List.count, List.countP_map, ← ht.1, List.count]
    refine List.countP_congr fun x _ ↦ ?_
    simp only [Function.comp_apply, beq_iff_eq, liftPos]
    split_ifs with hx
    · have := lt_length_of_rename hf hx; omega
    · omega

/-- Reordering the premises of a linear proof leaves it linear, so commutativity holds. -/
theorem Term.Linear.rename_perm {T : GlueTy α} {t : Term Γ T} (ht : t.Linear)
    (σ : Equiv.Perm ℕ) (hσ : ∀ n, Γ.length ≤ n → σ n = n) (hlen : Γ'.length = Γ.length)
    (hf : ∀ n B, Γ[n]? = some B → Γ'[σ n]? = some B) : (t.rename σ hf).Linear := by
  have hlift : liftPos Γ.length Γ'.length σ = σ := by
    funext n; simp only [liftPos, hlen]; split_ifs with hn
    · rfl
    · rw [hσ n (by omega)]; omega
  refine ⟨fun i hi ↦ ?_, ht.2.rename hf⟩
  have hsymm : σ.symm i < Γ.length := by
    by_contra h
    have := hσ (σ.symm i) (by omega)
    rw [Equiv.apply_symm_apply] at this
    omega
  rw [uses_rename, hlift, ← Equiv.apply_symm_apply σ i, List.count_map_of_injective _ _
    σ.injective]
  exact ht.1 _ hsymm

/-- Renaming the premises of a proof, with meanings that agree position by position, does not
    change what it means. -/
theorem Term.eval_rename (f : ℕ → ℕ) (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B)
    {T : GlueTy α} (t : Term Γ T) (ρ : Env D Γ) (ρ' : Env D Γ')
    (hρ : ∀ n B (h : Γ[n]? = some B), ρ'.get (f n) (hf n B h) = ρ.get n h) :
    (t.rename f hf).eval ρ' = t.eval ρ := by
  induction t generalizing Γ' f with
  | var n h => exact hρ n _ h
  | app s a ihs iha => simp only [rename, eval, ihs f hf ρ ρ' hρ, iha f hf ρ ρ' hρ]
  | @lam Γ A B b ih =>
    funext v
    refine ih (liftPos Γ.length Γ'.length f) (liftPos_getElem? hf A) (ρ.snoc v) (ρ'.snoc v)
      fun n C h ↦ ?_
    by_cases hn : n < Γ.length
    · have h₁ : Γ[n]? = some C := by rwa [List.getElem?_append_left hn] at h
      have h₂ : (Γ' ++ [A])[f n]? = some C := by
        rw [List.getElem?_append_left (lt_length_of_rename hf hn)]; exact hf n C h₁
      rw [Env.get_congr _ (by simp [liftPos, hn]) _ h₂,
        Env.get_snoc_of_lt _ _ (lt_length_of_rename hf hn) h₂ (hf n C h₁),
        Env.get_snoc_of_lt _ _ hn h h₁, hρ]
    · have h₁ := h
      rw [List.getElem?_append_right (by omega)] at h₁
      have hlt := (List.getElem?_eq_some_iff.1 h₁).1
      obtain rfl : C = A := by simpa using List.mem_of_getElem? h₁
      simp only [List.length_singleton] at hlt
      rw [Env.get_snoc_of_eq _ _ (by simp only [liftPos, hn, ↓reduceIte]; omega),
        Env.get_snoc_of_eq _ _ (by omega)]

theorem getElem?_append_left_of_eq_some {A : GlueTy α} {n : ℕ} {B : GlueTy α}
    (h : Γ[n]? = some B) : (Γ ++ [A])[n]? = some B := by
  rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]

/-- Weakening adds a premise that the proof does not use. -/
def Term.weaken {T : GlueTy α} (A : GlueTy α) (t : Term Γ T) : Term (Γ ++ [A]) T :=
  t.rename id fun _ _ ↦ getElem?_append_left_of_eq_some

/-- A weakened proof is never linear, since its added premise is left over. -/
theorem Term.not_linear_weaken {T : GlueTy α} (A : GlueTy α) (t : Term Γ T) :
    ¬ (t.weaken A).Linear := by
  intro h
  have h₁ := h.1 Γ.length (by simp)
  rw [weaken, uses_rename, List.count_eq_zero.2] at h₁
  · exact absurd h₁ (by decide)
  · simp only [List.length_append, List.length_singleton, List.mem_map, not_exists, not_and,
      liftPos, id]
    intro x _; split_ifs <;> omega

theorem contract_getElem? {A : GlueTy α} :
    ∀ n B, (Γ ++ [A, A])[n]? = some B → (Γ ++ [A])[min n Γ.length]? = some B := by
  intro n B h
  rcases lt_or_ge n Γ.length with hn | hn
  · rw [min_eq_left hn.le, List.getElem?_append_left hn]
    rwa [List.getElem?_append_left hn] at h
  · rw [List.getElem?_append_right hn] at h
    obtain rfl : B = A := by simpa using List.mem_of_getElem? h
    simp [min_eq_right hn]

/-- Contraction lets one premise stand for two occurrences of its formula. -/
def Term.contract {A T : GlueTy α} (t : Term (Γ ++ [A, A]) T) : Term (Γ ++ [A]) T :=
  t.rename (fun n ↦ min n Γ.length) contract_getElem?

private theorem count_map_contract (m : ℕ) : ∀ l : List ℕ,
    (l.map (liftPos (m + 2) (m + 1) (fun n ↦ min n m))).count m = l.count m + l.count (m + 1)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.count_cons, count_map_contract m l, liftPos, beq_iff_eq]
    split_ifs <;> omega

/-- Contracting a linear proof never yields a linear one, since the merged premise is used
    twice. -/
theorem Term.Linear.not_linear_contract {A T : GlueTy α} {t : Term (Γ ++ [A, A]) T}
    (ht : t.Linear) : ¬ t.contract.Linear := by
  intro h
  have h₁ := h.1 Γ.length (by simp)
  have h₂ := ht.1 Γ.length (by simp)
  have h₃ := ht.1 (Γ.length + 1) (by simp)
  simp only [contract, uses_rename, List.length_append, List.length_cons,
    List.length_nil] at h₁
  rw [count_map_contract, h₂, h₃] at h₁
  omega

/-! ### The substructural hierarchy

A logic is characterized by the structural rules it admits, and admitting more rules makes it
stronger. The Lambek calculus admits none, linear logic commutativity only; relevance logic adds
contraction, affine logic weakening, and intuitionistic logic both. -/

/-- The structural rules whose presence or absence characterizes a logic. -/
inductive StructuralRule
  | weakening
  | contraction
  | commutativity
  deriving DecidableEq

/-- A logic, by the structural rules it admits. -/
abbrev Logic := Finset StructuralRule

/-- The Lambek calculus admits no structural rules. -/
def Logic.lambek : Logic := ∅

/-- Linear logic admits commutativity only. -/
def Logic.linear : Logic := {.commutativity}

/-- A resource logic admits neither weakening nor contraction. -/
def Logic.Resource (l : Logic) : Prop := .weakening ∉ l ∧ .contraction ∉ l

/-- The resource logics are the Lambek calculus and linear logic. -/
theorem resource_iff (l : Logic) : l.Resource ↔ l = .lambek ∨ l = .linear := by
  rw [Logic.lambek, Logic.linear, ← Finset.subset_singleton_iff, Finset.subset_singleton_iff']
  constructor
  · rintro ⟨hw, hc⟩ r hr
    cases r <;> simp_all
  · intro h
    exact ⟨fun hw ↦ StructuralRule.noConfusion (h _ hw),
      fun hc ↦ StructuralRule.noConfusion (h _ hc)⟩

/-- Linear logic is the commutative resource logic. -/
theorem commutative_resource_iff (l : Logic) :
    l.Resource ∧ .commutativity ∈ l ↔ l = .linear := by
  rw [resource_iff]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · simp [Logic.lambek] at h
    · rfl
  · rintro rfl
    exact ⟨.inr rfl, by simp [Logic.linear]⟩

/-! ### The paper's proofs -/

/-- The instantiated atoms of the paper's examples. -/
inductive Label
  | a | b | c | l | e | s | p | w | d
  deriving DecidableEq, Repr

open GlueTy (atom)

/-- Recurrying by hypothetical reasoning turns a head taking `a` then `b` into one taking `b`
    then `a`, discharging both hypotheses. -/
def recurry :
    Term [atom Label.a ⊸ atom Label.b ⊸ atom Label.c]
      (atom Label.b ⊸ atom Label.a ⊸ atom Label.c) :=
  .lam (atom Label.b) (.lam (atom Label.a) (.app (.app (.var 0 rfl) (.var 2 rfl)) (.var 1 rfl)))

theorem recurry_linear : recurry.Linear := by decide

/-- The recurried proof means the same function with its arguments swapped. -/
theorem recurry_eval {D : Label → Type} (f : D .a → D .b → D .c) :
    recurry.eval (.cons f .nil) = fun u v ↦ f v u :=
  rfl

/-- The meaning constructors of *Alex likes Blake*, word by word. -/
def alexLikesBlake : List (List (GlueTy Label)) :=
  [[atom Label.a], [atom Label.b ⊸ atom Label.a ⊸ atom Label.l], [atom Label.b]]

/-- The single normal-form proof applies *likes* to *Blake* and then to *Alex*, taking the
    premises out of word order. -/
def likesProof : Term alexLikesBlake.flatten (atom Label.l) :=
  .app (.app (.var 1 rfl) (.var 2 rfl)) (.var 0 rfl)

theorem likesProof_linear : likesProof.Linear := by decide

theorem likesProof_eval {D : Label → Type} (alex : D .a) (like : D .b → D .a → D .l)
    (blake : D .b) : likesProof.eval (.cons alex (.cons like (.cons blake .nil))) =
      like blake alex :=
  rfl

/-- The meaning constructors of Finnish *Join vettä*, where *join* contributes the speaker and
    the drinking and *vettä* the water. -/
def finnish : List (List (GlueTy Label)) :=
  [[atom Label.p, atom Label.w ⊸ atom Label.p ⊸ atom Label.d], [atom Label.w]]

/-- The meaning constructors of English *I drank water*, one per word. -/
def english : List (List (GlueTy Label)) :=
  [[atom Label.p], [atom Label.w ⊸ atom Label.p ⊸ atom Label.d], [atom Label.w]]

/-- Two words and three words instantiate the same premises. -/
theorem finnish_english : finnish.flatten = english.flatten ∧ finnish.length ≠ english.length :=
  by decide

/-- The one normal-form proof of *I drank water* in either language. -/
def drinkProof : Term english.flatten (atom Label.d) :=
  .app (.app (.var 1 rfl) (.var 2 rfl)) (.var 0 rfl)

theorem drinkProof_linear : drinkProof.Linear := by decide

theorem drinkProof_eval {D : Label → Type} (speaker : D .p) (drink : D .w → D .p → D .d)
    (water : D .w) : drinkProof.eval (.cons speaker (.cons drink (.cons water .nil))) =
      drink water speaker :=
  rfl

/-- The meaning constructors of *Everybody loves somebody*, word by word, with both quantifiers'
    scope instantiated to the clause. -/
def everybodyLovesSomebody : List (List (GlueTy Label)) :=
  [[(atom Label.e ⊸ atom Label.l) ⊸ atom Label.l], [atom Label.s ⊸ atom Label.e ⊸ atom Label.l],
    [(atom Label.s ⊸ atom Label.l) ⊸ atom Label.l]]

/-- Surface scope hypothesizes the object and then the subject, discharges the object under
    *somebody* and then the subject under *everybody*. -/
def surface : Term everybodyLovesSomebody.flatten (atom Label.l) :=
  .app (.var 0 rfl) (.lam (atom Label.e)
    (.app (.var 2 rfl) (.lam (atom Label.s) (.app (.app (.var 1 rfl) (.var 4 rfl)) (.var 3 rfl)))))

/-- Inverse scope hypothesizes the object only, applies *everybody* to *loves* of it, and
    discharges the object under *somebody*. -/
def inverse : Term everybodyLovesSomebody.flatten (atom Label.l) :=
  .app (.var 2 rfl) (.lam (atom Label.s) (.app (.var 0 rfl) (.app (.var 1 rfl) (.var 3 rfl))))

theorem surface_linear : surface.Linear := by decide

theorem inverse_linear : inverse.Linear := by decide

/-- Meanings for the scope example, with entities for the two arguments and propositions for
    the clause. -/
def scopeDomain (E : Type) : Label → Type
  | .l | .c | .d => Prop
  | _ => E

/-- The premises' meanings are the two generalized quantifiers over persons and *love*. -/
def scopeEnv {E : Type} (person : E → Prop) (love : E → E → Prop) :
    Env (scopeDomain E) everybodyLovesSomebody.flatten :=
  .cons (fun Q ↦ ∀ x, person x → Q x) (.cons love (.cons (fun Q ↦ ∃ y, person y ∧ Q y) .nil))

/-- The surface proof means that every person loves some person. -/
theorem surface_eval {E : Type} (person : E → Prop) (love : E → E → Prop) :
    surface.eval (scopeEnv person love) = ∀ x, person x → ∃ y, person y ∧ love y x :=
  rfl

/-- The inverse proof means that some person is loved by every person. -/
theorem inverse_eval {E : Type} (person : E → Prop) (love : E → E → Prop) :
    inverse.eval (scopeEnv person love) = ∃ y, person y ∧ ∀ x, person x → love y x :=
  rfl

/-- The two proofs are two readings. Where each of two persons loves only the other, the
    surface reading holds and the inverse one fails. -/
theorem readings_differ :
    surface.eval (scopeEnv (fun _ : Bool ↦ True) (· ≠ ·)) ∧
      ¬ inverse.eval (scopeEnv (fun _ : Bool ↦ True) (· ≠ ·)) := by
  rw [surface_eval, inverse_eval]
  exact ⟨fun x _ ↦ ⟨!x, trivial, Bool.not_ne_self x⟩, fun ⟨y, _, h⟩ ↦ h y trivial rfl⟩

/-! ### The paper's examples -/

/-- The meaning constructors a row's words contribute. -/
def lexicon? (r : Datum) : Option (List (List (GlueTy Label))) :=
  match r.language, r.feature? "premises" with
  | "stan1293", some "likes, alex, blake" => some alexLikesBlake
  | "stan1293", some "love, every, some" => some everybodyLovesSomebody
  | "finn1318", some "speaker, drink, water" => some finnish
  | "stan1293", some "speaker, drink, water" => some english
  | _, _ => none

/-- The number of words of a row's sentence, which are separated by single spaces. -/
def wordCount (r : Datum) : ℕ := (r.primaryText.toList.filter (· = ' ')).length + 1

/-- Every row has a lexicon, and each of its words contributes meaning constructors. -/
theorem rows_lexicon : ∀ r ∈ Examples.all, ∃ lex ∈ lexicon? r, wordCount r = lex.length := by
  decide

end Asudeh2022
