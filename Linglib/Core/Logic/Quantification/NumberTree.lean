import Linglib.Core.Logic.Quantification.Defs

/-!
# Number-Tree Quantifiers
@cite{van-benthem-1984} @cite{van-benthem-1986}

The number-tree representation of conservative, quantity-invariant GQs.
Under CONSERV + QUANT, a quantifier's truth value depends only on
`a = |A ∩ B|` and `b = |A \ B|`, yielding a function `ℕ → ℕ → Bool`.

Includes impossibility theorems (§10), the Square of Opposition
uniqueness theorem (§10e), the GQ→NumberTreeGQ bridge (§10f),
and counting quantifiers (§11).
-/

namespace Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §10 Number-Tree Impossibility Theorems (§3.2)
-- ============================================================================

/-- Number-tree representation of a conservative, quantity-invariant GQ.
    Under CONSERV + QUANT, a quantifier's truth value depends only on
    `a = |A ∩ B|` and `b = |A \ B|` (§2, "tree of numbers").
    This is inherently cross-domain: any `(a, b)` pair is realizable in some
    universe of size ≥ a + b. -/
abbrev NumberTreeGQ := Nat → Nat → Bool

namespace NumberTreeGQ

/-- Variety for number-tree quantifiers: Q is non-trivial. -/
def Variety (q : NumberTreeGQ) : Prop :=
  (∃ a b, q a b = true) ∧ (∃ a b, q a b = false)

/-- Thm 3.2.1: No asymmetric CONSERV+QUANT quantifiers exist.

    On the number tree, asymmetry means: for all `a b c`,
    `q(a, b) → ¬q(a, c)` — because `|A ∩ B| = a` and `|B \ A| = c` is free
    (any `c` is realizable in a large enough universe).

    Proof: Set `c = b`. Then `q(a, b) → ¬q(a, b)`, so `q` is identically
    false. Contradicts Variety. -/
theorem no_asymmetric (q : NumberTreeGQ) (hVar : q.Variety)
    (hAsym : ∀ a b c, q a b = true → q a c = false) : False := by
  obtain ⟨⟨a, b, hab⟩, _⟩ := hVar
  exact absurd hab (Bool.eq_false_iff.mp (hAsym a b b hab))

/-- §3.2 consequence: No strict partial order quantifiers.

    On the number tree, irreflexivity is `∀ n, q(n, 0) = false` (since
    `Q(A,A)` has `|A ∩ A| = n`, `|A \ A| = 0`). Transitivity (with C = A
    in the 3-set diagram) gives: `q(a, b) ∧ q(a, c) → q(a+b, 0)`.

    Proof: From transitivity, `q(a, b) → q(a, c) → q(a+b, 0)`.
    From irreflexivity, `q(a+b, 0) = false`. So `q(a, b) → q(a, c) = false`
    — number-tree asymmetry. Apply `no_asymmetric`. -/
theorem no_strict_partial_order (q : NumberTreeGQ) (hVar : q.Variety)
    (hIrrefl : ∀ n, q n 0 = false)
    (hTrans : ∀ a b c, q a b = true → q a c = true → q (a + b) 0 = true) :
    False := by
  exact no_asymmetric q hVar (λ a b c hab => by
    by_contra h
    rw [Bool.not_eq_false] at h
    have := hTrans a b c hab h
    rw [hIrrefl] at this
    exact absurd this (by decide))

/-- Thm 3.2.3: No Euclidean CONSERV+QUANT quantifiers exist.

    On the number tree (3-set Venn diagram with 7 free size parameters
    `p, q, r, s, t, u` plus one more), the Euclidean property becomes:
    `q(p+q_, r+s) ∧ q(p+r, q_+s) → q(p+t, q_+u)` for all `p q_ r s t u`.

    Proof (4 steps):
    1. From Variety witness `q(α, β) = true`, set `p=α, q_=0, r=0, s=β`:
       `q(α+t, u)` for all `t, u`. So `q(a, b) = true` for `a ≥ α`.
    2. If `α = 0`, step 1 gives `q ≡ true`, contradicting Variety.
       If `α > 0`: pair `q(α, 2α)` and `q(2α, α)` (both from step 1)
       with `p=0, q_=α, r=2α, s=0`: get `q(t, α+u)` for all `t, u`.
       Combined: `q(a, b) = true` when `a ≥ α` or `b ≥ α`.
    3. `q(0, α)` (from step 2) and `q(α, 0)` (from step 1) with
       `p=0, q_=0, r=α, s=0`: get `q(t, u)` for all `t, u`.
    4. Contradicts Variety. -/
theorem no_euclidean (q : NumberTreeGQ) (hVar : q.Variety)
    (hEuc : ∀ p q_ r s t u,
      q (p + q_) (r + s) = true → q (p + r) (q_ + s) = true →
      q (p + t) (q_ + u) = true) : False := by
  obtain ⟨⟨α, β, hαβ⟩, ⟨a₀, b₀, hFalse⟩⟩ := hVar
  -- Step 1: q(α + t, u) for all t, u
  -- Use hEuc with p=α, q_=0, r=0, s=β: q(α+0)(0+β) ∧ q(α+0)(0+β) → q(α+t)(0+u)
  have step1 : ∀ t u, q (α + t) u = true := by
    intro t u
    have := hEuc α 0 0 β t u (by rwa [Nat.add_zero, Nat.zero_add])
      (by rwa [Nat.add_zero, Nat.zero_add])
    simpa [Nat.zero_add] using this
  -- Step 3 (shortcut): q(α, 0) from step1 (t=0, u=0)
  have qα0 : q α 0 = true := step1 0 0
  -- If α = 0: step1 gives q(t, u) for all t, u → contradiction
  by_cases hα : α = 0
  · subst hα; simp only [Nat.zero_add] at step1; rw [step1] at hFalse; exact absurd hFalse (by decide)
  -- α > 0
  -- Step 2: q(t, α + u) for all t, u
  -- q(α, β) is our witness. Use step1 to get q at larger first args.
  -- q(2*α, α) from step1 (t = α, u = α)
  have q_2α_α : q (2 * α) α = true := by
    have := step1 α α; rwa [show α + α = 2 * α from by omega] at this
  -- q(α, 2*α) via step1: need q(α + t', 2*α) — take t' = 0
  have q_α_2α : q α (2 * α) = true := by
    have := step1 0 (2 * α); rwa [Nat.add_zero] at this
  -- Use hEuc with p=0, q_=α, r=2*α, s=0: q(0+α)(2α+0) ∧ q(0+2α)(α+0) → q(0+t)(α+u)
  have step2 : ∀ t u, q t (α + u) = true := by
    intro t u
    have := hEuc 0 α (2 * α) 0 t u
      (by rwa [Nat.zero_add, Nat.add_zero])
      (by rwa [Nat.zero_add, Nat.add_zero])
    simpa [Nat.zero_add] using this
  -- Step 3: q(0, α) from step2 (t=0, u=0)
  have q0α : q 0 α = true := by have := step2 0 0; rwa [Nat.add_zero] at this
  -- Use hEuc with p=0, q_=0, r=α, s=0: q(0+0)(α+0) ∧ q(0+α)(0+0) → q(0+t)(0+u)
  have step3 : ∀ t u, q t u = true := by
    intro t u
    have := hEuc 0 0 α 0 t u
      (by rwa [Nat.zero_add, Nat.add_zero])
      (by rwa [Nat.zero_add, Nat.add_zero])
    simpa [Nat.zero_add] using this
  -- Step 4: contradiction with Variety
  rw [step3] at hFalse; exact absurd hFalse (by decide)

-- §10b Number-tree representations of the Square of Opposition

/-- "all" on the number tree: Q(A,B) iff A ⊆ B iff |A\B| = 0. -/
def allNT : NumberTreeGQ := λ _ b => b == 0

/-- "some" on the number tree: Q(A,B) iff A∩B ≠ ∅ iff |A∩B| ≥ 1. -/
def someNT : NumberTreeGQ := λ a _ => decide (a ≥ 1)

/-- "no" on the number tree: Q(A,B) iff A∩B = ∅ iff |A∩B| = 0. -/
def noNT : NumberTreeGQ := λ a _ => a == 0

/-- "not all" on the number tree: Q(A,B) iff A ⊄ B iff |A\B| ≥ 1. -/
def notAllNT : NumberTreeGQ := λ _ b => decide (b ≥ 1)

-- §10c Additivity (§5.2, p.460)

/-- Additive: (a,b) ∈ Q and (a',b') ∈ Q implies (a+a', b+b') ∈ Q.
    p.460: all, some, no, not all are additive.
    Additivity means Q's truth set is closed under componentwise addition
    in the number tree. -/
def Additive (q : NumberTreeGQ) : Prop :=
  ∀ a b a' b', q a b = true → q a' b' = true → q (a + a') (b + b') = true

theorem allNT_additive : Additive allNT := by
  intro a b a' b' h1 h2
  simp only [allNT, beq_iff_eq] at *; omega

theorem someNT_additive : Additive someNT := by
  intro a b a' b' h1 h2
  simp only [someNT, decide_eq_true_eq] at *; omega

theorem noNT_additive : Additive noNT := by
  intro a b a' b' h1 h2
  simp only [noNT, beq_iff_eq] at *; omega

theorem notAllNT_additive : Additive notAllNT := by
  intro a b a' b' h1 h2
  simp only [notAllNT, decide_eq_true_eq] at *; omega

-- §10d Continuity, PLUS, UNIF (§4.3, §7)

/-- Right continuity on the number tree (CONT): on each diagonal a+b = n,
    the true points form a contiguous interval.
    §4.3: all right-monotone quantifiers are
    continuous. "precisely one" is continuous but non-monotone. -/
def RightCont (q : NumberTreeGQ) : Prop :=
  ∀ n a₁ a₂ a, a₁ ≤ a → a ≤ a₂ → a₂ ≤ n →
    q a₁ (n - a₁) = true → q a₂ (n - a₂) = true →
    q a (n - a) = true

/-- Left continuity on the number tree: on each diagonal, the false
    points (absence) also form a contiguous interval.
    §4.3: equivalent to right continuity of ¬Q. -/
def LeftCont (q : NumberTreeGQ) : Prop :=
  ∀ n a₁ a₂ a, a₁ ≤ a → a ≤ a₂ → a₂ ≤ n →
    q a₁ (n - a₁) = false → q a₂ (n - a₂) = false →
    q a (n - a) = false

/-- PLUS (§7): adding one individual to the
    situation cannot create a "dead end." Both presence and absence must
    be extensible in at least one direction.
    - For + positions: q(a+1,b) or q(a,b+1) is true.
    - For − positions: q(a+1,b) or q(a,b+1) is false. -/
def Plus (q : NumberTreeGQ) : Prop :=
  (∀ a b, q a b = true → q (a + 1) b = true ∨ q a (b + 1) = true) ∧
  (∀ a b, q a b = false → q (a + 1) b = false ∨ q a (b + 1) = false)

/-- UNIF (§7): the addition experiment
    (a,b) → (a+1,b) and (a,b) → (a,b+1) always yields the same
    pattern for positions of the same truth value. The experiment
    result depends only on whether Q holds, not on *where* in the
    tree we are. -/
def Uniform (q : NumberTreeGQ) : Prop :=
  (∀ a₁ b₁ a₂ b₂, q a₁ b₁ = true → q a₂ b₂ = true →
    q (a₁ + 1) b₁ = q (a₂ + 1) b₂ ∧ q a₁ (b₁ + 1) = q a₂ (b₂ + 1)) ∧
  (∀ a₁ b₁ a₂ b₂, q a₁ b₁ = false → q a₂ b₂ = false →
    q (a₁ + 1) b₁ = q (a₂ + 1) b₂ ∧ q a₁ (b₁ + 1) = q a₂ (b₂ + 1))

-- Verification: the four basic quantifiers satisfy CONT, PLUS, UNIF

private theorem beq_zero_iff (n : Nat) : (n == 0) = true ↔ n = 0 := beq_iff_eq
private theorem beq_zero_false_iff (n : Nat) : (n == 0) = false ↔ n ≠ 0 := by
  cases n <;> simp

theorem allNT_rightCont : RightCont allNT := by
  intro n a₁ _ a ha₁ _ _ h1 _
  simp only [allNT, beq_zero_iff] at *; omega

theorem someNT_rightCont : RightCont someNT := by
  intro n a₁ _ a ha₁ _ _ h1 _
  simp only [someNT, decide_eq_true_eq] at *; omega

theorem noNT_rightCont : RightCont noNT := by
  intro n _ a₂ a _ ha₂ _ _ h2
  simp only [noNT, beq_zero_iff] at *; omega

theorem notAllNT_rightCont : RightCont notAllNT := by
  intro n a₁ _ a ha₁ ha₂ ha₂n h1 _
  simp only [notAllNT, decide_eq_true_eq] at *; omega

theorem allNT_plus : Plus allNT := by
  unfold Plus allNT
  exact ⟨λ _ _ h => Or.inl h,
         λ _ b h => Or.inr (by cases b <;> simp_all)⟩

theorem someNT_plus : Plus someNT := by
  unfold Plus someNT
  constructor
  · intro a _ h; left; simp only [decide_eq_true_eq] at *; omega
  · intro a _ h; right; simp only [decide_eq_false_iff_not, not_le] at *; omega

theorem noNT_plus : Plus noNT := by
  unfold Plus noNT
  exact ⟨λ _ _ h => Or.inr (by simp only [beq_zero_iff] at h; subst h; simp),
         λ _ _ _ => Or.inl (by simp)⟩

theorem notAllNT_plus : Plus notAllNT := by
  unfold Plus notAllNT
  constructor
  · intro _ b h; left; simp only [decide_eq_true_eq] at *; omega
  · intro _ b h; left; simp only [decide_eq_false_iff_not, not_le] at *; omega

theorem allNT_uniform : Uniform allNT := by
  unfold Uniform allNT
  constructor
  · intro _ b₁ _ b₂ h1 h2
    simp only [beq_zero_iff] at h1 h2; subst h1; subst h2; simp
  · intro _ b₁ _ b₂ h1 h2
    simp only [beq_zero_false_iff] at h1 h2
    exact ⟨by rw [beq_false_of_ne h1, beq_false_of_ne h2],
           by rw [beq_false_of_ne (Nat.succ_ne_zero b₁), beq_false_of_ne (Nat.succ_ne_zero b₂)]⟩

theorem someNT_uniform : Uniform someNT := by
  unfold Uniform someNT
  constructor
  · intro a₁ _ a₂ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega
  · intro a₁ _ a₂ _ h1 h2
    simp only [decide_eq_false_iff_not, not_le] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega

theorem noNT_uniform : Uniform noNT := by
  unfold Uniform noNT
  constructor
  · intro a₁ _ a₂ _ h1 h2
    simp only [beq_zero_iff] at h1 h2; subst h1; subst h2; simp
  · intro a₁ _ a₂ _ h1 h2
    simp only [beq_zero_false_iff] at h1 h2
    exact ⟨by rw [beq_false_of_ne (Nat.succ_ne_zero a₁), beq_false_of_ne (Nat.succ_ne_zero a₂)],
           by rw [beq_false_of_ne h1, beq_false_of_ne h2]⟩

theorem notAllNT_uniform : Uniform notAllNT := by
  unfold Uniform notAllNT
  constructor
  · intro _ b₁ _ b₂ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega
  · intro _ b₁ _ b₂ h1 h2
    simp only [decide_eq_false_iff_not, not_le] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega

-- §10e Theorem 7.1: Square of Opposition uniqueness

/-- Two number-tree quantifiers that agree at (0,0) and satisfy the same
    row/column recurrence must be identical. Used to factor out the common
    double-induction pattern in `square_uniqueness`. -/
private theorem grid_ext (f g : ℕ → ℕ → Bool)
    (h0 : f 0 0 = g 0 0)
    (hrow : ∀ a, f a 0 = g a 0 → f (a + 1) 0 = g (a + 1) 0)
    (hcol : ∀ a b, f a b = g a b → f a (b + 1) = g a (b + 1)) :
    f = g := by
  funext a
  induction a with
  | zero => funext b; induction b with
    | zero => exact h0
    | succ _ ihb => exact hcol 0 _ ihb
  | succ a iha => funext b; induction b with
    | zero => exact hrow a (congr_fun iha 0)
    | succ _ ihb => exact hcol _ _ ihb

/-- The six postulates that §7 uses to characterize
    the Square of Opposition. -/
structure SixPostulates (q : NumberTreeGQ) : Prop where
  variety : q.Variety
  cont    : q.RightCont
  lcont   : q.LeftCont
  plus    : q.Plus
  uniform : q.Uniform

/-- @cite{van-benthem-1986} Thm 7.1: On the finite sets, the only
    CONSERV+QUANT quantifiers satisfying VAR, CONT, PLUS, and UNIF are
    precisely the four corners of the logical Square of Opposition:
    **all**, **some**, **no**, and **not all**.

    Proof strategy: UNIF reduces every cell's truth value to four
    experiment booleans (tr, tu, fr, fu). PLUS eliminates 12 of the
    16 combinations; CONT and VAR eliminate 2 more (via path
    inconsistencies). The 4 survivors each determine exactly one
    quantifier, proved via `grid_ext`. -/
theorem square_uniqueness (q : NumberTreeGQ) (h : SixPostulates q) :
    q = allNT ∨ q = someNT ∨ q = noNT ∨ q = notAllNT := by
  obtain ⟨⟨at_, bt, habt⟩, ⟨af, bf, habf⟩⟩ := h.variety
  -- UNIF: every cell's step is determined by four experiment booleans
  have hTR (a b : ℕ) (hq : q a b = true) : q (a + 1) b = q (at_ + 1) bt :=
    (h.uniform.1 a b at_ bt hq habt).1
  have hTU (a b : ℕ) (hq : q a b = true) : q a (b + 1) = q at_ (bt + 1) :=
    (h.uniform.1 a b at_ bt hq habt).2
  have hFR (a b : ℕ) (hq : q a b = false) : q (a + 1) b = q (af + 1) bf :=
    (h.uniform.2 a b af bf hq habf).1
  have hFU (a b : ℕ) (hq : q a b = false) : q a (b + 1) = q af (bf + 1) :=
    (h.uniform.2 a b af bf hq habf).2
  have hPT := h.plus.1 at_ bt habt
  have hPF := h.plus.2 af bf habf
  have var_not_all_true (h0 : q 0 0 = true)
      (htr : q (at_ + 1) bt = true) (htu : q at_ (bt + 1) = true) : False := by
    have : ∀ a b, q a b = true := by
      intro a; induction a with
      | zero => intro b; induction b with
        | zero => exact h0
        | succ _ ihb => rw [hTU 0 _ ihb]; exact htu
      | succ a iha => intro b; induction b with
        | zero => rw [hTR a 0 (iha 0)]; exact htr
        | succ _ ihb => rw [hTU _ _ ihb]; exact htu
    exact absurd (this af bf) (by rw [habf]; decide)
  have var_not_all_false (h0 : q 0 0 = false)
      (hfr : q (af + 1) bf = false) (hfu : q af (bf + 1) = false) : False := by
    have : ∀ a b, q a b = false := by
      intro a; induction a with
      | zero => intro b; induction b with
        | zero => exact h0
        | succ _ ihb => rw [hFU 0 _ ihb]; exact hfu
      | succ a iha => intro b; induction b with
        | zero => rw [hFR a 0 (iha 0)]; exact hfr
        | succ _ ihb => rw [hFU _ _ ihb]; exact hfu
    exact absurd (this at_ bt) (by rw [habt]; decide)
  -- === Main case analysis on (tr, tu, fr, fu) ===
  rcases Bool.eq_false_or_eq_true (q (at_ + 1) bt) with htr | htr
  · -- tr = TRUE
    rcases Bool.eq_false_or_eq_true (q at_ (bt + 1)) with htu | htu
    · -- (T, T, *, *)
      rcases Bool.eq_false_or_eq_true (q (af + 1) bf) with hfr | hfr
      · rcases Bool.eq_false_or_eq_true (q af (bf + 1)) with hfu | hfu
        · -- (T,T,T,T) → PLUS-F violation
          exfalso; rcases hPF with h | h
          · exact absurd hfr (by rw [h]; decide)
          · exact absurd hfu (by rw [h]; decide)
        · -- (T,T,T,F) → someNT
          rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
          · exact (var_not_all_true hv htr htu).elim
          · right; left
            exact grid_ext q someNT hv
              (λ a heq => by
                cases hqa : q a 0
                · rw [hFR a 0 hqa, hfr]; rfl
                · rw [hTR a 0 hqa, htr]; rfl)
              (λ a b heq => by
                cases hqa : q a b
                · rw [hFU a b hqa, hfu]; exact (heq.symm.trans hqa).symm
                · rw [hTU a b hqa, htu]; exact (heq.symm.trans hqa).symm)
      · rcases Bool.eq_false_or_eq_true (q af (bf + 1)) with hfu | hfu
        · -- (T,T,F,T) → notAllNT
          rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
          · exact (var_not_all_true hv htr htu).elim
          · right; right; right
            exact grid_ext q notAllNT hv
              (λ a heq => by
                cases hqa : q a 0
                · rw [hFR a 0 hqa, hfr]; rfl
                · have h := heq.symm.trans hqa; simp [notAllNT] at h)
              (λ a b heq => by
                cases hqa : q a b
                · rw [hFU a b hqa, hfu]; rfl
                · rw [hTU a b hqa, htu]; rfl)
        · -- (T,T,F,F) → VAR contradiction
          rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
          · exact (var_not_all_true hv htr htu).elim
          · exact (var_not_all_false hv hfr hfu).elim
    · -- tu = FALSE
      rcases Bool.eq_false_or_eq_true (q (af + 1) bf) with hfr | hfr
      · -- PLUS-F forces fu = F
        have hfu : q af (bf + 1) = false := by
          rcases hPF with h | h
          · exact absurd hfr (by rw [h]; decide)
          · exact h
        -- (T,F,T,F) → path inconsistency
        exfalso
        rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
        · have h10 : q 1 0 = true := by rw [hTR 0 0 hv, htr]
          have h01 : q 0 1 = false := by rw [hTU 0 0 hv, htu]
          have h11a : q 1 1 = false := by rw [hTU 1 0 h10, htu]
          have h11b : q 1 1 = true := by rw [hFR 0 1 h01, hfr]
          rw [h11a] at h11b; exact absurd h11b (by decide)
        · have h10 : q 1 0 = true := by rw [hFR 0 0 hv, hfr]
          have h01 : q 0 1 = false := by rw [hFU 0 0 hv, hfu]
          have h11a : q 1 1 = false := by rw [hTU 1 0 h10, htu]
          have h11b : q 1 1 = true := by rw [hFR 0 1 h01, hfr]
          rw [h11a] at h11b; exact absurd h11b (by decide)
      · rcases Bool.eq_false_or_eq_true (q af (bf + 1)) with hfu | hfu
        · -- (T,F,F,T) → CONT contradiction
          exfalso
          rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
          · have h10 : q 1 0 = true := by rw [hTR 0 0 hv, htr]
            have h01 : q 0 1 = false := by rw [hTU 0 0 hv, htu]
            have h11 : q 1 1 = false := by rw [hTU 1 0 h10, htu]
            have h02 : q 0 2 = true := by rw [hFU 0 1 h01, hfu]
            have h20 : q 2 0 = true := by rw [hTR 1 0 h10, htr]
            exact absurd (h.cont 2 0 2 1 (by omega) (by omega) (by omega) h02 h20)
              (by rw [h11]; decide)
          · have h10 : q 1 0 = false := by rw [hFR 0 0 hv, hfr]
            have h01 : q 0 1 = true := by rw [hFU 0 0 hv, hfu]
            have h11 : q 1 1 = true := by rw [hFU 1 0 h10, hfu]
            have h02 : q 0 2 = false := by rw [hTU 0 1 h01, htu]
            have h20 : q 2 0 = false := by rw [hFR 1 0 h10, hfr]
            exact absurd h11 (Bool.eq_false_iff.mp
              (h.lcont 2 0 2 1 (by omega) (by omega) (by omega) h02 h20))
        · -- (T,F,F,F) → allNT
          rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
          · left
            exact grid_ext q allNT hv
              (λ a heq => by
                cases hqa : q a 0
                · have h := heq.symm.trans hqa; simp [allNT] at h
                · rw [hTR a 0 hqa, htr]; rfl)
              (λ a b heq => by
                cases hqa : q a b
                · rw [hFU a b hqa, hfu]; rfl
                · rw [hTU a b hqa, htu]; rfl)
          · exact (var_not_all_false hv hfr hfu).elim
  · -- tr = FALSE → PLUS forces tu = TRUE
    have htu : q at_ (bt + 1) = true := by
      rcases hPT with h | h
      · exact absurd htr (by rw [h]; decide)
      · exact h
    rcases Bool.eq_false_or_eq_true (q (af + 1) bf) with hfr | hfr
    · -- PLUS-F forces fu = F
      have hfu : q af (bf + 1) = false := by
        rcases hPF with h | h
        · exact absurd hfr (by rw [h]; decide)
        · exact h
      -- (F,T,T,F) → CONT contradiction
      exfalso
      rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
      · have h10 : q 1 0 = false := by rw [hTR 0 0 hv, htr]
        have h01 : q 0 1 = true := by rw [hTU 0 0 hv, htu]
        have h11 : q 1 1 = false := by rw [hFU 1 0 h10, hfu]
        have h02 : q 0 2 = true := by rw [hTU 0 1 h01, htu]
        have h20 : q 2 0 = true := by rw [hFR 1 0 h10, hfr]
        exact absurd (h.cont 2 0 2 1 (by omega) (by omega) (by omega) h02 h20)
          (by rw [h11]; decide)
      · have h10 : q 1 0 = true := by rw [hFR 0 0 hv, hfr]
        have h01 : q 0 1 = false := by rw [hFU 0 0 hv, hfu]
        have h11 : q 1 1 = true := by rw [hTU 1 0 h10, htu]
        have h02 : q 0 2 = false := by rw [hFU 0 1 h01, hfu]
        have h20 : q 2 0 = false := by rw [hTR 1 0 h10, htr]
        exact absurd h11 (Bool.eq_false_iff.mp
          (h.lcont 2 0 2 1 (by omega) (by omega) (by omega) h02 h20))
    · rcases Bool.eq_false_or_eq_true (q af (bf + 1)) with hfu | hfu
      · -- (F,T,F,T) → path inconsistency
        exfalso
        rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
        · have h10 : q 1 0 = false := by rw [hTR 0 0 hv, htr]
          have h01 : q 0 1 = true := by rw [hTU 0 0 hv, htu]
          have h11a : q 1 1 = true := by rw [hFU 1 0 h10, hfu]
          have h11b : q 1 1 = false := by rw [hTR 0 1 h01, htr]
          rw [h11a] at h11b; exact absurd h11b (by decide)
        · have h10 : q 1 0 = false := by rw [hFR 0 0 hv, hfr]
          have h01 : q 0 1 = true := by rw [hFU 0 0 hv, hfu]
          have h11a : q 1 1 = true := by rw [hFU 1 0 h10, hfu]
          have h11b : q 1 1 = false := by rw [hTR 0 1 h01, htr]
          rw [h11a] at h11b; exact absurd h11b (by decide)
      · -- (F,T,F,F) → noNT
        rcases Bool.eq_false_or_eq_true (q 0 0) with hv | hv
        · right; right; left
          exact grid_ext q noNT hv
            (λ a heq => by
              cases hqa : q a 0
              · rw [hFR a 0 hqa, hfr]; rfl
              · rw [hTR a 0 hqa, htr]; rfl)
            (λ a b heq => by
              cases hqa : q a b
              · rw [hFU a b hqa, hfu]; exact (heq.symm.trans hqa).symm
              · rw [hTU a b hqa, htu]; exact (heq.symm.trans hqa).symm)
        · exact (var_not_all_false hv hfr hfu).elim

end NumberTreeGQ

-- ============================================================================
-- §10f GQ → NumberTreeGQ Bridge
-- ============================================================================

section NumberTreeBridge
open Classical Finset

/-- Decompose α into 4 cells based on two Boolean predicates (A, B).
    Each element x lands in cell (A x, B x). -/
private def cellEquiv (A B : α → Bool) :
    α ≃ Σ (b₁ : Bool) (b₂ : Bool), {x : α // A x == b₁ && B x == b₂} where
  toFun x := ⟨A x, B x, ⟨x, by simp⟩⟩
  invFun := fun ⟨_, _, ⟨x, _⟩⟩ => x
  left_inv _ := rfl
  right_inv := fun ⟨b₁, b₂, ⟨x, h⟩⟩ => by
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h₁, h₂⟩; subst h₁; subst h₂; rfl

/-- Build a cell-preserving bijection from matching 4-cell cardinalities. -/
private noncomputable def cellBijection [Fintype α] [DecidableEq α]
    (A₁ B₁ A₂ B₂ : α → Bool)
    (h_card : ∀ b₁ b₂, Fintype.card {x : α // A₁ x == b₁ && B₁ x == b₂} =
                         Fintype.card {x : α // A₂ x == b₁ && B₂ x == b₂}) :
    α ≃ α :=
  (cellEquiv A₂ B₂).trans
    ((Equiv.sigmaCongrRight fun b₁ => Equiv.sigmaCongrRight fun b₂ =>
        Fintype.equivOfCardEq (h_card b₁ b₂).symm).trans
      (cellEquiv A₁ B₁).symm)

/-- The cell bijection preserves both predicates pointwise. -/
private lemma cellBijection_spec [Fintype α] [DecidableEq α]
    (A₁ B₁ A₂ B₂ : α → Bool)
    (h_card : ∀ b₁ b₂, Fintype.card {x : α // A₁ x == b₁ && B₁ x == b₂} =
                         Fintype.card {x : α // A₂ x == b₁ && B₂ x == b₂})
    (x : α) :
    A₁ (cellBijection A₁ B₁ A₂ B₂ h_card x) = A₂ x ∧
    B₁ (cellBijection A₁ B₁ A₂ B₂ h_card x) = B₂ x := by
  unfold cellBijection
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, cellEquiv]
  have h := (Fintype.equivOfCardEq (h_card (A₂ x) (B₂ x)).symm ⟨x, by simp⟩).property
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- Bool complement partition: |{f}| + |{¬f}| = |α|. -/
private lemma bool_filter_partition [Fintype α] [DecidableEq α] (f : α → Bool) :
    (univ.filter fun x => f x).card + (univ.filter fun x => !(f x)).card =
    Fintype.card α := by
  have hunion : (univ.filter fun x => f x) ∪ (univ.filter fun x => !(f x)) = univ := by
    ext x; simp only [mem_union, mem_filter, mem_univ, true_and]
    cases f x <;> simp
  have hdisj : Disjoint (univ.filter fun x => f x) (univ.filter fun x => !(f x)) :=
    disjoint_filter.mpr fun x _ h1 h2 => by cases f x <;> simp_all
  rw [← card_union_of_disjoint hdisj, hunion, card_univ]

/-- |A| = |A∩B| + |A\B| for Bool predicates. -/
private lemma bool_filter_split [Fintype α] [DecidableEq α] (A B : α → Bool) :
    (univ.filter fun x => A x).card =
    (univ.filter fun x => A x && B x).card +
    (univ.filter fun x => A x && !(B x)).card := by
  have hunion : (univ.filter fun x => A x && B x) ∪ (univ.filter fun x => A x && !(B x)) =
                univ.filter fun x => A x := by
    ext x; simp only [mem_union, mem_filter, mem_univ, true_and]
    cases A x <;> cases B x <;> simp
  have hdisj : Disjoint (univ.filter fun x => A x && B x)
      (univ.filter fun x => A x && !(B x)) :=
    disjoint_filter.mpr fun x _ h1 h2 => by cases A x <;> cases B x <;> simp_all
  rw [← card_union_of_disjoint hdisj, hunion]

/-- Relate Fintype.card of a Bool-predicate subtype to Finset.filter card. -/
private lemma card_subtype_bool [Fintype α] (f : α → Bool) :
    Fintype.card {x : α // f x} = (univ.filter fun x => f x).card := by
  rw [Fintype.card_subtype]

/-- Lift a Bool predicate to a Prop predicate via `(· = true)`. -/
private abbrev liftP (f : α → Bool) : α → Prop := fun x => f x = true

/-- CONSERV + QUANT GQs agree on any two pairs (A, B) and (A', B') with
    matching `|A∩B|` and `|A\B|` cardinalities. The proof decomposes the
    domain into 4 cells via conservativity (collapsing B to A∧B),
    builds a cell-preserving bijection from `Fintype.equivOfCardEq`,
    then applies `QuantityInvariant`. -/
private theorem gq_depends_on_card [Fintype α] [DecidableEq α]
    (q : GQ α) (hCons : Conservative q) (hQ : QuantityInvariant q)
    (A B A' B' : α → Bool)
    (h_ab : (univ.filter (fun x => A x && B x)).card =
            (univ.filter (fun x => A' x && B' x)).card)
    (h_anb : (univ.filter (fun x => A x && !(B x))).card =
             (univ.filter (fun x => A' x && !(B' x))).card) :
    q (liftP A) (liftP B) ↔ q (liftP A') (liftP B') := by
  rw [hCons (liftP A) (liftP B), hCons (liftP A') (liftP B')]
  -- Cell simplification: relate each (b₁, b₂) cell to a simple filter
  have cell_TT (R S : α → Bool) :
      (univ.filter fun x => R x == true && (R x && S x) == true).card =
      (univ.filter fun x => R x && S x).card := by
    congr 1; ext x; simp only [mem_filter, mem_univ, true_and]
    cases R x <;> cases S x <;> simp
  have cell_TF (R S : α → Bool) :
      (univ.filter fun x => R x == true && (R x && S x) == false).card =
      (univ.filter fun x => R x && !(S x)).card := by
    congr 1; ext x; simp only [mem_filter, mem_univ, true_and]
    cases R x <;> cases S x <;> simp
  have cell_FT (R S : α → Bool) :
      (univ.filter fun x => R x == false && (R x && S x) == true).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x _; simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  have cell_FF (R S : α → Bool) :
      (univ.filter fun x => R x == false && (R x && S x) == false).card =
      (univ.filter fun x => !(R x)).card := by
    congr 1; ext x; simp only [mem_filter, mem_univ, true_and]
    cases R x <;> cases S x <;> simp
  -- Build 4-cell cardinality match
  have h_card : ∀ b₁ b₂,
      Fintype.card {x : α // A x == b₁ && (A x && B x) == b₂} =
      Fintype.card {x : α // A' x == b₁ && (A' x && B' x) == b₂} := by
    intro b₁ b₂
    rw [card_subtype_bool, card_subtype_bool]
    cases b₁ <;> cases b₂
    · rw [cell_FF, cell_FF]
      have hA : (univ.filter fun x => A x).card = (univ.filter fun x => A' x).card := by
        rw [bool_filter_split A B, bool_filter_split A' B', h_ab, h_anb]
      have p1 := bool_filter_partition A
      have p2 := bool_filter_partition A'
      omega
    · rw [cell_FT, cell_FT]
    · rw [cell_TF, cell_TF, h_anb]
    · rw [cell_TT, cell_TT, h_ab]
  let f := cellBijection A (fun x => A x && B x) A' (fun x => A' x && B' x) h_card
  -- Goal: q (liftP A) (fun x => liftP A x ∧ liftP B x) ↔
  --       q (liftP A') (fun x => liftP A' x ∧ liftP B' x).
  -- Reduce the conjoined scopes to the lifted Bool intersection, then
  -- apply QuantityInvariant via the cell bijection.
  have hAndA : (fun x => liftP A x ∧ liftP B x) = liftP (fun x => A x && B x) := by
    funext x; exact propext ⟨fun ⟨h1, h2⟩ => by simp [liftP, h1, h2],
      fun h => by simp [liftP, Bool.and_eq_true] at h; exact ⟨h.1, h.2⟩⟩
  have hAndA' : (fun x => liftP A' x ∧ liftP B' x) = liftP (fun x => A' x && B' x) := by
    funext x; exact propext ⟨fun ⟨h1, h2⟩ => by simp [liftP, h1, h2],
      fun h => by simp [liftP, Bool.and_eq_true] at h; exact ⟨h.1, h.2⟩⟩
  rw [hAndA, hAndA']
  exact hQ (liftP A) (liftP (fun x => A x && B x))
    (liftP A') (liftP (fun x => A' x && B' x)) f f.bijective
    (fun x => by
      have h := (cellBijection_spec _ _ _ _ h_card x).1
      show (A (f x) = true) ↔ (A' x = true); rw [h])
    (fun x => by
      have h := (cellBijection_spec _ _ _ _ h_card x).2
      show ((A (f x) && B (f x)) = true) ↔ ((A' x && B' x) = true); rw [h])

section ToNumberTree
open Classical

/-- Extract the number-tree representation of a CONSERV+QUANT quantifier.
    Under conservativity and quantity-invariance, Q(A,B) depends only on
    `|A ∩ B|` and `|A \ B|`. This definition picks a canonical witness
    pair for each (a,b) coordinate.

    For (a,b) realizable in the domain (a + b ≤ |α|), the value is
    determined by any witness; for unrealizable pairs, we default to false. -/
noncomputable def toNumberTree [Fintype α] (q : GQ α) : NumberTreeGQ :=
  λ a b =>
    if h : ∃ (A B : α → Bool),
      (Finset.univ.filter (λ x => A x && B x)).card = a ∧
      (Finset.univ.filter (λ x => A x && !(B x))).card = b
    then decide (q (liftP h.choose) (liftP h.choose_spec.choose))
    else false

/-- The number-tree representation faithfully reflects the GQ on
    realizable coordinates: for any A, B, the GQ holds iff the
    number-tree value at (|A∩B|, |A\B|) is `true`.

    Proof: A and B themselves witness the existential in `toNumberTree`,
    so the `dite` takes the positive branch. The chosen witness pair has
    matching `|A∩B|` and `|A\B|` cardinalities, so `gq_depends_on_card`
    (via cell-preserving bijection) gives the GQ-level Iff between
    `q A B` and `q A_chosen B_chosen`. -/
theorem toNumberTree_spec [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hQ : QuantityInvariant q) :
    ∀ (A B : α → Bool),
      q (liftP A) (liftP B) ↔
        toNumberTree q
          (Finset.univ.filter (λ x => A x && B x)).card
          (Finset.univ.filter (λ x => A x && !(B x))).card = true := by
  intro A B
  have hexists : ∃ (A' B' : α → Bool),
      (univ.filter (fun x => A' x && B' x)).card =
        (univ.filter (fun x => A x && B x)).card ∧
      (univ.filter (fun x => A' x && !(B' x))).card =
        (univ.filter (fun x => A x && !(B x))).card :=
    ⟨A, B, rfl, rfl⟩
  unfold toNumberTree
  rw [dif_pos hexists]
  have hspec := hexists.choose_spec.choose_spec
  have hIff := gq_depends_on_card q hCons hQ A B _ _ hspec.1.symm hspec.2.symm
  rw [hIff, decide_eq_true_iff]

end ToNumberTree

end NumberTreeBridge

-- ============================================================================
-- §11 Counting Quantifiers (§5.4)
-- ============================================================================

/-- Thm 5.4: On a finite set with n individuals, there are
    exactly 2^((n+1)(n+2)/2) conservative quantifiers (satisfying QUANT).
    The tree of numbers has (n+1)(n+2)/2 points at levels a + b ≤ n. -/
def conservativeQuantifierCount (n : Nat) : Nat :=
  2 ^ ((n + 1) * (n + 2) / 2)

#guard conservativeQuantifierCount 0 == 2
#guard conservativeQuantifierCount 1 == 8
#guard conservativeQuantifierCount 2 == 64
#guard conservativeQuantifierCount 3 == 1024
#guard conservativeQuantifierCount 4 == 32768


end Core.Quantification
