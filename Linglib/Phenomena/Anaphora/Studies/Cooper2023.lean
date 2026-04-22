import Linglib.Theories.Semantics.TypeTheoretic.Underspecification
import Linglib.Theories.Semantics.TypeTheoretic.Quantification
import Linglib.Theories.Semantics.Dynamic.CDRT.Basic
import Linglib.Phenomena.Anaphora.DonkeyAnaphora
import Linglib.Phenomena.Anaphora.Coreference

/-!
# TTR Underspecification -> Anaphora Data
@cite{chomsky-1981} @cite{cooper-2023} @cite{kanazawa-1994}
@cite{groenendijk-stokhof-1991} @cite{muskens-1996} @cite{sutton-2024}

Connects TTR's localization (donkey anaphora) and binding theory
(reflexivization, anaphoric resolution) from
`Theories.Semantics.TypeTheoretic.Underspecification` to the empirical
data in `Phenomena.Anaphora.DonkeyAnaphora` and
`Phenomena.Anaphora.Coreference`.

Per-datum verification: each theorem verifies one data point from the
Phenomena files against TTR predictions.

§§ 4–5 establish the truth-conditional bridge from CDRT
(Dynamic/CDRT/Basic.lean, @cite{muskens-1996}) to TTR for the existential
and donkey-implication core, and the divergence under negation: TTR and
CDRT agree on truth conditions but differ on anaphoric potential
(state-threading vs. type-structure). This is the formal correspondence
surveyed in @cite{sutton-2024}.

-/

namespace Cooper2023

open Semantics.TypeTheoretic
open Phenomena.Anaphora.DonkeyAnaphora
open Phenomena.Anaphora.Coreference

-- ============================================================================
-- Bridge: TTR donkey predictions -> Phenomena/Anaphora/DonkeyAnaphora
-- ============================================================================

/-! ### Per-datum verification: TTR predictions match empirical data

Connect the TTR localization analysis to the theory-neutral donkey
anaphora data in `Phenomena.Anaphora.DonkeyAnaphora`. Each theorem
verifies one data point: the empirical datum records a reading as
available, and TTR produces a witness for that reading.

Changing a Ppty (e.g., making `beats` asymmetric) will break exactly
the theorems whose empirical predictions depend on it. -/

/-- Geach donkey: weak reading available -- TTR predicts checkmark.
    `geachDonkey.weakReading = true` and TTR produces a weak (localize) witness
    for both farmers in the scenario. -/
theorem geach_weak_available :
    geachDonkey.weakReading = true ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer2) :=
  ⟨rfl, ⟨farmer1_weak_donkey⟩, ⟨farmer2_weak_donkey⟩⟩

/-- Geach donkey: strong reading available -- TTR predicts checkmark.
    `geachDonkey.strongReading = true` and TTR produces a conditional
    strong witness for both farmers. -/
theorem geach_strong_available :
    geachDonkey.strongReading = true ∧
    Nonempty (strongDonkeyConditional .farmer1) ∧
    Nonempty (strongDonkeyConditional .farmer2) :=
  ⟨rfl, ⟨farmer1_strong_conditional⟩, ⟨farmer2_strong_conditional⟩⟩

/-- Geach donkey: bound reading -- TTR confirms the pronoun depends on
    the indefinite via parametric background (the donkey is the Bg). -/
theorem geach_bound_reading :
    geachDonkey.boundReading = true ∧
    farmerOwnsBeatsDonkey.Bg = DonkeyBg :=
  ⟨rfl, rfl⟩

/-- Strong dominant: both readings TTR-available (consistent with
    `strongDominant` recording both as available with strong preferred). -/
theorem strongDominant_readings_available :
    strongDominant.strongAvailable = true ∧
    strongDominant.weakAvailable = true ∧
    Nonempty (strongDonkeyConditional .farmer1) ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) :=
  ⟨rfl, rfl, ⟨farmer1_strong_conditional⟩, ⟨farmer1_weak_donkey⟩⟩

-- ============================================================================
-- Bridge: TTR binding -> Phenomena/Anaphora/Coreference (bridge theorem 3)
-- ============================================================================

/-! ### Per-datum verification: binding predictions match coreference data

Connect TTR's reflexivization and anaphoric resolution to the theory-neutral binding
data in `Phenomena.Anaphora.Coreference`.

@cite{cooper-2023} Ch8 section 8.3 gives a type-theoretic account of @cite{chomsky-1981}'s binding conditions:
- **Condition A** (reflexives must be locally bound): reflexivization forces argument identity
- **Condition B** (pronouns must be locally free): anaphoric resolution with disjoint reference
- **Complementary distribution**: reflexivization vs anaphoric resolution for the same position

Each theorem verifies one empirical pattern from `Coreference.lean`.
Changing `reflexivize` or `anaphoricResolve` will break these bridges. -/

/-- TTR's reflexivization predicts Binding Condition A:
    reflexives require a local antecedent because reflexivization forces argument
    identity within the local clause.
    Cooper Ch8, eq (84) + (88): reflexivization at VP level binds reflexive to subject.
    Matches `reflexivePattern` from Phenomena. -/
theorem reflexive_predicts_condA :
    reflexivePattern.requiresAntecedent = true ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- TTR predicts Binding Condition B:
    pronouns allow disjoint reference via anaphoric resolution with a
    constant function (the assignment provides the referent from
    non-local context). Cooper Ch8, eq (28).
    Matches `pronounPattern` from Phenomena. -/
theorem pronoun_predicts_condB :
    pronounPattern.requiresAntecedent = false ∧
    pronounPattern.antecedentDomain = some .nonlocal ∧
    (∀ (y x : BindInd),
      anaphoricResolve likeParam (fun _ => y) x = like₈ x y) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Complementary distribution: reflexive and pronoun are predicted
    by different TTR mechanisms (reflexivization vs anaphoric resolution).
    Cooper Ch8, eqs (67)-(73): "Sam likes him" is NOT appropriate for
    "Sam likes himself" -- reflexivization must be used instead.
    Matches `complementaryDistributionData` from Phenomena. -/
theorem complementary_distribution_predicted :
    reflexivePattern.anaphorType = .reflexive ∧
    pronounPattern.anaphorType = .pronoun ∧
    Nonempty (ℜ like₈ .sam) ∧
    Nonempty (anaphoricResolve likeParam (fun _ => BindInd.bill) .sam) :=
  ⟨rfl, rfl, ⟨samLikesHimself⟩, ⟨samLikesBill⟩⟩

/-- The main bridge theorem (bridge theorem 3):
    TTR's reflexivization predicts the binding data.

    1. Reflexivization forces local coreference (Condition A): Cooper eq (84)
    2. Anaphoric resolution allows disjoint reference (Condition B): Cooper eq (28)
    3. The empirical coreference patterns match: @cite{chomsky-1981}
    4. Reflexivization = anaphoricResolve with id: reflexivization is a special case -/
theorem reflexive_predicts_binding :
    -- Reflexivization forces identity (Condition A)
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) ∧
    -- Pronoun resolution allows distinct arguments (Condition B)
    (∀ (y x : BindInd),
      anaphoricResolve likeParam (fun _ => y) x = like₈ x y) ∧
    -- Reflexivization is a special case of anaphoric resolution
    (anaphoricResolve likeParam id = ℜ like₈) ∧
    -- Matches empirical coreference patterns
    reflexivePattern.requiresAntecedent = true ∧
    pronounPattern.requiresAntecedent = false ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    pronounPattern.antecedentDomain = some .nonlocal :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Truth-Conditional Bridge: CDRT ↔ TTR
-- ════════════════════════════════════════════════════════════════

/-! CDRT (Dynamic/CDRT/Basic.lean, @cite{muskens-1996}) and TTR
(TypeTheoretic/, @cite{cooper-2023}) handle overlapping anaphora
phenomena — discourse referents, donkey anaphora, cross-sentential
binding — with no shared infrastructure. This section proves they
agree on truth conditions for the existential and donkey cores, and
identifies where they diverge (§ 5).

| Dynamic (CDRT)          | Type-Theoretic (TTR)     | Classical          |
|-------------------------|--------------------------|--------------------|
| `DProp.ofStatic p`      | `propT (p i)`            | `p i`              |
| `DProp.new n; test P` | `Σ (x : E), P x`        | `∃ x, P x`        |
| `DProp.impl (new;P) Q` | `Π (x : E), P x → Q x`  | `∀ x, P x → Q x`  |

The first column is state-threading (assignments as side effects);
the second is type-dependency (witnesses as structure). Both reduce
to the same classical truth conditions.
-/

open Semantics.Dynamic.CDRT (DProp Register SProp)
open Semantics.TypeTheoretic (Ppty PPpty Parametric IsTrue IsFalse
  propT purify purifyUniv)

variable {E : Type}

/-- CDRT existential: introduce dref n, test P on r(n). -/
def cdrt_exists (n : Nat) (P : E → Prop) : DProp E :=
  DProp.new n ;; DProp.ofStatic (λ r => P (r n))

/-- TTR existential: Σ-type with entity witness. This is `purify` applied
to a parametric property with background `E`; the result doesn't depend
on the input, so we state it directly. -/
def ttr_exists (P : E → Prop) : Type := (x : E) × propT (P x)

/-- **Equivalence 1**: CDRT dref introduction and TTR Σ-type have
the same truth conditions. Both reduce to `∃ x, P x`. -/
theorem exists_equiv (n : Nat) (P : E → Prop) (i : Register E) :
    DProp.true_at (cdrt_exists n P) i ↔ Nonempty (ttr_exists P) := by
  simp only [DProp.true_at, cdrt_exists, DProp.seq, DProp.new, DProp.ofStatic, ttr_exists]
  constructor
  · rintro ⟨o, k, ⟨e, rfl⟩, rfl, hp⟩
    exact ⟨⟨e, PLift.up (by simpa using hp)⟩⟩
  · rintro ⟨⟨x, ⟨hx⟩⟩⟩
    exact ⟨_, _, ⟨x, rfl⟩, rfl, by simpa⟩

/-- Both reduce to classical ∃. -/
theorem exists_classical (P : E → Prop) :
    Nonempty (ttr_exists P) ↔ ∃ x : E, P x :=
  ⟨λ ⟨⟨x, ⟨hx⟩⟩⟩ => ⟨x, hx⟩, λ ⟨x, hx⟩ => ⟨⟨x, PLift.up hx⟩⟩⟩

/-- CDRT donkey: `impl(new n; test P, test Q)`. "For every way of
extending the register with a P-entity at n, Q holds of that entity." -/
def cdrt_donkey (n : Nat) (P Q : E → Prop) : DProp E :=
  DProp.impl
    (DProp.new n ;; DProp.ofStatic (λ r => P (r n)))
    (DProp.ofStatic (λ r => Q (r n)))

/-- TTR donkey: Π-type over witnesses. "For every P-witness, Q holds."
This is `purifyUniv` on the parametric property with background
`{x : E // P x}`. -/
def ttr_donkey (P Q : E → Prop) : Type :=
  (x : E) → P x → propT (Q x)

/-- **Equivalence 2**: CDRT donkey implication and TTR Π-type have
the same truth conditions. Both reduce to `∀ x, P x → Q x`. -/
theorem donkey_equiv (n : Nat) (P Q : E → Prop) (i : Register E) :
    DProp.true_at (cdrt_donkey n P Q) i ↔ Nonempty (ttr_donkey P Q) := by
  simp only [DProp.true_at, cdrt_donkey, DProp.impl, DProp.seq, DProp.new,
    DProp.ofStatic, ttr_donkey]
  constructor
  · rintro ⟨o, rfl, hall⟩
    refine ⟨λ x hpx => PLift.up ?_⟩
    have := hall (λ m => if m = n then x else i m) ⟨_, ⟨x, rfl⟩, rfl, by simpa⟩
    obtain ⟨m, rfl, hq⟩ := this
    simpa using hq
  · rintro ⟨f⟩
    refine ⟨i, rfl, λ k ⟨j, ⟨e, hj⟩, hjk, hp⟩ => ?_⟩
    subst hj; subst hjk
    simp at hp
    have ⟨hq⟩ := f e hp
    exact ⟨_, rfl, by simpa⟩

/-- Both reduce to classical ∀→. -/
theorem donkey_classical (P Q : E → Prop) :
    Nonempty (ttr_donkey P Q) ↔ ∀ x : E, P x → Q x :=
  ⟨λ ⟨f⟩ x hx => (f x hx).down, λ h => ⟨λ x hx => PLift.up (h x hx)⟩⟩

/-! ### Two-variable donkey

"Every farmer who owns a donkey beats it." -/

def cdrt_full_donkey (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) :
    DProp E :=
  DProp.impl
    (DProp.new 0 ;; DProp.ofStatic (λ r => farmer (r 0)) ;;
     DProp.new 1 ;; DProp.ofStatic (λ r => donkey_ (r 1) ∧ owns (r 0) (r 1)))
    (DProp.ofStatic (λ r => beats (r 0) (r 1)))

def ttr_full_donkey (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) :
    Type :=
  (x : E) → farmer x → (y : E) → donkey_ y → owns x y → propT (beats x y)

private theorem donkey_antecedent_iff
    (farmer donkey_ : E → Prop) (owns : E → E → Prop) (i k : Register E) :
    (DProp.new 0 ;; DProp.ofStatic (λ r => farmer (r 0)) ;;
     DProp.new 1 ;; DProp.ofStatic (λ r => donkey_ (r 1) ∧ owns (r 0) (r 1))) i k ↔
    ∃ x y, k = (λ m => if m = 1 then y else if m = 0 then x else i m) ∧
      farmer x ∧ donkey_ y ∧ owns x y := by
  simp only [DProp.seq, DProp.new, DProp.ofStatic]
  constructor
  · rintro ⟨k₃, ⟨k₂, ⟨k₁, ⟨e₀, rfl⟩, rfl, hf⟩, ⟨e₁, rfl⟩⟩, rfl, hd, ho⟩
    exact ⟨e₀, e₁, rfl, by simpa, by simpa, by simpa⟩
  · rintro ⟨x, y, rfl, hf, hd, ho⟩
    exact ⟨_, ⟨_, ⟨_, ⟨x, rfl⟩, rfl, by simpa⟩, ⟨y, rfl⟩⟩, rfl,
      by simpa, by simp [show (0 : ℕ) ≠ 1 from by omega]; exact ho⟩

/-- **Equivalence 3**: The full donkey sentence has the same truth
conditions in CDRT and TTR. -/
theorem full_donkey_equiv
    (farmer donkey_ : E → Prop) (owns beats : E → E → Prop)
    (i : Register E) :
    DProp.true_at (cdrt_full_donkey farmer donkey_ owns beats) i ↔
    Nonempty (ttr_full_donkey farmer donkey_ owns beats) := by
  simp only [cdrt_full_donkey]
  rw [DProp.impl_true_at]
  constructor
  · intro hall
    refine ⟨λ x hf y hd ho => PLift.up ?_⟩
    let k := λ m => if m = 1 then y else if m = 0 then x else i m
    have hk := (donkey_antecedent_iff farmer donkey_ owns i k).mpr ⟨x, y, rfl, hf, hd, ho⟩
    have := hall k hk
    rw [DProp.ofStatic_true_at] at this
    exact this
  · rintro ⟨f⟩
    intro k hk
    rw [donkey_antecedent_iff] at hk
    obtain ⟨x, y, rfl, hf, hd, ho⟩ := hk
    rw [DProp.ofStatic_true_at]
    simp [show (0 : ℕ) ≠ 1 from by omega]
    exact (f x hf y hd ho).down

/-! ### Connection to TTR's `purify` / `purifyUniv` -/

/-- The parametric property whose purification is `ttr_exists P`. -/
def ttr_exists_as_pppty (P : E → Prop) : PPpty E :=
  ⟨E, λ x _ => propT (P x)⟩

/-- `purify` of the existential parametric property is definitionally `ttr_exists`. -/
theorem purify_exists_eq (P : E → Prop) (a : E) :
    purify (ttr_exists_as_pppty P) a = ttr_exists P := rfl

/-- The parametric property whose universal purification is `ttr_donkey`. -/
def ttr_donkey_as_pppty (P Q : E → Prop) : PPpty E :=
  ⟨{x : E // P x}, λ ⟨x, _⟩ _ => propT (Q x)⟩

/-- `purifyUniv` of the donkey parametric property is inhabited iff the
donkey universal holds. -/
theorem purifyUniv_donkey_iff (P Q : E → Prop) (a : E) :
    Nonempty (purifyUniv (ttr_donkey_as_pppty P Q) a) ↔
    ∀ x : E, P x → Q x :=
  ⟨λ ⟨f⟩ x hx => (f ⟨x, hx⟩).down,
   λ h => ⟨λ ⟨x, hx⟩ => PLift.up (h x hx)⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Divergence: Anaphoric Potential under Negation
-- ════════════════════════════════════════════════════════════════

/-! The systems agree on truth conditions but differ on **discourse
effect**. CDRT tracks anaphoric potential via the *output register*:
after processing φ, the output register determines what drefs are
available for subsequent sentences.

- `new n; test P` outputs a register with `n` bound → dref available
- `neg (new n; test P)` outputs `i` unchanged → dref lost

TTR tracks anaphoric potential via *type structure*: the Σ-type
`(x : E) × P x` makes `x` available as a projection, regardless of
how many negations wrap it.

This is the architectural difference: CDRT uses *state* for binding;
TTR uses *structure*. The bilateral DNE strategy
(`Theories/Semantics/Dynamic/Bilateral/Basic.lean`) is a third
approach — bilateral DNE is structural at the *state* level (swap is
involutive), distinct from TTR's structural-at-the-*type* level. The
three are surveyed in `Dynamic/Core/DynProp.lean`'s "three
incompatible DNE solutions" table. -/

/-- In CDRT, negation destroys anaphoric potential. After `¬φ`, the
output register is unchanged from input — any drefs introduced by φ
are inaccessible. -/
theorem neg_destroys_dref {φ : DProp E} (i o : Register E)
    (h : DProp.neg φ i o) : o = i :=
  DProp.neg_output h

/-- Double negation preserves truth but not drefs. `¬¬(∃x.P(x))` has
the same truth conditions as `∃x.P(x)`, but the output register is
the *input* register (no binding). -/
theorem dne_same_truth (n : Nat) (P : E → Prop) (i : Register E) :
    DProp.true_at (DProp.neg (DProp.neg (cdrt_exists n P))) i ↔
    DProp.true_at (cdrt_exists n P) i := by
  simp only [DProp.true_at, DProp.neg]
  constructor
  · rintro ⟨_, rfl, h⟩
    exact Classical.byContradiction (λ hno => h ⟨i, rfl, hno⟩)
  · rintro h
    exact ⟨i, rfl, λ ⟨_, rfl, hno⟩ => hno h⟩

/-- In TTR there is no analogous destruction. The Σ-type `(x : E) × P x`
carries its witness structurally; the projection `Sigma.fst` is always
available, regardless of logical context. -/
theorem ttr_witness_survives (P : E → Prop) (w : ttr_exists P) :
    ∃ x : E, P x :=
  ⟨w.1, w.2.down⟩

/-! ### Concrete two-variable donkey verification -/

section ConcreteModel

inductive Ent where | john | bill | fido deriving DecidableEq

private def farmerP : Ent → Prop
  | .john => True | .bill => True | .fido => False

private def donkeyP : Ent → Prop
  | .fido => True | _ => False

private def ownsP : Ent → Ent → Prop
  | .john, .fido => True | _, _ => False

private def beatsP : Ent → Ent → Prop
  | .john, .fido => True | _, _ => False

private def initReg : Register Ent := λ _ => .john

/-- CDRT donkey sentence is true on this model. -/
theorem cdrt_donkey_concrete :
    DProp.true_at (cdrt_full_donkey farmerP donkeyP ownsP beatsP) initReg := by
  rw [full_donkey_equiv]
  exact ⟨λ x hf y hd ho => PLift.up (by
    cases x <;> cases y <;> simp_all [farmerP, donkeyP, ownsP, beatsP])⟩

/-- TTR donkey sentence is true on this model. -/
theorem ttr_donkey_concrete : Nonempty (ttr_full_donkey farmerP donkeyP ownsP beatsP) :=
  ⟨λ x hf y hd ho => PLift.up (by
    cases x <;> cases y <;> simp_all [farmerP, donkeyP, ownsP, beatsP])⟩

/-- The two concrete results agree (by the equivalence theorem). -/
theorem concrete_agreement :
    DProp.true_at (cdrt_full_donkey farmerP donkeyP ownsP beatsP) initReg ↔
    Nonempty (ttr_full_donkey farmerP donkeyP ownsP beatsP) :=
  full_donkey_equiv farmerP donkeyP ownsP beatsP initReg

end ConcreteModel

end Cooper2023
