import Linglib.Studies.Cooper2023.Ch8
import Linglib.Studies.Cooper2023.Ch7
import Linglib.Semantics.Dynamic.CDRT.Basic
import Linglib.Studies.Chomsky1981
import Linglib.Data.Examples.Geach1962
import Linglib.Data.Examples.Kanazawa1994

/-!
# Cooper (2023) — TTR Underspecification [cooper-2023]

Connects TTR underspecification to anaphora data, drawing on
[kanazawa-1994], [groenendijk-stokhof-1991],
[muskens-1996], [sutton-2024], [chomsky-1981].

Connects TTR's localization (donkey anaphora) and binding theory
(reflexivization, anaphoric resolution) from
`Semantics.TypeTheoretic.Underspecification` to the donkey rows in
`Data/Examples/Geach1962.json` / `Kanazawa1994.json` and the binding
paradigm in `Studies/Chomsky1981.lean`.

Per-datum verification: each theorem verifies one data point
against TTR predictions.

§§ 4–5 establish the truth-conditional bridge from CDRT
(Dynamic/CDRT/Basic.lean, [muskens-1996]) to TTR for the existential
and donkey-implication core, and the divergence under negation: TTR and
CDRT agree on truth conditions but differ on anaphoric potential
(state-threading vs. type-structure). This is the formal correspondence
surveyed in [sutton-2024].

-/

namespace Cooper2023

open Semantics.TypeTheoretic
open Cooper2023Ch8
open Chomsky1981

-- ============================================================================
-- Bridge: TTR donkey predictions -> Data/Examples donkey rows
-- ============================================================================

/-! ### Per-datum verification: TTR predictions match empirical data

Connect the TTR localization analysis to the donkey rows in
`Data/Examples/Geach1962.json` and `Kanazawa1994.json`. Each theorem
verifies one data point: the row records a reading as available, and
TTR produces a witness for that reading.

Changing a Ppty (e.g., making `beats` asymmetric) will break exactly
the theorems whose empirical predictions depend on it. -/

/-- Geach donkey: weak reading available -- TTR predicts checkmark.
    The row records the weak/existential reading and TTR produces a weak
    (localize) witness for both farmers in the scenario. -/
theorem geach_weak_available :
    Geach1962.Examples.donkey_classic.readings.contains
      ("weak/existential", .acceptable) = true ∧
    Nonempty (ℒ farmerOwnsBeatsDonkey .farmer1) ∧
    Nonempty (ℒ farmerOwnsBeatsDonkey .farmer2) :=
  ⟨rfl, ⟨farmer1WeakDonkey⟩, ⟨farmer2WeakDonkey⟩⟩

/-- Geach donkey: bound reading — TTR confirms the pronoun depends on
    the indefinite via parametric background (the donkey is the Bg). -/
theorem geach_bound_reading :
    Geach1962.Examples.donkey_classic.readings.contains
      ("bound", .acceptable) = true ∧
    farmerOwnsBeatsDonkey.Bg = DonkeyBg :=
  ⟨rfl, rfl⟩

/-- Strong dominant: TTR records the weak reading is available (ℒ produces
    a witness). The conditional-strong reading via the formaliser-invented
    `localizeConditional` was deleted in 0.230.564 (per audit: Cooper's own
    strong-donkey mechanism is 𝔓^∀ over an indexed background, not a
    separate conditional gate; see TODO note in `Cooper2023Ch8.lean`
    DonkeyAnaphora section). -/
theorem strongDominant_readings_available :
    Kanazawa1994.Examples.strong_dominant.readings.contains
      ("strong/universal", .acceptable) = true ∧
    Kanazawa1994.Examples.strong_dominant.readings.contains
      ("weak/existential", .acceptable) = true ∧
    Nonempty (ℒ farmerOwnsBeatsDonkey .farmer1) :=
  ⟨rfl, rfl, ⟨farmer1WeakDonkey⟩⟩

-- ============================================================================
-- Bridge: TTR binding -> Chomsky1981 binding paradigm (bridge theorem 3)
-- ============================================================================

/-! ### Per-datum verification: binding predictions match coreference data

Connect TTR's reflexivization and anaphoric resolution to the binding
paradigm in `Studies/Chomsky1981.lean`.

[cooper-2023] Ch8 section 8.3 gives a type-theoretic account of [chomsky-1981]'s binding conditions:
- **Condition A** (reflexives must be locally bound): reflexivization forces argument identity
- **Condition B** (pronouns must be locally free): anaphoric resolution with disjoint reference
- **Complementary distribution**: reflexivization vs anaphoric resolution for the same position

Each theorem verifies one empirical pattern from `Studies/Chomsky1981.lean`.
Changing `reflexivize` or `anaphoricResolve` will break these bridges. -/

/-- TTR's reflexivization predicts Binding Condition A:
    reflexives require a local antecedent because reflexivization forces argument
    identity within the local clause.
    Cooper Ch8, eq (84) + (88): reflexivization at VP level binds reflexive to subject.
    Matches `Chomsky1981.reflexivePattern`. -/
theorem reflexive_predicts_condA :
    reflexivePattern.requiresAntecedent = true ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- TTR predicts Binding Condition B:
    pronouns allow disjoint reference via anaphoric resolution with a
    constant function (the assignment provides the referent from
    non-local context). Cooper Ch8, eq (28).
    Matches `Chomsky1981.pronounPattern`. -/
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
    Matches `Chomsky1981.complementaryDistributionData`. -/
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
    3. The empirical coreference patterns match: [chomsky-1981]
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

/-! CDRT (Dynamic/CDRT/Basic.lean, [muskens-1996]) and TTR
(TypeTheoretic/, [cooper-2023]) handle overlapping anaphora
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

open Semantics.Dynamic.CDRT (DProp State SProp)
open Semantics.Dynamic.Core.DynProp (closure dseq test dneg dimpl)
open Semantics.TypeTheoretic (Ppty PPpty Parametric IsTrue IsFalse propT)
open Cooper2023Ch7 (purify purifyUniv)

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
theorem exists_equiv (n : Nat) (P : E → Prop) (i : State E) :
    DProp.true_at (cdrt_exists n P) i ↔ Nonempty (ttr_exists P) := by
  simp only [DProp.true_at, Semantics.Dynamic.Core.DynProp.closure, cdrt_exists, DProp.seq, dseq, Relation.Comp, DProp.new,
    DProp.ofStatic, test, ttr_exists]
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
theorem donkey_equiv (n : Nat) (P Q : E → Prop) (i : State E) :
    DProp.true_at (cdrt_donkey n P Q) i ↔ Nonempty (ttr_donkey P Q) := by
  simp only [DProp.true_at, Semantics.Dynamic.Core.DynProp.closure, cdrt_donkey, DProp.impl, dimpl, DProp.seq, dseq, Relation.Comp,
    DProp.new, DProp.ofStatic, test, ttr_donkey]
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
    (farmer donkey_ : E → Prop) (owns : E → E → Prop) (i k : State E) :
    (DProp.new 0 ;; DProp.ofStatic (λ r => farmer (r 0)) ;;
     DProp.new 1 ;; DProp.ofStatic (λ r => donkey_ (r 1) ∧ owns (r 0) (r 1))) i k ↔
    ∃ x y, k = (λ m => if m = 1 then y else if m = 0 then x else i m) ∧
      farmer x ∧ donkey_ y ∧ owns x y := by
  simp only [DProp.seq, dseq, Relation.Comp, DProp.new, DProp.ofStatic, test]
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
    (i : State E) :
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
(`Semantics/Dynamic/Bilateral/Defs.lean`) is a third
approach — bilateral DNE is structural at the *state* level (swap is
involutive), distinct from TTR's structural-at-the-*type* level. The
three are surveyed in `Dynamic/Update.lean`'s "three
incompatible DNE solutions" table. -/

/-- In CDRT, negation destroys anaphoric potential. After `¬φ`, the
output register is unchanged from input — any drefs introduced by φ
are inaccessible. -/
theorem neg_destroys_dref {φ : DProp E} (i o : State E)
    (h : DProp.neg φ i o) : o = i :=
  DProp.neg_output h

/-- Double negation preserves truth but not drefs. `¬¬(∃x.P(x))` has
the same truth conditions as `∃x.P(x)`, but the output register is
the *input* register (no binding). -/
theorem dne_same_truth (n : Nat) (P : E → Prop) (i : State E) :
    DProp.true_at (DProp.neg (DProp.neg (cdrt_exists n P))) i ↔
    DProp.true_at (cdrt_exists n P) i := by
  simp only [DProp.true_at, Semantics.Dynamic.Core.DynProp.closure, DProp.neg, test, dneg]
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

private def initReg : State Ent := λ _ => .john

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
