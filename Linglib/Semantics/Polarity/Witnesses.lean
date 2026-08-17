import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Polarity.Strength
import Linglib.Logic.Natural.Soundness
import Linglib.Logic.Natural.StrawsonSoundness
import Linglib.Core.Order.AntiAdditive
import Linglib.Semantics.Quantification.Signatures
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting

/-!
# Model witnesses for the licensing-context table

Each witnessed row of `LicensingContext.properties` carries a model operator
realizing its signatures: the classical row via `Signature.SoundFor`,
the Strawson row via `Signature.StrawsonSoundFor`. This converts the
table's `strawsonSignature`/`classicalSignature` annotations into derived
facts about denotations — the licensing analogue of the
derive-don't-stipulate rule.

Coverage is incremental (`contextWitness?` is `Option`-valued): the
witnessed rows are those whose operators exist in the zoo — negation
(complementation), the quantifier rows (`every_sem`/`no_sem`/`few_sem` sections,
`atMost2_student`), conditional antecedents (`condNecessity`), and the
four Strawson-only rows (`onlyFull`, `sorryFull`, `superlativeAssert`,
`sinceFull`). The `none` rows await operators (*without*, *deny*,
*doubt*, *before*, *too…to*, the comparatives) or concern rows whose
content is the licensing mechanism rather than the signature (the
FC/`mono` rows, questions).

Each witness carries a `strength` certificate for its classical row
(`DEStrength.HoldsFor`, from `Semantics/Polarity/Strength.lean`), and
`ContextWitness.holdsFor_of_licenses` grounds the keystone: at a
witnessed presupposition-free row, strength-matched licensing means the
operator really holds the strength the item requires.
-/

namespace Polarity

open NaturalLogic
open Quantification
open Entailment

/-- A model-theoretic witness for a licensing-context row: an operator
(with its definedness/presupposition function) realizing the row's
Strawson signature, and its classical signature when one exists. -/
structure ContextWitness (c : LicensingContext) where
  {W : Type*}
  {β : Type*}
  /-- The context function. -/
  f : Set W → β
  /-- Definedness: where the argument's presupposition is satisfied. -/
  defined : Set W → β
  [latticeβ : Lattice β]
  [boundedβ : BoundedOrder β]
  /-- The Strawson row is Strawson-sound for `f`. -/
  strawson :
    Signature.StrawsonSoundFor c.properties.strawsonSignature
      f defined
  /-- The classical row, when present, is classically sound for `f`. -/
  classical :
    ∀ σ ∈ c.properties.classicalSignature, Signature.SoundFor σ f
  /-- The classical row's Zwarts strength holds semantically of `f`
      (vacuous at Strawson-only rows). -/
  strength :
    ∀ σ ∈ c.properties.classicalSignature, ∀ s ∈ σ.toDEStrength,
      s.HoldsFor f

private theorem soundFor_of_mem_some {W : Type*} {β : Type*} [Lattice β]
    [BoundedOrder β] {f : Set W → β} {σ₀ : Signature}
    (hf : Signature.SoundFor σ₀ f) :
    ∀ σ ∈ (some σ₀ : Option Signature), Signature.SoundFor σ f := by
  intro σ hσ
  rw [Option.mem_def] at hσ
  injection hσ with h
  exact h ▸ hf

private theorem soundFor_of_mem_none {W : Type*} {β : Type*} [Lattice β]
    [BoundedOrder β] {f : Set W → β} :
    ∀ σ ∈ (none : Option Signature), Signature.SoundFor σ f := by
  intro σ hσ
  rw [Option.mem_def] at hσ
  exact absurd hσ (by simp)

private theorem strength_of_mem_some {W : Type*} {β : Type*} [Lattice β]
    {f : Set W → β} {σ₀ : Signature} {s₀ : DEStrength}
    (hσ : σ₀.toDEStrength = some s₀) (hf : s₀.HoldsFor f) :
    ∀ σ ∈ (some σ₀ : Option Signature), ∀ s ∈ σ.toDEStrength,
      s.HoldsFor f := by
  intro σ hσ' s hs
  rw [Option.mem_def] at hσ'
  injection hσ' with h
  subst h
  rw [Option.mem_def, hσ] at hs
  injection hs with h'
  exact h' ▸ hf

private theorem strength_of_mem_none {W : Type*} {β : Type*} [Lattice β]
    {f : Set W → β} :
    ∀ σ ∈ (none : Option Signature), ∀ s ∈ σ.toDEStrength,
      s.HoldsFor f := by
  intro σ hσ
  rw [Option.mem_def] at hσ
  exact absurd hσ (by simp)

/-! ### The at-most operator

The model operator for the `.atMost` row: antitone in scope but not
anti-additive — the strictness witness separating weak DE from
anti-additivity. -/

/-- "At most n A's are B" - true if at most n worlds satisfy both.
    Uses an existential over a sublist witness so the def is decidable
    only when the predicates are decidable, but stays in `Prop`. -/
def atMost (n : Nat) (restr scope : Set (Fin 4)) : Prop :=
  ∀ ws : List (Fin 4), ws.Nodup →
    (∀ w ∈ ws, restr w ∧ scope w) →
    ws.length ≤ n

/-- Monotonicity: if `p ⊆ q` (entailment) and `q` has at most `n` witnesses,
    so does `p`. -/
theorem atMost_mono (n : Nat) (restr p q : Set (Fin 4))
    (hpq : ∀ w, p w → q w) (h : atMost n restr q) :
    atMost n restr p := by
  intro ws hnd hall
  apply h ws hnd
  intro w hw
  exact ⟨(hall w hw).1, hpq w (hall w hw).2⟩

/-- "At most 2 students ___" with fixed restrictor. -/
def atMost2_student : Set (Fin 4) → Set (Fin 4) :=
  λ scope => λ _ => atMost 2 {0, 1} scope

/-- "At most n" is antitone in scope. -/
theorem atMost_antitone_scope : Antitone atMost2_student := by
  intro p q hpq _w h
  exact atMost_mono 2 {0, 1} p q (fun _ hp => hpq hp) h

/-- "At most 1 student ___" with fixed restrictor. -/
def atMost1_student : Set (Fin 4) → Set (Fin 4) :=
  λ scope => λ _ => atMost 1 {0, 1} scope

/-- "At most 1" is still antitone. -/
theorem atMost1_antitone_scope : Antitone atMost1_student := by
  intro p q hpq _w h
  exact atMost_mono 1 {0, 1} p q (fun _ hp => hpq hp) h

/-- "At most n" is not anti-additive (counterexample): the strictness
witness for DE ⊊ anti-additive. -/
theorem atMost_not_antiAdditive :
    ¬IsAntiAdditive atMost1_student := by
  intro hAA
  have h := isAntiAdditive_iff_mem.mp hAA
  let qProp : Set (Fin 4) := λ w => w = 1
  let p0 : Set (Fin 4) := {0}
  have key : atMost1_student (p0 ∪ qProp) 0 ↔
             atMost1_student p0 0 ∧ atMost1_student qProp 0 :=
    h p0 qProp 0
  -- p0 has just w0 as a witness; ≤ 1 ✓
  have hp : atMost1_student p0 0 := by
    intro ws hnd hall
    -- Every element of ws satisfies p01 ∧ p0, hence equals w0
    have hall_w0 : ∀ w ∈ ws, w = 0 := by
      intro w hw
      have := (hall w hw).2
      exact this
    -- A nodup list whose every element is w0 has length ≤ 1
    rcases ws with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = 0 := hall_w0 a (List.mem_cons_self ..)
        have hb : b = 0 := hall_w0 b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have : a ≠ b := List.ne_of_not_mem_cons (List.Nodup.notMem hnd)
        exact this (ha.trans hb.symm)
  -- qProp has just w1 as a witness; ≤ 1 ✓
  have hq : atMost1_student qProp 0 := by
    intro ws hnd hall
    have hall_w1 : ∀ w ∈ ws, w = 1 := by
      intro w hw
      have := (hall w hw).2
      simpa [qProp] using this
    rcases ws with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = 1 := hall_w1 a (List.mem_cons_self ..)
        have hb : b = 1 := hall_w1 b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have : a ≠ b := List.ne_of_not_mem_cons (List.Nodup.notMem hnd)
        exact this (ha.trans hb.symm)
  -- p0 ∪ qProp has both w0 and w1 as witnesses; not ≤ 1
  have hcontr : ¬ atMost1_student (p0 ∪ qProp) 0 := by
    intro hle
    have : ([(0 : Fin 4), 1]).length ≤ 1 := by
      apply hle [0, 1]
      · decide
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact ⟨Or.inl rfl, by left; rfl⟩
        · rcases List.mem_singleton.mp hw' with rfl
          exact ⟨Or.inr rfl, by right; rfl⟩
    simp at this
  exact hcontr (key.mpr ⟨hp, hq⟩)

/-! ### Classical rows -/

/-- Negation: complementation realizes the anti-morphism row. -/
def negationWitness : ContextWitness .negation where
  f := (compl : Set (Fin 4) → Set (Fin 4))
  defined := fun _ => ⊤
  strawson := compl_soundFor_antiAddMult.strawsonSoundFor _
  classical := soundFor_of_mem_some compl_soundFor_antiAddMult
  strength := strength_of_mem_some (s₀ := .antiMorphic) (by decide)
    isAntiMorphic_compl

private theorem everyRestrictor_soundFor :
    Signature.SoundFor .antiAdd
      (fun R => every_sem (α := Bool) R (fun _ => False)) :=
  soundFor_antiAdd
    ⟨(leftAntiAdditive_iff_isAntiAdditive _).mp every_laa _,
     propext ⟨fun h => h true trivial, False.elim⟩⟩

/-- Universal restrictor: the restrictor section of `every_sem` is
completely anti-additive (toy scope falsifying the unit condition's
vacuity). -/
noncomputable def universalRestrictorWitness :
    ContextWitness .universalRestrictor where
  f := fun R => every_sem (α := Bool) R (fun _ => False)
  defined := fun _ => ⊤
  strawson := everyRestrictor_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some everyRestrictor_soundFor
  strength := strength_of_mem_some (s₀ := .antiAdditive) (by decide)
    ((leftAntiAdditive_iff_isAntiAdditive _).mp every_laa _)

private theorem noScope_soundFor :
    Signature.SoundFor .antiAdd
      (fun S => no_sem (α := Bool) (fun _ => True) S) :=
  soundFor_antiAdd
    ⟨(rightAntiAdditive_iff_isAntiAdditive _).mp no_raa _,
     propext ⟨fun h => h true trivial trivial, False.elim⟩⟩

/-- *Nobody*: the scope section of `no_sem` is completely anti-additive. -/
noncomputable def nobodyWitness : ContextWitness .nobody where
  f := fun S => no_sem (α := Bool) (fun _ => True) S
  defined := fun _ => ⊤
  strawson := noScope_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some noScope_soundFor
  strength := strength_of_mem_some (s₀ := .antiAdditive) (by decide)
    ((rightAntiAdditive_iff_isAntiAdditive _).mp no_raa _)

private noncomputable def fewScope : Set Bool → Prop :=
  few_sem (α := Bool) (fun _ => True)

private theorem fewScope_soundFor : Signature.SoundFor .anti fewScope :=
  soundFor_anti_iff.mpr ((scopeDownMono_iff_antitone _).mp few_scope_down _)

/-- *Few*: the scope section of `few_sem` is antitone (weak DE — and not
anti-additive, matching its `.anti` row). -/
noncomputable def fewWitness : ContextWitness .few where
  f := fewScope
  defined := fun _ => ⊤
  strawson := fewScope_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some fewScope_soundFor
  strength := strength_of_mem_some (s₀ := .weak) (by decide)
    (soundFor_anti_iff.mp fewScope_soundFor)

private theorem atMost_soundFor :
    Signature.SoundFor .anti atMost2_student :=
  soundFor_anti_iff.mpr atMost_antitone_scope

/-- *At most n*: `atMost2_student` is antitone; the strictness witness
`atMost_not_antiAdditive` is why this row is `.anti`, not `.antiAdd`. -/
def atMostWitness : ContextWitness .atMost where
  f := atMost2_student
  defined := fun _ => ⊤
  strawson := atMost_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some atMost_soundFor
  strength := strength_of_mem_some (s₀ := .weak) (by decide)
    atMost_antitone_scope

private theorem condAntecedent_soundFor :
    Signature.SoundFor .anti
      (fun α => condNecessity (W := Fin 4) (fun _ => Set.univ) α ∅) :=
  soundFor_anti_iff.mpr (conditional_antecedent_antitone _ _)

/-- Conditional antecedents: the antecedent section of `condNecessity` is
classically antitone with the modal base held constant. -/
def conditionalAntecedentWitness : ContextWitness .conditionalAntecedent where
  f := fun α => condNecessity (W := Fin 4) (fun _ => Set.univ) α ∅
  defined := fun _ => ⊤
  strawson := condAntecedent_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some condAntecedent_soundFor
  strength := strength_of_mem_some (s₀ := .weak) (by decide)
    (soundFor_anti_iff.mp condAntecedent_soundFor)

/-! ### Strawson-only rows (`classicalSignature = none`) -/

/-- *Only*: Strawson-`.anti` with its existence presupposition;
classically nothing (`onlyFull_not_de`). -/
def onlyFocusWitness : ContextWitness .onlyFocus where
  f := onlyFull (W := Fin 4) (· = (0 : Fin 4))
  defined := fun scope => {w | ∃ w', w' = (0 : Fin 4) ∧ scope w'}
  strawson := onlyFull_strawsonSoundFor_anti _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-- Adversatives: Strawson-`.anti` with doxastic factivity; classically
nothing (`sorryFull_not_de`). -/
def adversativeWitness : ContextWitness .adversative where
  f := sorryFull (W := Fin 4) (fun w => {w}) (fun _ => ({1} : Set (Fin 4)))
  defined := fun p => {w | ∀ w' ∈ ({w} : Set (Fin 4)), p w'}
  strawson := sorryFull_strawsonSoundFor_anti _ _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-- Temporal *since*: Strawson-`.anti` with the past-event
presupposition. -/
def sinceTemporalWitness : ContextWitness .sinceTemporal where
  f := sinceFull (W := Fin 4) (fun _ => ({0} : Set (Fin 4))) (fun _ => ∅)
  defined := fun p => {w | ∃ w' ∈ (({0} : Set (Fin 4)) : Set (Fin 4)), p w'}
  strawson := sinceFull_strawsonSoundFor_anti _ _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-- Superlatives: Strawson-`.anti` in the restriction with the
designated-subject presupposition. -/
def superlativeWitness : ContextWitness .superlative where
  f := superlativeAssert (W := Fin 4) (0 : Fin 4)
  defined := fun restriction => {w | superlativePresup (0 : Fin 4) restriction w}
  strawson := superlativeAssert_strawsonSoundFor_anti _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-! ### The table -/

/-- The witness table, populated incrementally; `none` rows are recorded
in the module docstring. -/
noncomputable def contextWitness? :
    (c : LicensingContext) → Option (ContextWitness c)
  | .negation => some negationWitness
  | .nobody => some nobodyWitness
  | .universalRestrictor => some universalRestrictorWitness
  | .few => some fewWitness
  | .atMost => some atMostWitness
  | .conditionalAntecedent => some conditionalAntecedentWitness
  | .onlyFocus => some onlyFocusWitness
  | .adversative => some adversativeWitness
  | .sinceTemporal => some sinceTemporalWitness
  | .superlative => some superlativeWitness
  -- Not yet grounded (no witness operator built). Explicit `none` arms — no `_`
  -- catch-all — so a newly-added `LicensingContext` fails to compile here rather
  -- than silently being treated as unwitnessed.
  | .beforeClause => none
  | .withoutClause => none
  | .question => none
  | .comparativeNP => none
  | .comparativeS => none
  | .tooTo => none
  | .modalPossibility => none
  | .modalNecessity => none
  | .imperative => none
  | .generic => none
  | .freeRelative => none
  | .doubtVerb => none
  | .denyVerb => none

-- Coverage sentries (drift detection, not aggregate counts).
example : (contextWitness? .negation).isSome = true := rfl
example : (contextWitness? .superlative).isSome = true := rfl
example : (contextWitness? .atMost).isSome = true := rfl
example : (contextWitness? .withoutClause).isSome = false := rfl

/-! ### Grounded strength licensing -/

instance {c : LicensingContext} (w : ContextWitness c) : Lattice w.β :=
  w.latticeβ

instance {c : LicensingContext} (w : ContextWitness c) : BoundedOrder w.β :=
  w.boundedβ

/-- At a witnessed presupposition-free row, keystone strength licensing
is semantically real: the witness operator holds the strength the item
requires. Strawson-only rows are exempt — their antitonicity holds only
on the definedness region. -/
theorem ContextWitness.holdsFor_of_licenses {c : LicensingContext}
    (w : ContextWitness c)
    (hcl : c.properties.classicalSignature =
      some c.properties.strawsonSignature)
    {e : Item} (hlic : zwartsScale.licenses e c) :
    ∀ r ∈ e.licensor, r.HoldsFor w.f := by
  obtain ⟨r, hr, s, hs, hrs⟩ := hlic
  intro r' hr'
  have hr₂ : r ∈ e.licensor := hr
  rw [Option.mem_def] at hr₂ hr'
  rw [hr₂] at hr'
  injection hr' with h
  subst h
  exact (w.strength _ (Option.mem_def.mpr hcl) s hs).of_le hrs

end Polarity
