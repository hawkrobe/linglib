import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Entailment.Soundness
import Linglib.Semantics.Entailment.StrawsonSoundness
import Linglib.Semantics.Entailment.AntiAdditivity
import Linglib.Semantics.Entailment.PositionProfile
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting

/-!
# Model witnesses for the licensing-context table

Each witnessed row of `LicensingContext.properties` carries a model operator
realizing its signatures: the classical row via `EntailmentSig.SoundFor`,
the Strawson row via `EntailmentSig.StrawsonSoundFor`. This converts the
table's `strawsonSignature`/`classicalSignature` annotations into derived
facts about denotations — the licensing analogue of the
derive-don't-stipulate rule.

Coverage is incremental (`contextWitness?` is `Option`-valued): the
witnessed rows are those whose operators exist in the zoo — negation
(`pnot`), the quantifier rows (`every_sem`/`no_sem`/`few_sem` sections,
`atMost2_student`), conditional antecedents (`condNecessity`), and the
four Strawson-only rows (`onlyFull`, `sorryFull`, `superlativeAssert`,
`sinceFull`). The `none` rows await operators (*without*, *deny*,
*doubt*, *before*, *too…to*, the comparatives) or concern rows whose
content is the licensing mechanism rather than the signature (the
FC/`mono` rows, questions).

`DEStrength.HoldsFor` gives the Zwarts strength levels their semantic
content (weak = `Antitone`, antiAdditive = `IsAntiAdditive`, antiMorphic
= `IsAntiMorphic`), downward closed along the chain
(`HoldsFor.of_le`); each witness carries a `strength` certificate for
its classical row, and `ContextWitness.holdsFor_of_licenses` grounds
the keystone: at a witnessed presupposition-free row, strength-matched
licensing means the operator really holds the strength the item
requires.

`GroundedPolarity` (in `Entailment/Polarity.lean`) is subsumed by this
table at the polarity quotient but retains external consumers; its
retirement is deferred.
-/

namespace Polarity

open NaturalLogic
open Quantification
open Entailment (World pnot)
open Entailment (atMost2_student atMost_isDE_scope)
open Entailment

/-! ### The Zwarts hierarchy semantically -/

/-- The semantic content of a `DEStrength` level for a context function
([icard-2012] §4, after Zwarts): `weak` is antitonicity, `antiAdditive`
the anti-additivity equation, `antiMorphic` the full anti-morphism —
*few* is weak-only, *no* anti-additive, *not* anti-morphic. -/
def _root_.NaturalLogic.DEStrength.HoldsFor {α β : Type*} [Lattice α]
    [Lattice β] (s : DEStrength) (f : α → β) : Prop :=
  match s with
  | .weak => Antitone f
  | .antiAdditive => IsAntiAdditive f
  | .antiMorphic => IsAntiMorphic f

/-- Strength facts are downward closed along the Zwarts chain
`weak < antiAdditive < antiMorphic`: a function holding a level holds
every weaker one. -/
theorem _root_.NaturalLogic.DEStrength.HoldsFor.of_le {α β : Type*}
    [Lattice α] [Lattice β] {f : α → β} {s₁ s₂ : DEStrength}
    (h : s₁ ≤ s₂) (hf : s₂.HoldsFor f) : s₁.HoldsFor f := by
  cases s₁ <;> cases s₂ <;>
    first
      | exact hf
      | exact hf.antitone
      | exact hf.antiAdditive
      | exact absurd h (by decide)

example : DEStrength.antiMorphic.HoldsFor pnot := pnot_isAntiMorphic
example : DEStrength.weak.HoldsFor pnot :=
  DEStrength.HoldsFor.of_le (s₂ := .antiMorphic) (by decide)
    pnot_isAntiMorphic

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
    EntailmentSig.StrawsonSoundFor c.properties.strawsonSignature
      f defined
  /-- The classical row, when present, is classically sound for `f`. -/
  classical :
    ∀ σ ∈ c.properties.classicalSignature, EntailmentSig.SoundFor σ f
  /-- The classical row's Zwarts strength holds semantically of `f`
      (vacuous at Strawson-only rows). -/
  strength :
    ∀ σ ∈ c.properties.classicalSignature, ∀ s ∈ σ.toDEStrength,
      s.HoldsFor f

private theorem soundFor_of_mem_some {W : Type*} {β : Type*} [Lattice β]
    [BoundedOrder β] {f : Set W → β} {σ₀ : EntailmentSig}
    (hf : EntailmentSig.SoundFor σ₀ f) :
    ∀ σ ∈ (some σ₀ : Option EntailmentSig), EntailmentSig.SoundFor σ f := by
  intro σ hσ
  rw [Option.mem_def] at hσ
  injection hσ with h
  exact h ▸ hf

private theorem soundFor_of_mem_none {W : Type*} {β : Type*} [Lattice β]
    [BoundedOrder β] {f : Set W → β} :
    ∀ σ ∈ (none : Option EntailmentSig), EntailmentSig.SoundFor σ f := by
  intro σ hσ
  rw [Option.mem_def] at hσ
  exact absurd hσ (by simp)

private theorem strength_of_mem_some {W : Type*} {β : Type*} [Lattice β]
    {f : Set W → β} {σ₀ : EntailmentSig} {s₀ : DEStrength}
    (hσ : σ₀.toDEStrength = some s₀) (hf : s₀.HoldsFor f) :
    ∀ σ ∈ (some σ₀ : Option EntailmentSig), ∀ s ∈ σ.toDEStrength,
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
    ∀ σ ∈ (none : Option EntailmentSig), ∀ s ∈ σ.toDEStrength,
      s.HoldsFor f := by
  intro σ hσ
  rw [Option.mem_def] at hσ
  exact absurd hσ (by simp)

/-! ### Classical rows -/

/-- Negation: `pnot` realizes the anti-morphism row. -/
def negationWitness : ContextWitness .negation where
  f := pnot
  defined := fun _ => ⊤
  strawson := pnot_soundFor_antiAddMult.strawsonSoundFor _
  classical := soundFor_of_mem_some pnot_soundFor_antiAddMult
  strength := strength_of_mem_some (s₀ := .antiMorphic) (by decide)
    pnot_isAntiMorphic

private theorem everyRestrictor_soundFor :
    EntailmentSig.SoundFor .antiAdd
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
    EntailmentSig.SoundFor .antiAdd
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

private theorem fewScope_soundFor : EntailmentSig.SoundFor .anti fewScope :=
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
    EntailmentSig.SoundFor .anti atMost2_student :=
  soundFor_anti_iff.mpr atMost_isDE_scope

/-- *At most n*: `atMost2_student` is antitone; the strictness witness
`atMost_not_antiAdditive` is why this row is `.anti`, not `.antiAdd`. -/
def atMostWitness : ContextWitness .atMost where
  f := atMost2_student
  defined := fun _ => ⊤
  strawson := atMost_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some atMost_soundFor
  strength := strength_of_mem_some (s₀ := .weak) (by decide)
    atMost_isDE_scope

private theorem condAntecedent_soundFor :
    EntailmentSig.SoundFor .anti
      (fun α => condNecessity (W := World) (fun _ => Set.univ) α ∅) :=
  soundFor_anti_iff.mpr (conditional_antecedent_antitone _ _)

/-- Conditional antecedents: the antecedent section of `condNecessity` is
classically antitone with the modal base held constant. -/
def conditionalAntecedentWitness : ContextWitness .conditionalAntecedent where
  f := fun α => condNecessity (W := World) (fun _ => Set.univ) α ∅
  defined := fun _ => ⊤
  strawson := condAntecedent_soundFor.strawsonSoundFor _
  classical := soundFor_of_mem_some condAntecedent_soundFor
  strength := strength_of_mem_some (s₀ := .weak) (by decide)
    (soundFor_anti_iff.mp condAntecedent_soundFor)

/-! ### Strawson-only rows (`classicalSignature = none`) -/

/-- *Only*: Strawson-`.anti` with its existence presupposition;
classically nothing (`onlyFull_not_de`). -/
def onlyFocusWitness : ContextWitness .onlyFocus where
  f := onlyFull (W := World) (· = World.w0)
  defined := fun scope => {w | ∃ w', w' = World.w0 ∧ scope w'}
  strawson := onlyFull_strawsonSoundFor_anti _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-- Adversatives: Strawson-`.anti` with doxastic factivity; classically
nothing (`sorryFull_not_de`). -/
def adversativeWitness : ContextWitness .adversative where
  f := sorryFull (W := World) (fun w => {w}) (fun _ => {World.w1})
  defined := fun p => {w | ∀ w' ∈ ({w} : Set World), p w'}
  strawson := sorryFull_strawsonSoundFor_anti _ _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-- Temporal *since*: Strawson-`.anti` with the past-event
presupposition. -/
def sinceTemporalWitness : ContextWitness .sinceTemporal where
  f := sinceFull (W := World) (fun _ => {World.w0}) (fun _ => ∅)
  defined := fun p => {w | ∃ w' ∈ ({World.w0} : Set World), p w'}
  strawson := sinceFull_strawsonSoundFor_anti _ _
  classical := soundFor_of_mem_none
  strength := strength_of_mem_none

/-- Superlatives: Strawson-`.anti` in the restriction with the
designated-subject presupposition. -/
def superlativeWitness : ContextWitness .superlative where
  f := superlativeAssert (W := World) World.w0
  defined := fun restriction => {w | superlativePresup World.w0 restriction w}
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
