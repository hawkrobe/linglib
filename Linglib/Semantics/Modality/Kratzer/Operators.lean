module

public import Linglib.Semantics.Modality.Kratzer.Ordering
public import Linglib.Logic.Modal.Basic

/-!
# Kratzer's modal operators

This file defines necessity and possibility over a modal base and an ordering source,
[kratzer-1981]'s operators, as the box and diamond of `Logic.Modal` over the accessibility
relations the two backgrounds induce: simple necessity quantifies over the accessible worlds
(`kratzerR`, `simpleNecessity`), necessity over the best accessible worlds (`kratzerBestR`,
`necessity`). The paper's own definition needs no Limit Assumption: human necessity asks each
accessible world to see, at least as good, a witness below which only `p`-worlds occur
(`humanNecessity`), and it is universal quantification over the best worlds exactly under the
Limit Assumption (`humanNecessity_iff_necessity`). The modal axioms follow from the frame
conditions the backgrounds impose (`duality`, `K_axiom`, `totally_realistic_gives_T`), a
realistic base being exactly one over which simple necessity is veridical
(`isRealistic_iff_simpleNecessity_le_id`), and a conditional antecedent restricts the modal base
(`restrictedBase`, `accessibleWorlds_restrictedBase`).

## Implementation notes

`necessity` quantifies over `bestWorlds` directly, so studies that treat `necessity` and
`possibility` as the Kratzer pair inherit the Limit Assumption; `humanNecessity` is the
limit-free form. The comparative-possibility scale of [kratzer-2012], good possibility, weak
necessity, and slight possibility, is not formalized.

## References

* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section


namespace Modality.Kratzer

open ModalLogic

variable {W : Type*}

/-! ### Accessibility relations -/

/-- Accessibility relation derived from a modal base.

    `kratzerR f w w'` iff `w'` satisfies all propositions in `f(w)`,
    i.e., `w' ∈ ⋂f(w)` in Kratzer's notation. -/
def kratzerR (f : ModalBase W) : W → W → Prop :=
  fun w w' => ∀ p ∈ f w, p w'

/-- Accessibility restricted to best worlds (modal base + ordering source).

    `kratzerBestR f g w w'` iff `w'` is among the best accessible worlds
    from `w` — accessible via `f` and maximal under the `g(w)`-ordering. -/
def kratzerBestR (f : ModalBase W) (g : OrderingSource W) : W → W → Prop :=
  fun w w' => w' ∈ bestWorlds f g w

/-- With the empty ordering source, best-world accessibility reduces to base
    accessibility. -/
theorem kratzerBestR_empty (f : ModalBase W) (w w' : W) :
    kratzerBestR f (emptyBackground (W := W)) w w' ↔ kratzerR f w w' := by
  rw [kratzerBestR, kratzerR, bestWorlds_emptyBackground]
  rfl

/-! ### Operators -/

/-- **Simple f-necessity**: `p` holds at every accessible world.
    `⟦must⟧_f(p)(w) = ∀w' ∈ ⋂f(w). p(w')`. -/
def simpleNecessity (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  box (kratzerR f) p w

/-- **Simple f-possibility**: `p` holds at some accessible world.
    `⟦can⟧_f(p)(w) = ∃w' ∈ ⋂f(w). p(w')`. -/
def simplePossibility (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  diamond (kratzerR f) p w

/-- Necessity with an ordering source holds when `p` holds at every best world.
    `⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')`.

    Adopts the Limit-Assumption-collapsed form. -/
def necessity (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  box (kratzerBestR f g) p w

/-- Possibility with an ordering source holds when `p` holds at some best world.
    `⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')`. -/
def possibility (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  diamond (kratzerBestR f g) p w

/-! ### Human necessity

[kratzer-1981]'s official definition needs no Limit Assumption: it
asks each accessible world to see, at least as good, a witness below
which only `p`-worlds occur. `necessity` (universal quantification
over `bestWorlds`) is its Limit-Assumption collapse. -/

/-- Human necessity ([kratzer-1981]; restated verbatim as "Necessity"
in [kratzer-2012]): every accessible world has an accessible world at
least as good, below which `p` holds throughout. Neutral with respect
to the Limit Assumption, after Lewis's counterfactual semantics. -/
def humanNecessity (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  ∀ u ∈ accessibleWorlds f w, ∃ v ∈ accessibleWorlds f w,
    atLeastAsGoodAs (g w) v u ∧
    ∀ z ∈ accessibleWorlds f w, atLeastAsGoodAs (g w) z v → p z

/-- Human necessity implies best-worlds necessity, unconditionally. -/
theorem necessity_of_humanNecessity {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W}
    (h : humanNecessity f g p w) : necessity f g p w := by
  rintro w' ⟨hacc, hmin⟩
  obtain ⟨v, hvacc, hvle, hall⟩ := h w' hacc
  exact hall w' hacc (hmin hvacc hvle)

/-- The Limit Assumption at `w` says that every accessible world sees a best
world at least as good. -/
def LimitAssumption (f : ModalBase W) (g : OrderingSource W) (w : W) : Prop :=
  ∀ u ∈ accessibleWorlds f w, ∃ v ∈ bestWorlds f g w,
    atLeastAsGoodAs (g w) v u

/-- Under the Limit Assumption, best-worlds necessity implies human
necessity. -/
theorem humanNecessity_of_necessity {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W}
    (hlim : LimitAssumption f g w) (h : necessity f g p w) :
    humanNecessity f g p w := by
  intro u hu
  obtain ⟨v, hvbest, hvle⟩ := hlim u hu
  refine ⟨v, hvbest.1, hvle, fun z hz hzv => h z ⟨hz, fun z' hz' hz'z => ?_⟩⟩
  exact atLeastAsGoodAs_trans hzv (hvbest.2 hz' (atLeastAsGoodAs_trans hz'z hzv))

/-- Under the Limit Assumption, [kratzer-1981]'s human necessity is
exactly universal quantification over the best worlds. -/
theorem humanNecessity_iff_necessity {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W} (hlim : LimitAssumption f g w) :
    humanNecessity f g p w ↔ necessity f g p w :=
  ⟨necessity_of_humanNecessity, humanNecessity_of_necessity hlim⟩

/-- Human possibility ([kratzer-2012]: "a possibility ... iff its
negation ... is not a necessity"): the dual of `humanNecessity`. -/
def humanPossibility (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  ¬ humanNecessity f g (fun v => ¬ p v) w

/-- With the empty ordering source, human necessity is simple necessity
([kratzer-1981], her equivalence for arbitrary `f` and empty `g`). -/
theorem humanNecessity_emptyBackground_iff (f : ModalBase W)
    (p : W → Prop) (w : W) :
    humanNecessity f emptyBackground p w ↔ simpleNecessity f p w := by
  constructor
  · intro h u hu
    obtain ⟨v, _, _, hall⟩ := h u hu
    exact hall u hu (atLeastAsGoodAs_nil u v)
  · intro h u hu
    exact ⟨u, hu, atLeastAsGoodAs_nil u u, fun z hz _ => h z hz⟩

/-! ### Characterization lemmas -/

@[simp]
theorem simpleNecessity_iff_all (f : ModalBase W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ ∀ w' ∈ accessibleWorlds f w, p w' := Iff.rfl

@[simp]
theorem simplePossibility_iff_any (f : ModalBase W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ∃ w' ∈ accessibleWorlds f w, p w' := Iff.rfl

@[simp]
theorem necessity_iff_all (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' := Iff.rfl

@[simp]
theorem possibility_iff_any (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    possibility f g p w ↔ ∃ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- Necessity with an empty ordering source collapses to simple necessity. -/
theorem necessity_empty_iff_simple (f : ModalBase W) (p : W → Prop) (w : W) :
    necessity f (emptyBackground (W := W)) p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff_all, simpleNecessity_iff_all]
  rw [bestWorlds_emptyBackground]

/-! ### Monotonicity in the modal base -/

/-- Premise growth preserves simple necessity, since more evidence leaves fewer accessible
    worlds and so at least as many necessities. This is [kratzer-2012]'s point about
    epistemic change over time (Ch. 4's approaching-man dialogue): one
    conversational background can represent evidence that grows as time goes by,
    and what *must* hold on the earlier evidence still must on the later. -/
theorem simpleNecessity_mono {f f' : ModalBase W} {p : W → Prop} {w : W}
    (h : f w ⊆ f' w) (hNec : simpleNecessity f p w) : simpleNecessity f' p w :=
  fun w' hw' => hNec w' (accessibleWorlds_anti h hw')

/-- Adding `p` to an ordering source that holds a proposition incompatible with `p` makes nothing
necessary that a best world verifying the latter fails. -/
theorem not_necessity_cons {f : ModalBase W} {g : OrderingSource W} {p q r : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u)
    (hur : ¬ r u) : ¬ necessity f (λ v => p :: g v) r w :=
  λ h => hur (h u (mem_bestWorlds_cons hq hpq hu huq))

/-! ### Frame conditions on `kratzerR` -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem realistic_refl (f : ModalBase W) (hReal : isRealistic f) :
    Std.Refl (kratzerR f) :=
  ⟨fun w p hp => hReal w p hp⟩

/-- Over a realistic base the evaluation world is itself accessible. -/
theorem realistic_gives_reflexive_access (f : ModalBase W)
    (hReal : isRealistic f) (w : W) :
    w ∈ accessibleWorlds f w :=
  (realistic_refl f hReal).refl w

/-- Realistic ⟹ serial. -/
theorem realistic_is_serial (f : ModalBase W) (hReal : isRealistic f) :
    IsSerial (kratzerR f) :=
  ⟨fun w => ⟨w, (realistic_refl f hReal).refl w⟩⟩

/-- A modal base is realistic exactly when its accessibility relation is reflexive. -/
theorem isRealistic_iff_refl {f : ModalBase W} : isRealistic f ↔ Std.Refl (kratzerR f) :=
  ⟨realistic_refl f, fun h w => h.refl w⟩

/-- A modal base is realistic exactly when simple necessity over it is veridical, what must be
the case being the case: **T** defines realism. -/
theorem isRealistic_iff_simpleNecessity_le_id {f : ModalBase W} :
    isRealistic f ↔ simpleNecessity f ≤ id :=
  isRealistic_iff_refl.trans box_T_iff.symm

/-- Under the empty modal base, every world is accessible. -/
theorem kratzerR_emptyBackground (w w' : W) :
    kratzerR (emptyBackground (W := W)) w w' :=
  λ _ hq => (List.not_mem_nil hq).elim

/-- Under a singleton modal base, accessibility is the sole premise. -/
theorem kratzerR_singleton (p : W → Prop) (w w' : W) :
    kratzerR (λ _ => [p]) w w' ↔ p w' := by
  simp [kratzerR]

/-- Empty modal base gives universal accessibility. -/
theorem empty_base_universal_access (w : W) :
    accessibleWorlds (emptyBackground (W := W)) w = Set.univ := by
  ext w'
  simp only [accessibleWorlds, emptyBackground, propIntersection,
             List.not_mem_nil, false_implies, forall_const, Set.mem_ofPred_eq,
             Set.mem_univ]

/-! ### Modal axioms (from `RestrictedModality`) -/

/-- Modal duality, `□p ↔ ¬◇¬p`, is the box–diamond duality (`ModalLogic.not_diamond`), since
    `necessity = box (kratzerBestR f g)`. -/
theorem duality (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ¬ possibility f g (fun w' => ¬ p w') w := by
  rw [necessity, possibility, ModalLogic.not_diamond]
  simp [ModalLogic.box]

/-- The K axiom, distribution, gives `□(p → q) → □p → □q`. -/
theorem K_axiom (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W)
    (hImpl : necessity f g (fun w' => p w' → q w') w)
    (hP : necessity f g p w) :
    necessity f g q w :=
  box_K hImpl hP

/-- Over a totally realistic base the T axiom holds for full necessity. -/
theorem totally_realistic_gives_T (f : ModalBase W) (g : OrderingSource W)
    (hTotal : isTotallyRealistic f)
    (p : W → Prop) (w : W)
    (hNec : necessity f g p w) : p w := by
  have hSelf : kratzerBestR f g w w := by
    refine ⟨?_, fun w'' hw'' _ => ?_⟩
    · show w ∈ propIntersection (f w)
      rw [hTotal w]; rfl
    · have : w'' ∈ propIntersection (f w) := hw''
      rw [hTotal w] at this
      cases this
      exact atLeastAsGoodAs_refl (g w) w
  exact hNec w hSelf

/-! ### Conditionals as modal-base restriction -/

/-- The modal base restricted by an antecedent, which prepends the antecedent to the base, so that
*if α, must β* is `must_{f + α} β`. -/
def restrictedBase (f : ModalBase W) (antecedent : W → Prop) : ModalBase W :=
  fun w => antecedent :: f w

/-- The accessible worlds of the restricted base are the antecedent-worlds among the accessible
worlds. -/
theorem accessibleWorlds_restrictedBase (f : ModalBase W) (α : W → Prop) (w : W) :
    accessibleWorlds (restrictedBase f α) w = {v ∈ accessibleWorlds f w | α v} :=
  Set.ext fun _ ↦ List.forall_mem_cons.trans and_comm

theorem mem_accessibleWorlds_restrictedBase {f : ModalBase W} {α : W → Prop} {w v : W} :
    v ∈ accessibleWorlds (restrictedBase f α) w ↔ v ∈ accessibleWorlds f w ∧ α v :=
  List.forall_mem_cons.trans and_comm

/-- Restricting by a stronger antecedent leaves fewer accessible worlds. -/
theorem accessibleWorlds_restrictedBase_mono (f : ModalBase W) {α₁ α₂ : W → Prop} (w : W)
    (h : ∀ v, α₂ v → α₁ v) :
    accessibleWorlds (restrictedBase f α₂) w ⊆ accessibleWorlds (restrictedBase f α₁) w :=
  fun _ hv ↦ mem_accessibleWorlds_restrictedBase.2
    ⟨(mem_accessibleWorlds_restrictedBase.1 hv).1, h _ (mem_accessibleWorlds_restrictedBase.1 hv).2⟩

end Modality.Kratzer
