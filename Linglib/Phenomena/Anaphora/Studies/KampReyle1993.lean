import Linglib.Theories.Semantics.Dynamic.Core.Accessibility
import Linglib.Theories.Semantics.Dynamic.DRT.Basic

/-!
# Kamp & Reyle (1993): From Discourse to Logic
@cite{kamp-reyle-1993}

End-to-end DRS analyses connecting the dynamic semantic formalism
from `Core.Accessibility` to empirical anaphora phenomena.

## Examples

1. **Existential persistence** (K&R Ch 1): "A man walked in. He sat down."
   Indefinites introduce discourse referents that persist across sentences.
   Truth conditions: `∃ e, man(e) ∧ walked_in(e) ∧ sat_down(e)`.

2. **Donkey anaphora** (K&R Def 1.4.4): "If a farmer owns a donkey, he beats it."
   The implication verification clause yields universal quantification:
   `∀ e₁ e₂, (farmer(e₁) ∧ donkey(e₂) ∧ owns(e₁,e₂)) → beats(e₁,e₂)`.

3. **Negation blocking** (K&R Ch 1): "A man didn't walk in. *He sat down."
   Drefs introduced under negation are not accessible.

4. **Subordination** (K&R Def 2.1.2): structural embedding governs
   anaphoric accessibility.
-/

namespace KampReyle1993

open Semantics.Dynamic.Core
open Semantics.Dynamic.Core.Accessibility
open Semantics.Dynamic.Core
open Semantics.Dynamic.Core.WeakestPrecondition
open Semantics.Dynamic.Core.DRSExpr
open Semantics.Dynamic.DRT

variable {E : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. Existential Persistence (Cross-Sentential Anaphora)
-- ════════════════════════════════════════════════════════════════

/-! "A¹ man walked in. He₁ sat down."

Two sentences merge into a single DRS via sequencing:
  `[u₁ | man u₁, walked_in u₁] ; [| sat_down u₁]`
After T₅ REDUCTION:
  `[u₁ | man u₁, walked_in u₁, sat_down u₁]`

Rels: 0=man, 1=walked_in, 2=sat_down -/

def exPersistence_compositional : DRSExpr :=
  .seq (.box [1] [.atom 0 [1], .atom 1 [1]])
       (.box [] [.atom 2 [1]])

def exPersistence : DRSExpr :=
  .box [1] [.atom 0 [1], .atom 1 [1], .atom 2 [1]]

/-- Cross-sentential anaphora: indefinite's dref persists. -/
theorem persistence_merge (rels : RelInterp E) :
    interp rels exPersistence_compositional = interp rels exPersistence :=
  (reduce_sound rels exPersistence_compositional).symm

/-- The merged DRS is proper: dref 1 is bound by the box. -/
example : isProper exPersistence = true := by decide

/-- Truth conditions for cross-sentential anaphora:
`∃ e, man(e) ∧ walked_in(e) ∧ sat_down(e)`.

The pronoun "he" in the second sentence is resolved to the dref
introduced by "a man" in the first — this is existential persistence. -/
theorem persistence_truthConditions (rels : RelInterp E) (g : Assignment E) :
    wp (interp rels exPersistence_compositional) (λ _ => True) g ↔
    ∃ e : E, rels 0 [e] ∧ rels 1 [e] ∧ rels 2 [e] := by
  rw [persistence_merge]
  simp only [exPersistence, interp, interp.interpConds,
    wp, dseq, test, List.foldl, and_true, List.map]
  constructor
  · rintro ⟨_, _, ⟨_, rfl, e, rfl⟩, _, ⟨rfl, hM⟩, _, ⟨rfl, hW⟩, _, ⟨rfl, hS⟩, rfl⟩
    exact ⟨e, hM, hW, hS⟩
  · rintro ⟨e, hM, hW, hS⟩
    let g' := g.update 1 e
    exact ⟨g', g', ⟨g, rfl, e, rfl⟩,
      g', ⟨rfl, hM⟩, g', ⟨rfl, hW⟩, g', ⟨rfl, hS⟩, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2. Donkey Anaphora (Universal Reading)
-- ════════════════════════════════════════════════════════════════

/-! "If a¹ farmer owns a² donkey, he₁ beats it₂."

The DRS `[| [u₁ u₂ | farmer u₁, donkey u₂, owns u₁ u₂] ⇒ [| beats u₁ u₂]]`
yields the universal reading: every farmer-donkey pair where ownership holds
also satisfies the beating relation. This is the K&R showpiece for how
dynamic implication (Def 1.4.4(f)) captures donkey anaphora without
E-type pronouns or syntactic movement.

Rels: 0=farmer, 1=donkey, 2=owns, 3=beats -/

def exDonkeyStandalone : DRSExpr :=
  .box [] [.impl
    (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
    (.box [] [.atom 3 [1, 2]])]

/-- The donkey conditional is proper: no free discourse referents. -/
example : isProper exDonkeyStandalone = true := by decide

/-- Donkey truth conditions: universal reading.

The dynamic implication verification clause (Def 1.4.4(f)) yields
universal quantification over farmer-donkey pairs:
`∀ e₁ e₂, (farmer(e₁) ∧ donkey(e₂) ∧ owns(e₁,e₂)) → beats(e₁,e₂)`. -/
theorem donkey_universal_reading (rels : RelInterp E) (g : Assignment E) :
    wp (interp rels exDonkeyStandalone) (λ _ => True) g ↔
    ∀ e₁ e₂ : E, (rels 0 [e₁] ∧ rels 1 [e₂] ∧ rels 2 [e₁, e₂]) →
                  rels 3 [e₁, e₂] := by
  simp only [exDonkeyStandalone, interp, interp.interpConds,
    wp, dseq, test, dimpl, List.foldl, and_true, List.map]
  constructor
  · intro h e₁ e₂ ⟨hF, hD, hO⟩
    obtain ⟨_, _, rfl, _, ⟨rfl, himpl⟩, rfl⟩ := h
    let g' := (g.update 1 e₁).update 2 e₂
    obtain ⟨_, _, rfl, _, ⟨rfl, hB⟩, rfl⟩ := himpl g'
      ⟨g', ⟨g.update 1 e₁, ⟨g, rfl, e₁, rfl⟩, e₂, rfl⟩,
       g', ⟨rfl, hF⟩, g', ⟨rfl, hD⟩, g', ⟨rfl, hO⟩, rfl⟩
    exact hB
  · intro hall
    exact ⟨g, g, rfl, g, ⟨rfl, fun h' hant => by
      obtain ⟨mid, ⟨m, ⟨_, rfl, e₁, rfl⟩, e₂, rfl⟩, hconds⟩ := hant
      obtain ⟨_, ⟨rfl, hF⟩, _, ⟨rfl, hD⟩, _, ⟨rfl, hO⟩, rfl⟩ := hconds
      let g' : Assignment E := (g.update 1 e₁).update 2 e₂
      exact ⟨g', g', rfl, g', ⟨rfl, hall _ _ ⟨hF, hD, hO⟩⟩, rfl⟩⟩, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Negation Blocking
-- ════════════════════════════════════════════════════════════════

/-! "A man didn't walk in. *He sat down."

Negation creates an inaccessible sub-DRS. The dref introduced
under negation cannot be picked up by a subsequent pronoun.

`[| ¬[u₁ | man u₁, walked_in u₁]]`

Dref 1 occurs only inside the negated box and is NOT free in the
overall DRS — the box binds it within the scope of negation. But
critically, it is not accessible from outside the negation. -/

def exNegationBlocking : DRSExpr :=
  .box [] [.neg (.box [1] [.atom 0 [1], .atom 1 [1]])]

/-- The negated DRS is proper (dref 1 is bound by its box). -/
example : isProper exNegationBlocking = true := by decide

/-- Truth conditions under negation:
`¬∃ e, man(e) ∧ walked_in(e)`.

The negation blocks dref accessibility: any continuation that
tries to reference dref 1 would be improper. -/
theorem negation_truthConditions (rels : RelInterp E) (g : Assignment E) :
    wp (interp rels exNegationBlocking) (λ _ => True) g ↔
    ¬∃ e : E, rels 0 [e] ∧ rels 1 [e] := by
  simp only [exNegationBlocking, interp, interp.interpConds,
    wp, dseq, test, dneg, List.foldl, and_true, List.map]
  constructor
  · rintro ⟨_, _, rfl, _, ⟨rfl, hneg⟩, rfl⟩
    intro ⟨e, hM, hW⟩
    apply hneg
    let g' := g.update 1 e
    exact ⟨g', g', ⟨g, rfl, e, rfl⟩,
      g', ⟨rfl, hM⟩, g', ⟨rfl, hW⟩, rfl⟩
  · intro hneg
    exact ⟨g, g, rfl, g, ⟨rfl, fun ⟨j, hj⟩ => by
      obtain ⟨_, ⟨_, rfl, e, rfl⟩, _, ⟨rfl, hM⟩, _, ⟨rfl, hW⟩, rfl⟩ := hj
      exact hneg ⟨e, hM, hW⟩⟩, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Multiple Discourse Referents
-- ════════════════════════════════════════════════════════════════

/-! "A¹ man met a² woman. He₁ greeted her₂."

Multiple drefs from a single sentence persist into the continuation.
  `[u₁ u₂ | man u₁, woman u₂, met u₁ u₂] ; [| greeted u₁ u₂]`

Rels: 0=man, 1=woman, 2=met, 3=greeted -/

def exMultipleDrefs_compositional : DRSExpr :=
  .seq (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
       (.box [] [.atom 3 [1, 2]])

/-- Multiple drefs merge: drefs 1,2 from the first box are fresh
in the (empty) continuation. -/
theorem multipleDrefs_merge (rels : RelInterp E) :
    interp rels exMultipleDrefs_compositional =
    interp rels (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2], .atom 3 [1, 2]]) :=
  (reduce_sound rels exMultipleDrefs_compositional).symm

-- ════════════════════════════════════════════════════════════════
-- § 5. Subordination (Def 2.1.2)
-- ════════════════════════════════════════════════════════════════

/-! Structural subordination governs anaphoric accessibility.
A sub-DRS K₁ is subordinate to K₂ when K₂'s conditions structurally
contain K₁ (via negation, implication, or disjunction).

These examples verify the subordination relation for the donkey
conditional, where both the antecedent and consequent boxes are
subordinate to the outer DRS. -/

/-- The antecedent box is immediately subordinate to the donkey DRS. -/
theorem donkey_antecedent_subordinate :
    ImmSubordinate
      (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
      (.box [] [.impl
        (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
        (.box [] [.atom 3 [1, 2]])]) :=
  .implLeft _ _ [] [] []

/-- The consequent box is immediately subordinate to the donkey DRS. -/
theorem donkey_consequent_subordinate :
    ImmSubordinate
      (.box [] [.atom 3 [1, 2]])
      (.box [] [.impl
        (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
        (.box [] [.atom 3 [1, 2]])]) :=
  .implRight _ _ [] [] []

/-- The consequent is (weakly) subordinate to the antecedent's
containing DRS, establishing the accessibility chain for donkey
anaphora: drefs introduced in the antecedent are accessible in
the consequent because both are subordinate to the same DRS. -/
theorem donkey_accessibility_chain :
    WeakSubordinate
      (.box [] [.atom 3 [1, 2]])
      (.box [] [.impl
        (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
        (.box [] [.atom 3 [1, 2]])]) :=
  .inr (.imm donkey_consequent_subordinate)

-- ════════════════════════════════════════════════════════════════
-- § 6. KRModel Evaluation
-- ════════════════════════════════════════════════════════════════

/-! Verification that `trueIn` correctly evaluates DRSs against
concrete models. These tests connect the model theory (Def 1.2.1)
to the wp truth-condition extraction. -/

/-- A concrete two-element domain with farmer, donkey, owns, beats.
Farmer = 0, donkey = 1. Farmer 0 owns donkey 1 and beats donkey 1. -/
def farmerPreds : RelInterp (Fin 2) := fun rel args =>
  match rel with
  | 0 => args = [0]            -- farmer(0)
  | 1 => args = [1]            -- donkey(1)
  | 2 => args = [0, 1]         -- owns(0,1)
  | 3 => args = [0, 1]         -- beats(0,1)
  | _ => False

/-- The donkey conditional is true in the farmer model:
farmer 0 owns donkey 1, and farmer 0 beats donkey 1. -/
theorem donkey_true_in_model (g : Assignment (Fin 2)) :
    wp (interp farmerPreds exDonkeyStandalone) (λ _ => True) g := by
  rw [donkey_universal_reading]
  intro e₁ e₂ ⟨hF, hD, hO⟩
  simp only [farmerPreds, List.cons.injEq, and_true] at hF hD hO ⊢
  subst hF; subst hD; exact hO

-- ════════════════════════════════════════════════════════════════
-- § 7. Compositional Derivation (T₀–T₅ Pipeline)
-- ════════════════════════════════════════════════════════════════

/-! End-to-end compositional derivation of "a¹ man adores a² woman".

The T₀–T₅ rules (@cite{muskens-1996}, pp. 165–167) produce a sequence
of two boxes. The derivation tree yields:

  `[u₁ | man u₁] ; [u₂ | woman u₂, u₁ adores u₂]`

T₅ REDUCTION (the merging lemma) collapses this into the standard
single-box DRS `exManAdoresWoman` from `Core.DRSExpr`.

Rels: 0=man, 1=woman, 2=adores -/

def exManAdoresWoman_compositional : DRSExpr :=
  .seq (.box [1] [.atom 0 [1]])
       (.box [2] [.atom 1 [2], .atom 2 [1, 2]])

/-- T₅ REDUCTION: the merging lemma collapses the compositional
derivation into the standard single-box DRS. -/
theorem exManAdoresWoman_merge (rels : RelInterp E) :
    interp rels exManAdoresWoman_compositional = interp rels exManAdoresWoman :=
  mergingLemma rels [1] [2] [.atom 0 [1]] [.atom 1 [2], .atom 2 [1, 2]]
    (by intro n hn c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn hc
        subst hn; subst hc; decide)

/-- Truth conditions via the compositional route:
`∃ e₁ e₂, man(e₁) ∧ woman(e₂) ∧ adores(e₁, e₂)`. -/
theorem exManAdoresWoman_truthConditions (rels : RelInterp E) (g : Assignment E) :
    wp (interp rels exManAdoresWoman_compositional) (λ _ => True) g ↔
    ∃ e₁ e₂ : E, rels 0 [e₁] ∧ rels 1 [e₂] ∧ rels 2 [e₁, e₂] := by
  rw [exManAdoresWoman_merge]
  simp only [exManAdoresWoman, interp, interp.interpConds,
    wp, dseq, test, List.foldl, and_true, List.map]
  constructor
  · intro h
    obtain ⟨j, g₁, hintro, hconds⟩ := h
    obtain ⟨g₂, hg₂, e₂, rfl⟩ := hintro
    obtain ⟨g₃, rfl, e₁, rfl⟩ := hg₂
    obtain ⟨g₄, ⟨rfl, hR₁⟩, hrest⟩ := hconds
    obtain ⟨g₅, ⟨rfl, hR₂⟩, hrest2⟩ := hrest
    obtain ⟨g₆, ⟨rfl, hR₃⟩, rfl⟩ := hrest2
    simp [Assignment.update] at hR₁ hR₂ hR₃
    exact ⟨e₁, e₂, hR₁, hR₂, hR₃⟩
  · intro ⟨e₁, e₂, hR₁, hR₂, hR₃⟩
    let g' := (g.update 1 e₁).update 2 e₂
    use g', g'
    exact ⟨⟨g.update 1 e₁, ⟨g, rfl, e₁, rfl⟩, e₂, rfl⟩,
      g', ⟨rfl, by simp [g']; exact hR₁⟩,
      g', ⟨rfl, by simp [g']; exact hR₂⟩,
      g', ⟨rfl, by simp [g']; exact hR₃⟩, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 8. Stress Tests for the Merging Lemma
-- ════════════════════════════════════════════════════════════════

/-! Harder derivations that stress-test `reduce` across multiple
dimensions: three-box merges, nested conditions, iterated reductions,
and multi-sentence discourses.  Every merge theorem is a one-liner:
`reduce_sound` handles all freshness checks automatically. -/

-- ──────────────────────────────────────────────────────────────
-- Test 1: Three-box merge (ditransitive)
-- "A¹ man gives a² woman a³ book"
-- Compositional: [u₁|man u₁]; [u₂|woman u₂]; [u₃|book u₃, gives u₁ u₂ u₃]
-- Merged:        [u₁ u₂ u₃|man u₁, woman u₂, book u₃, gives u₁ u₂ u₃]
-- Rels: 0=man, 1=woman, 2=book, 3=gives
-- ──────────────────────────────────────────────────────────────

def exDitransitive_compositional : DRSExpr :=
  .seq (.seq (.box [1] [.atom 0 [1]])
             (.box [2] [.atom 1 [2]]))
       (.box [3] [.atom 2 [3], .atom 3 [1, 2, 3]])

def exDitransitive : DRSExpr :=
  .box [1, 2, 3] [.atom 0 [1], .atom 1 [2], .atom 2 [3], .atom 3 [1, 2, 3]]

/-- Three-box merge via `reduce`. -/
theorem exDitransitive_merge (rels : RelInterp E) :
    interp rels exDitransitive_compositional = interp rels exDitransitive :=
  (reduce_sound rels exDitransitive_compositional).symm

/-- Truth conditions: `∃ e₁ e₂ e₃, man(e₁) ∧ woman(e₂) ∧ book(e₃) ∧ gives(e₁,e₂,e₃)` -/
theorem exDitransitive_truthConditions (rels : RelInterp E) (g : Assignment E) :
    wp (interp rels exDitransitive_compositional) (λ _ => True) g ↔
    ∃ e₁ e₂ e₃ : E, rels 0 [e₁] ∧ rels 1 [e₂] ∧ rels 2 [e₃] ∧ rels 3 [e₁, e₂, e₃] := by
  rw [exDitransitive_merge]
  simp only [exDitransitive, interp, interp.interpConds,
    wp, dseq, test, List.foldl, and_true, List.map]
  constructor
  · rintro ⟨j, g₁, hintro, hconds⟩
    obtain ⟨g₂, ⟨g₃, ⟨g₄, rfl, e₁, rfl⟩, e₂, rfl⟩, e₃, rfl⟩ := hintro
    obtain ⟨g₅, ⟨rfl, hR₁⟩, g₆, ⟨rfl, hR₂⟩, g₇, ⟨rfl, hR₃⟩, g₈, ⟨rfl, hR₄⟩, rfl⟩ := hconds
    simp [Assignment.update] at hR₁ hR₂ hR₃ hR₄
    exact ⟨e₁, e₂, e₃, hR₁, hR₂, hR₃, hR₄⟩
  · rintro ⟨e₁, e₂, e₃, hR₁, hR₂, hR₃, hR₄⟩
    let g' := ((g.update 1 e₁).update 2 e₂).update 3 e₃
    use g', g'
    refine ⟨⟨(g.update 1 e₁).update 2 e₂, ⟨g.update 1 e₁, ⟨g, rfl, e₁, rfl⟩, e₂, rfl⟩, e₃, rfl⟩, ?_⟩
    exact ⟨g', ⟨rfl, by simp [g']; exact hR₁⟩,
      g', ⟨rfl, by simp [g']; exact hR₂⟩,
      g', ⟨rfl, by simp [g']; exact hR₃⟩,
      g', ⟨rfl, by simp [g']; exact hR₄⟩, rfl⟩

-- ──────────────────────────────────────────────────────────────
-- Test 2: Nested negation in first box
-- "A¹ man who doesn't smoke² meets a³ woman"
-- Compositional: [u₁|man u₁, ¬[u₂|smoke u₂, u₂=u₁]]; [u₃|woman u₃, meets u₁ u₃]
-- Rels: 0=man, 1=smoke, 2=woman, 3=meets
-- ──────────────────────────────────────────────────────────────

def exNegation_compositional : DRSExpr :=
  .seq (.box [1] [.atom 0 [1], .neg (.box [2] [.atom 1 [2], .is 2 1])])
       (.box [3] [.atom 2 [3], .atom 3 [1, 3]])

def exNegation : DRSExpr :=
  .box [1, 3] [.atom 0 [1], .neg (.box [2] [.atom 1 [2], .is 2 1]),
               .atom 2 [3], .atom 3 [1, 3]]

/-- Merge with nested negation: dref 3 is fresh in `¬[u₂|smoke u₂, u₂=u₁]`. -/
theorem exNegation_merge (rels : RelInterp E) :
    interp rels exNegation_compositional = interp rels exNegation :=
  (reduce_sound rels exNegation_compositional).symm

-- ──────────────────────────────────────────────────────────────
-- Test 3: Nested implication (donkey sentence + continuation)
-- "Every¹ farmer who owns a² donkey beats it₂.  A³ vet arrives."
-- Rels: 0=farmer, 1=donkey, 2=owns, 3=beats, 4=vet, 5=arrives
-- ──────────────────────────────────────────────────────────────

def exDonkey_compositional : DRSExpr :=
  .seq (.box [] [.impl
          (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
          (.box [] [.atom 3 [1, 2]])])
       (.box [3] [.atom 4 [3], .atom 5 [3]])

def exDonkey_merged : DRSExpr :=
  .box [3] [.impl
          (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
          (.box [] [.atom 3 [1, 2]]),
        .atom 4 [3], .atom 5 [3]]

/-- Merge through nested implication: dref 3 is fresh in the donkey conditional. -/
theorem exDonkey_merge (rels : RelInterp E) :
    interp rels exDonkey_compositional = interp rels exDonkey_merged :=
  (reduce_sound rels exDonkey_compositional).symm

-- ──────────────────────────────────────────────────────────────
-- Test 4: K&R (1.47) — relative clause with three drefs
-- "Jones¹ owns a² book which Smith³ adores"
-- Rels: 0=Jones, 1=book, 2=Smith, 3=adores, 4=owns
-- ──────────────────────────────────────────────────────────────

def exRelClause_compositional : DRSExpr :=
  .seq (.box [1] [.atom 0 [1]])
       (.box [2, 3] [.atom 1 [2], .atom 2 [3], .atom 3 [3, 2], .atom 4 [1, 2]])

def exRelClause : DRSExpr :=
  .box [1, 2, 3] [.atom 0 [1], .atom 1 [2], .atom 2 [3],
                   .atom 3 [3, 2], .atom 4 [1, 2]]

/-- K&R (1.47): merge with cross-referencing conditions. -/
theorem exRelClause_merge (rels : RelInterp E) :
    interp rels exRelClause_compositional = interp rels exRelClause :=
  (reduce_sound rels exRelClause_compositional).symm

-- ──────────────────────────────────────────────────────────────
-- Test 5: Four-sentence discourse with iterated merge
-- "A¹ cat caught a² mouse.  It₁ ate it₂.  A³ dog watched.  It₃ barked."
-- Rels: 0=cat, 1=mouse, 2=caught, 3=ate, 4=dog, 5=watched, 6=barked
-- ──────────────────────────────────────────────────────────────

def exFourSentence_compositional : DRSExpr :=
  .seq (.seq (.seq (.seq
    (.box [1] [.atom 0 [1]])
    (.box [2] [.atom 1 [2], .atom 2 [1, 2]]))
    (.box [] [.atom 3 [1, 2]]))
    (.box [3] [.atom 4 [3], .atom 5 [3]]))
    (.box [] [.atom 6 [3]])

def exFourSentence : DRSExpr :=
  .box [1, 2, 3] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2],
                   .atom 3 [1, 2], .atom 4 [3], .atom 5 [3], .atom 6 [3]]

/-- Iterated merge across a 4-sentence discourse — one line via `reduce`. -/
theorem exFourSentence_merge (rels : RelInterp E) :
    interp rels exFourSentence_compositional = interp rels exFourSentence :=
  (reduce_sound rels exFourSentence_compositional).symm

-- ──────────────────────────────────────────────────────────────
-- Test 6: Disjunction in first box
-- "A¹ student [passed or failed].  A² teacher noticed."
-- Rels: 0=student, 1=passed, 2=failed, 3=teacher, 4=noticed
-- ──────────────────────────────────────────────────────────────

def exDisjunction_compositional : DRSExpr :=
  .seq (.box [1] [.atom 0 [1], .disj (.box [] [.atom 1 [1]]) (.box [] [.atom 2 [1]])])
       (.box [2] [.atom 3 [2], .atom 4 [2, 1]])

/-- Merge with disjunction condition: dref 2 is fresh in the disjunction. -/
theorem exDisjunction_merge (rels : RelInterp E) :
    interp rels exDisjunction_compositional =
    interp rels (.box [1, 2] [.atom 0 [1],
                   .disj (.box [] [.atom 1 [1]]) (.box [] [.atom 2 [1]]),
                   .atom 3 [2], .atom 4 [2, 1]]) :=
  (reduce_sound rels exDisjunction_compositional).symm

end KampReyle1993
