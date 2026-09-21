import Linglib.Semantics.Dynamic.CDRT
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Piecewise
import Mathlib.Tactic.Tauto

/-!
# Visser (1998): Contexts in Dynamic Predicate Logic

This file formalizes [visser-1998]'s notion of context for the dynamic predicate logic of
[groenendijk-stokhof-1991], over updates of assignments. A context is a triple of
finite variable sets, the inputs a relation reads, the blocks at which it cuts the link between
input and output value, and the outputs it constrains, coherent off the blocks (`Context`,
Definition 3.1). Contexts compose and carry an information order, forming a monoid and a
partial order (Theorem 3.3). A relation has a context when it reads only the inputs, constrains
only the outputs and changes only the blocks (`HasContext`, Definition 3.4), which recovers the
paper's equational form of the definition and, at a test context, the finitely restricted
conditions of Definition 2.2. The information order is sound for the typing (Theorem 3.5), the
output of a typed relation over a varied input is unique and transfers agreement (Lemma 3.7),
and composition and dynamic implication are typed by the composed and the implication context
(Theorems 3.8 and 3.9). The typed generators, conditions and resets, give the language-free
soundness result that every DPL-expressible relation has a context (`DPLExpressible`,
Definition 3.10 and Theorem 3.11), with the existential typed by a block before its scope
(Definition 3.12).

## Implementation notes

Variables are natural numbers and the domain is a type parameter, so contexts are finsets of
naturals and assignments are functions from naturals. The patched output of Lemma 3.7 is
`Finset.piecewise` at the blocks. The typing is stated over the semantic relations rather than
the syntax, so Theorem 3.13 is the induction `DPLExpressible.hasContext` over the generators.

## TODO

* The converse of Theorem 3.5, for a domain with at least two elements, and the most
  informative context of the appendix, the partial meet of contexts as the infimum in the
  information order.
* The Switching Property characterization of the DPL-expressible relations of §§4-5, whose
  completeness direction needs the syntax stratum, and the meet typing of §6.

## References

* [visser-1998]
* [groenendijk-stokhof-1991]
-/

namespace Visser1998

open DynamicSemantics DynamicSemantics.Update

variable {E : Type*}

/-! ### Agreement relations (Definition 2.2) -/

/-- Agreement on `V` relates the assignments equal on `V` (Definition 2.2); the reset `[x]` of
the existential is agreement off `x`, the substrate's `randomAssign`
(`randomAssign_iff_eqOn`). -/
def agreeOn (V : Set ℕ) : Update (Assignment E) := fun f g ↦ Set.EqOn f g V

/-- A relation embeds in its composition with agreement on either side. -/
theorem le_agreeOn_seq (R : Update (Assignment E)) (V W : Set ℕ) :
    R ≤ seq (agreeOn V) (seq R (agreeOn W)) :=
  fun f g hR ↦ ⟨f, Set.eqOn_refl _ _, g, hR, Set.eqOn_refl _ _⟩

/-- Agreements compose to agreement on the intersection. -/
theorem agreeOn_seq_agreeOn (V W : Set ℕ) :
    seq (agreeOn V) (agreeOn W) = agreeOn (E := E) (V ∩ W) := by
  classical
  funext f h
  exact propext ⟨fun ⟨g, hV, hW⟩ v hv ↦ (hV hv.1).trans (hW hv.2),
    fun hVW ↦ ⟨V.piecewise f h, (V.piecewise_eqOn f h).symm,
      V.eqOn_piecewise.mpr ⟨fun v hv ↦ hVW ⟨hv.2, hv.1⟩, fun _ _ ↦ rfl⟩⟩⟩

/-- Agreements meet in agreement on the union. -/
theorem agreeOn_inf_agreeOn (V W : Set ℕ) :
    agreeOn V ⊓ agreeOn W = agreeOn (E := E) (V ∪ W) := by
  funext f g
  exact propext Set.eqOn_union.symm

/-- Agreement on no variables is trivial. -/
theorem agreeOn_empty : agreeOn (E := E) ∅ = ⊤ := by
  funext f g
  exact propext ⟨fun _ ↦ trivial, fun _ ↦ Set.eqOn_empty f g⟩

/-! ### Contexts (Definition 3.1) -/

/-- A DPL-context (Definition 3.1): input set `I` (variables the incoming
assignment is read at), block set `B` (variables whose input-output link
is cut), output set `O` (variables the outgoing assignment is constrained
at), coherent in the sense `I ∪ B = O ∪ B`. -/
@[ext] structure Context where
  /-- The input set. -/
  I : Finset ℕ
  /-- The block set: the barrier between past and future. -/
  B : Finset ℕ
  /-- The output set. -/
  O : Finset ℕ
  /-- Coherence: off the blocks, inputs and outputs coincide. -/
  coh : I ∪ B = O ∪ B

namespace Context

/-- Membership form of coherence. -/
theorem coh_mem (c : Context) {v : ℕ} : v ∈ c.I ∪ c.B ↔ v ∈ c.O ∪ c.B :=
  Finset.ext_iff.mp c.coh v

instance : One Context := ⟨⟨∅, ∅, ∅, rfl⟩⟩

/-- Context composition (Definition 3.1):
`⟨I,B,O⟩ * ⟨I',B',O'⟩ = ⟨I ∪ (I'∖B), B ∪ B', (O∖B') ∪ O'⟩`. -/
instance : Mul Context where
  mul c d :=
    { I := c.I ∪ (d.I \ c.B)
      B := c.B ∪ d.B
      O := (c.O \ d.B) ∪ d.O
      coh := calc
        (c.I ∪ (d.I \ c.B)) ∪ (c.B ∪ d.B)
            = (c.I ∪ c.B) ∪ (d.I ∪ d.B) := by ext v; grind
          _ = (c.O ∪ c.B) ∪ (d.O ∪ d.B) := by rw [c.coh, d.coh]
          _ = ((c.O \ d.B) ∪ d.O) ∪ (c.B ∪ d.B) := by ext v; grind }

@[simp] theorem I_mul (c d : Context) : (c * d).I = c.I ∪ (d.I \ c.B) := rfl
@[simp] theorem B_mul (c d : Context) : (c * d).B = c.B ∪ d.B := rfl
@[simp] theorem O_mul (c d : Context) : (c * d).O = (c.O \ d.B) ∪ d.O := rfl
@[simp] theorem I_one : (1 : Context).I = ∅ := rfl
@[simp] theorem B_one : (1 : Context).B = ∅ := rfl
@[simp] theorem O_one : (1 : Context).O = ∅ := rfl

/-- The contexts form a monoid (Theorem 3.3). -/
instance : Monoid Context where
  mul_assoc c d e := by
    ext v <;> simp only [I_mul, B_mul, O_mul, Finset.mem_union,
      Finset.mem_sdiff] <;> tauto
  one_mul c := by ext v <;> simp
  mul_one c := by ext v <;> simp

/-- The information order on contexts (Definition 3.1): more informative
contexts read, write, and block more — with new blocks confined to
variables the larger context both reads and writes. -/
instance : LE Context :=
  ⟨fun c d ↦ c.I ⊆ d.I ∧ c.O ⊆ d.O ∧ c.B ⊆ d.B ∧ d.B ⊆ c.B ∪ (d.I ∩ d.O)⟩

theorem le_def {c d : Context} :
    c ≤ d ↔ c.I ⊆ d.I ∧ c.O ⊆ d.O ∧ c.B ⊆ d.B ∧ d.B ⊆ c.B ∪ (d.I ∩ d.O) :=
  Iff.rfl

instance : DecidableLE Context := fun _ _ ↦ decidable_of_iff' _ le_def

/-- The information order is a partial order (Theorem 3.3). -/
instance : PartialOrder Context where
  le := (· ≤ ·)
  le_refl c := ⟨subset_rfl, subset_rfl, subset_rfl, Finset.subset_union_left⟩
  le_trans c d e h h' := by grind [le_def]
  le_antisymm c d h h' := by
    obtain ⟨hI, hO, hB, -⟩ := h
    obtain ⟨hI', hO', hB', -⟩ := h'
    exact Context.ext (hI.antisymm hI') (hB.antisymm hB') (hO.antisymm hO')

/-- The test context at `V`: reads and writes `V`, blocks nothing.
Conditions live here (`hasContext_atom`), and implication contexts are tests
(`Context.impl`). -/
def test (V : Finset ℕ) : Context := ⟨V, ∅, V, rfl⟩

/-- The implication context (Definition 3.1): implications are tests
reading the combined inputs. -/
def impl (c d : Context) : Context := test (c * d).I

@[simp] theorem I_test (V : Finset ℕ) : (test V).I = V := rfl
@[simp] theorem B_test (V : Finset ℕ) : (test V).B = ∅ := rfl
@[simp] theorem O_test (V : Finset ℕ) : (test V).O = V := rfl
@[simp] theorem I_impl (c d : Context) : (c.impl d).I = c.I ∪ (d.I \ c.B) := rfl
@[simp] theorem B_impl (c d : Context) : (c.impl d).B = ∅ := rfl
@[simp] theorem O_impl (c d : Context) : (c.impl d).O = c.I ∪ (d.I \ c.B) := rfl

end Context

/-! ### c-relations (Definition 3.4) -/

/-- `c` is a context for `R` (Definition 3.4): `R` reads its input only
at `c.I`, constrains its output only at `c.O`, and changes values only
at `c.B`. -/
structure HasContext (R : Update (Assignment E)) (c : Context) : Prop where
  /-- Only blocked variables change. -/
  blocks : ∀ ⦃f g⦄, R f g → Set.EqOn f g (↑c.B)ᶜ
  /-- Membership is invariant under input agreement on `I`, output
  agreement on `O`, and preservation off `B`. -/
  stable : ∀ ⦃f f' g g'⦄, R f g → Set.EqOn f' f ↑c.I →
    Set.EqOn g g' ↑c.O → Set.EqOn f' g' (↑c.B)ᶜ → R f' g'

/-- The paper's equational form of Definition 3.4. -/
theorem hasContext_iff_eq (R : Update (Assignment E)) (c : Context) :
    HasContext R c ↔
      R = seq (agreeOn ↑c.I) (seq R (agreeOn ↑c.O)) ⊓ agreeOn (↑c.B)ᶜ := by
  rw [le_antisymm_iff, le_inf_iff, and_iff_right (le_agreeOn_seq R _ _)]
  exact ⟨fun h ↦ ⟨h.blocks,
      fun f g ⟨⟨f₀, hI, g₀, hR, hO⟩, hB⟩ ↦ h.stable hR hI hO hB⟩,
    fun ⟨hb, hs⟩ ↦ ⟨hb,
      fun f f' g g' hR hI hO hB ↦ hs f' g' ⟨⟨f, hI, g, hR, hO⟩, hB⟩⟩⟩

/-- The `test V`-typed relations are exactly the `V`-invariant tests —
Definition 2.2's ⟨V⟩-conditions (noted after Definition 3.4). -/
theorem hasContext_test_iff {V : Finset ℕ} {R : Update (Assignment E)} :
    HasContext R (Context.test V) ↔
      IsTest R ∧
        ∀ ⦃f f'⦄, Set.EqOn f' f ↑V → R f f → R f' f' := by
  constructor
  · exact fun h ↦ ⟨fun f g hR ↦ funext fun v ↦ h.blocks hR (by simp),
      fun f f' hV hR ↦ h.stable hR hV hV.symm (Set.eqOn_refl _ _)⟩
  · rintro ⟨hdiag, hinv⟩
    refine ⟨fun f g hR v _ ↦ congrFun (hdiag hR) v,
      fun f f' g g' hR hI hO hB ↦ ?_⟩
    obtain rfl : f = g := hdiag hR
    obtain rfl : f' = g' := funext fun v ↦ hB (by simp)
    exact hinv hI hR

namespace HasContext

variable {c d : Context} {R S : Update (Assignment E)} {f f' g g' : ℕ → E}

/-! ### The order is sound for the typing (Theorem 3.5) -/

/-- Theorem 3.5(1): larger contexts type more relations —
`c ≤ d` and `R` a `c`-relation make `R` a `d`-relation. -/
theorem mono (h : HasContext R c) (hcd : c ≤ d) : HasContext R d := by
  obtain ⟨hI, hO, hB, hBio⟩ := hcd
  refine ⟨fun f g hR ↦ (h.blocks hR).mono
      (Set.compl_subset_compl.mpr (Finset.coe_subset.mpr hB)),
    fun f f' g g' hR hI' hO' hB' ↦ h.stable hR
      (hI'.mono (Finset.coe_subset.mpr hI))
      (hO'.mono (Finset.coe_subset.mpr hO)) (fun v hv ↦ ?_)⟩
  have hb := h.blocks hR
  grind [Set.EqOn]

/-! ### The unique-output lemma (Lemma 3.7) -/

/-- Lemma 3.7, transfer: the patch agrees with `g` at the blocks and
wherever the inputs agree. -/
theorem patch_eqOn {J : Set ℕ} (h : HasContext R c) (hR : R f g)
    (hJ : Set.EqOn f' f J) :
    Set.EqOn (c.B.piecewise g f') g (J ∪ ↑c.B) := by
  intro v hv
  have hb := h.blocks hR
  grind [Set.EqOn, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

/-- Lemma 3.7, existence: if `f'` agrees with `f` on the inputs and
`f R g`, then `R` relates `f'` to the patch of `f'` by `g` at the
blocks. -/
theorem patch (h : HasContext R c) (hI : Set.EqOn f' f ↑c.I)
    (hR : R f g) : R f' (c.B.piecewise g f') :=
  h.stable hR hI
    ((h.patch_eqOn hR hI).mono (fun v hv ↦ by
      have hc := c.coh_mem (v := v)
      grind)).symm
    (fun v hv ↦ (c.B.piecewise_eq_of_notMem _ _ hv).symm)

/-- Lemma 3.7, uniqueness: the patch is the only output over `f'`
agreeing with `g` on the blocks. -/
theorem patch_unique (h : HasContext R c) (hR : R f' g')
    (hB : Set.EqOn g' g ↑c.B) : g' = c.B.piecewise g f' := by
  have hb := h.blocks hR
  funext v
  grind [Set.EqOn, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

/-! ### Composition and implication typing (Theorems 3.8–3.9) -/

/-- Theorem 3.8: composition of a `c`-relation and a `d`-relation is a
`c * d`-relation. -/
theorem seq (hR : HasContext R c) (hS : HasContext S d) :
    HasContext (Update.seq R S) (c * d) where
  blocks := by
    rintro f g ⟨k, hfk, hkg⟩ v hv
    rw [Context.B_mul, Finset.coe_union, Set.compl_union] at hv
    exact (hR.blocks hfk hv.1).trans (hS.blocks hkg hv.2)
  stable := by
    rintro f f' g g' ⟨k, hfk, hkg⟩ hI hO hB
    -- Patch the intermediate assignment: keep it at `c.O ∪ d.I`, take
    -- the new output at the old blocks, the new input elsewhere.
    refine ⟨(c.O ∪ d.I).piecewise k (c.B.piecewise g' f'),
      hR.stable hfk (hI.mono (Finset.coe_subset.mpr Finset.subset_union_left))
        (fun v hv ↦ ((c.O ∪ d.I).piecewise_eq_of_mem _ _
          (Finset.mem_union_left _ hv)).symm) ?_,
      hS.stable hkg
        (fun v hv ↦ (c.O ∪ d.I).piecewise_eq_of_mem _ _
          (Finset.mem_union_right _ hv))
        (hO.mono (Finset.coe_subset.mpr Finset.subset_union_right)) ?_⟩
    all_goals
      intro v hv
      have hbR := hR.blocks hfk
      have hbS := hS.blocks hkg
      have hc := c.coh_mem (v := v)
      have hd := d.coh_mem (v := v)
      grind [Set.EqOn, Finset.piecewise_eq_of_mem,
        Finset.piecewise_eq_of_notMem, Context.I_mul, Context.O_mul,
        Context.B_mul]

/-- Theorem 3.9: DPL implication of a `c`-relation and a `d`-relation is
a `(c → d)`-relation. -/
theorem impl (hR : HasContext R c) (hS : HasContext S d) :
    HasContext (test (Update.impl R S)) (c.impl d) := by
  refine hasContext_test_iff.mpr ⟨fun _ _ h ↦ h.1, ?_⟩
  rintro f f' hI ⟨-, hall⟩
  refine ⟨rfl, fun k hRk ↦ ?_⟩
  -- Lemma 3.7 twice: patch the antecedent back to `f`, then transfer
  -- the consequent forward to `k`.
  obtain ⟨j, hSj⟩ := hall (c.B.piecewise k f) (hR.patch
    (hI.mono (Finset.coe_subset.mpr Finset.subset_union_left)).symm hRk)
  exact ⟨_, hS.patch ((hR.patch_eqOn hRk hI.symm).mono
    (fun v hv ↦ by grind [Context.I_mul])).symm hSj⟩

end HasContext

/-! ### The DPL generators, typed -/

/-- A condition depending only on `V` is a `Context.test V`-relation as a
test (the atomic case of the paper's semantic Theorem 3.13). -/
theorem hasContext_test (V : Finset ℕ) (p : (ℕ → E) → Prop)
    (hp : ∀ ⦃f f'⦄, Set.EqOn f f' ↑V → p f → p f') :
    HasContext (test p) (Context.test V) :=
  hasContext_test_iff.mpr ⟨fun _ _ h ↦ h.1,
    fun _ _ hV hR ↦ ⟨rfl, hp hV.symm hR.2⟩⟩

/-- The reset is typed at `⟨∅, {x}, ∅⟩` — Definition 3.12's `c_{∃v}`: it
reads nothing, constrains no output, and blocks `x`. -/
theorem hasContext_randomAssign (x : ℕ) :
    HasContext (randomAssign (S := Assignment E) x) ⟨∅, {x}, ∅, rfl⟩ :=
  ⟨fun f g hR v hv ↦ randomAssign_iff_eqOn.mp hR (by simpa using hv),
   fun f f' g g' _ _ _ hB ↦ randomAssign_iff_eqOn.mpr fun v hv ↦ hB (by simpa using hv)⟩

/-- The existential typing (Definition 3.12's `c_{∃v} • c_φ`): blocking
`x` before a `c`-relation types `∃x φ`. -/
theorem HasContext.dexists {c : Context} {φ : Update (Assignment E)} (x : ℕ)
    (h : HasContext φ c) :
    HasContext (dexists x φ) (⟨∅, {x}, ∅, rfl⟩ * c) :=
  (hasContext_randomAssign x).seq h

/-! ### The language-free soundness result (Theorem 3.11) -/

/-- The DPL-expressible relations (Definition 3.10): generated by
composition from resets and finitely restricted conditions. -/
inductive DPLExpressible : Update (Assignment E) → Prop
  | test (V : Finset ℕ) (p : (ℕ → E) → Prop)
      (hp : ∀ ⦃f f'⦄, Set.EqOn f f' ↑V → p f → p f') :
      DPLExpressible (test p)
  | randomAssign (x : ℕ) : DPLExpressible (randomAssign x)
  | seq {R S : Update (Assignment E)} :
      DPLExpressible R → DPLExpressible S → DPLExpressible (seq R S)

/-- Theorem 3.11: every DPL-expressible relation is an IBO-relation —
typed by some context. -/
theorem DPLExpressible.hasContext {R : Update (Assignment E)} (h : DPLExpressible R) :
    ∃ c, HasContext R c := by
  induction h with
  | test V p hp => exact ⟨_, hasContext_test V p hp⟩
  | randomAssign x => exact ⟨_, hasContext_randomAssign x⟩
  | seq _ _ ih ih' =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := ih'
    exact ⟨c * d, hc.seq hd⟩

end Visser1998
