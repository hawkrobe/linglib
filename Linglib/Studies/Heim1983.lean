import Linglib.Semantics.Dynamic.Partial
import Linglib.Studies.Karttunen1973
import Linglib.Data.Examples.Heim1983

/-!
# Heim (1983): On the Projection Problem for Presuppositions

This file formalizes [heim-1983]: a context admits a sentence when the sentence's context
change potential is defined on it, a sentence presupposes what every admitting context
entails (12), and the heritage properties that [karttunen-peters-1979] stipulate for *if*
and *not* are read off the potentials (14) and (15): a context admits "If A, B" iff it admits
A and its update by A admits B, and negation is a hole. The King example (1)–(3) is worked as
the paper does (`king_admits_iff`), the two ways of accommodating a presupposition under
negation are (16)'s global and local readings (`globalNeg_entails`, `localNeg_entails`), and
contexts as sets of sequence–world pairs (§3) carry the potentials for open sentences and
for *every* (21): under the novelty stipulation (22), "Every nation cherishes its king"
presupposes that every nation has a king (`every_nation_presupposes`), a presupposition in
the restrictor projects universally (23), and an indefinite's presupposition projects
universally unless it is accommodated in the course of the update (§3.3).

## Implementation notes

The propositional part (§2) uses the substrate's partial context change potentials over a
type of worlds: `ofPartialProp` for a sentence with a presupposition and an assertion,
`cond` for (14), `neg` for (15), and `admits` for definedness, so that the heritage
properties are the substrate's `admits_cond` and `admits_neg`. The file part (§3) uses the
same potentials over pairs of a sequence `ℕ → M` and a world, with `atom`, `atomP`, and
`every` stated here as (19)–(21) and entailment by a context read as inclusion. The paper
gives no potential for *no* (24), so that sentence is a row only.

## References

* [heim-1983]
* [karttunen-1973]
* [karttunen-1974]
* [karttunen-peters-1979]
* [gazdar-1979]
* [lewis-1979]
-/

namespace Heim1983

open DynamicSemantics CCP.Partial Presupposition

/-! ### Admittance and presupposition (§2.1–§2.2) -/

section Propositional

variable {W : Type*}

/-- (12): `S` presupposes `p` iff every context that admits `S` entails `p`. -/
def Presupposes (φ : CCP.Partial W) (p : W → Prop) : Prop := ∀ c, φ.admits c → ∀ w ∈ c, p w

/-- (13): `S` is true in `w` with respect to `c` iff the context `c` updated by `S` is true
    in `w`; defined only when `c` admits `S`. -/
def TrueWrt (φ : CCP.Partial W) (c : Set W) (w : W) : Prop := ∃ h : φ.admits c, w ∈ (φ c).get h

/-- The content property is derivable from the potential: with respect to a context that is
    true in `w` and admits it, an atomic sentence is true in `w` iff its assertion holds. -/
theorem trueWrt_ofPartialProp {p : PartialProp W} {c : Set W} {w : W} (hw : w ∈ c)
    (h : (ofPartialProp p).admits c) : TrueWrt (ofPartialProp p) c w ↔ p.assertion w :=
  ⟨λ ⟨_, hm⟩ => hm.2, λ hq => ⟨h, hw, hq⟩⟩

variable (king son bald : W → Prop)

/-- (1) "The king has a son": presupposes a king, asserts that he has a son. -/
def kingHasSon : PartialProp W := ⟨king, son⟩

/-- (2) "The king's son is bald": presupposes a king with a son. -/
def kingsSonBald : PartialProp W := ⟨λ w => king w ∧ son w, bald⟩

/-- (3) "If the king has a son, the king's son is bald", by (14). -/
def ifKingHasSon : CCP.Partial W :=
  cond (ofPartialProp (kingHasSon king son)) (ofPartialProp (kingsSonBald king son bald))

variable {king son bald}

/-- §2.1: a context admits (3) iff it entails that there is a king: it must admit (1), and
    its update by (1) then admits (2) automatically. -/
theorem king_admits_iff (c : Set W) :
    (ifKingHasSon king son bald).admits c ↔ ∀ w ∈ c, king w := by
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, λ w hw => ⟨h w hw.1, hw.2⟩⟩

/-- (3) presupposes that there is a king. -/
theorem king_presupposes : Presupposes (ifKingHasSon king son bald) king :=
  λ _ h => (king_admits_iff _).1 h

/-- (3) does not presuppose that the king has a son, as soon as some world has a sonless
    king. -/
theorem not_presupposes_son (h : ∃ w, king w ∧ ¬ son w) :
    ¬ Presupposes (ifKingHasSon king son bald) son := by
  obtain ⟨w, hk, hs⟩ := h
  intro hp
  exact hs (hp {w} ((king_admits_iff _).2 λ _ hv => hv ▸ hk) w rfl)

/-! ### Accommodation (§2.3) -/

variable (φ : CCP.Partial W) (p : Set W)

/-- (A) The global option: to evaluate "Not S" in a context that does not admit `S`, amend the
    context to `c ∩ p` and compute `(c ∩ p) + Not S`. -/
def globalNeg : CCP.Partial W := λ c => neg φ (c ∩ p)

/-- (B) The local option: amend the context to `c ∩ p` only to compute `(c ∩ p) + S`, and
    subtract that from `c` itself. -/
def localNeg : CCP.Partial W := λ c => (φ (c ∩ p)).map (c \ ·)

variable {φ p}

/-- Both options make the update defined once the amended context admits `S`. -/
theorem globalNeg_admits {c : Set W} (h : φ.admits (c ∩ p)) : (globalNeg φ p).admits c := h

theorem localNeg_admits {c : Set W} (h : φ.admits (c ∩ p)) : (localNeg φ p).admits c := h

/-- The global option's result entails the accommodated presupposition: (16) read in
    isolation has France with a king. -/
theorem globalNeg_entails {c c' : Set W} (h : c' ∈ globalNeg φ p c) : c' ⊆ p :=
  λ _ hw => ((neg_eliminative φ h) hw).2

/-- The local option's result is the context minus the amended update: (16) continued with
    "because France doesn't have a king" entails only that either France has no king or he
    did not come. -/
theorem localNeg_entails {came : W → Prop} {c c' : Set W}
    (h : c' ∈ localNeg (ofPartialProp ⟨(· ∈ p), came⟩) p c) :
    c' = {w ∈ c | w ∉ p ∨ ¬ came w} := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).1 h
  rw [ofPartialProp, Part.mem_mk_iff] at ht
  obtain ⟨-, rfl⟩ := ht
  ext w
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- The local option is what a continuation denying the presupposition needs: the global
    result cannot contain a world without the presupposition, the local one can. -/
theorem globalNeg_disjoint {c c' : Set W} (h : c' ∈ globalNeg φ p c) : c' ∩ pᶜ = ∅ :=
  Set.eq_empty_of_forall_notMem λ _ ⟨hw, hn⟩ => hn (globalNeg_entails h hw)

end Propositional

/-! ### Files: contexts as sets of sequence–world pairs (§3) -/

section Files

variable {M W : Type*}

/-- A file: a set of pairs of a sequence of individuals and a world (§3.1). -/
abbrev File (M W : Type*) := Set ((ℕ → M) × W)

/-- (17): the proposition a file determines. -/
def File.prop (c : File M W) : Set W := {w | ∃ g, (g, w) ∈ c}

/-- (18): a file is true in a world when some sequence fits it there. -/
def File.TrueIn (c : File M W) (w : W) : Prop := ∃ g, (g, w) ∈ c

/-- (19): the update by an open sentence `P xᵢ` without presupposition. -/
def atom (P : M → W → Prop) (i : ℕ) : CCP.Partial ((ℕ → M) × W) :=
  ofTotal λ c => {gw ∈ c | P (gw.1 i) gw.2}

/-- (20): an open sentence `P xᵢ` presupposing `pre xᵢ` is admitted by a file iff every pair
    in it satisfies the presupposition at the `i`-th member. -/
def atomP (pre P : M → W → Prop) (i : ℕ) : CCP.Partial ((ℕ → M) × W) :=
  λ c => ⟨∀ gw ∈ c, pre (gw.1 i) gw.2, λ _ => {gw ∈ c | P (gw.1 i) gw.2}⟩

/-- (21): `c + Every xᵢ, A, B` keeps the pairs of `c` each of whose `i`-variants in `c + A`
    survives in `c + A + B`; defined iff `c + A` and `c + A + B` are. -/
def every (i : ℕ) (A B : CCP.Partial ((ℕ → M) × W)) : CCP.Partial ((ℕ → M) × W) :=
  λ c => (A c).bind λ cA => (B cA).map λ cAB =>
    {gw ∈ c | ∀ a, (Function.update gw.1 i a, gw.2) ∈ cA → (Function.update gw.1 i a, gw.2) ∈ cAB}

/-- (22): the file does not yet distinguish the `i`-th member of a sequence, the lexical
    novelty requirement of *every* and of an indefinite indexed `i`. -/
def File.NovelIn (c : File M W) (i : ℕ) : Prop :=
  ∀ g w a, (g, w) ∈ c ↔ (Function.update g i a, w) ∈ c

theorem atom_admits (P : M → W → Prop) (i : ℕ) (c : File M W) : (atom P i).admits c := trivial

theorem atomP_admits_iff (pre P : M → W → Prop) (i : ℕ) (c : File M W) :
    (atomP pre P i).admits c ↔ ∀ gw ∈ c, pre (gw.1 i) gw.2 := Iff.rfl

/-- The heritage of *every*: `c` admits `Every xᵢ, A, B` iff it admits `A` and `c + A` admits
    `B`. -/
theorem every_admits_iff (i : ℕ) (A B : CCP.Partial ((ℕ → M) × W)) (c : File M W) :
    (every i A B).admits c ↔ ∃ h : A.admits c, B.admits ((A c).get h) :=
  Iff.rfl

/-- (ii) of §3.2: with a presupposition-free restrictor `A xᵢ` and a nuclear scope
    presupposing `pre xᵢ`, the file must satisfy `pre` at the `i`-th member of every pair
    that survives `A`. -/
theorem every_atom_admits_iff (i : ℕ) (A pre B : M → W → Prop) (c : File M W) :
    (every i (atom A i) (atomP pre B i)).admits c ↔
      ∀ gw ∈ c, A (gw.1 i) gw.2 → pre (gw.1 i) gw.2 :=
  ⟨λ ⟨_, h⟩ gw hgw hA => h gw ⟨hgw, hA⟩, λ h => ⟨trivial, λ gw hgw => h gw hgw.1 hgw.2⟩⟩

/-- **(7) presupposes that every nation has a king.** Under (22) the condition of
    `every_atom_admits_iff` holds iff, in every world of the file's proposition, every
    individual satisfying the restrictor satisfies the presupposition: the novelty
    stipulation is what makes the universal presupposition necessary, not only sufficient. -/
theorem every_nation_presupposes (i : ℕ) (nation hasKing cherishes : M → W → Prop)
    {c : File M W} (hc : c.NovelIn i) :
    (every i (atom nation i) (atomP hasKing cherishes i)).admits c ↔
      ∀ w ∈ c.prop, ∀ a, nation a w → hasKing a w := by
  rw [every_atom_admits_iff]
  constructor
  · rintro h w ⟨g, hg⟩ a hn
    have := h (Function.update g i a, w) ((hc g w a).1 hg)
    simp only [Function.update_self] at this
    exact this hn
  · rintro h ⟨g, w⟩ hgw hn
    exact h w ⟨g, hgw⟩ _ hn

/-- (23): a presupposition in the restrictor projects universally too: "Everyone who serves
    his king will be rewarded" presupposes that everyone has a king, where
    [karttunen-peters-1979] predict no presupposition. -/
theorem every_restrictor_presupposes (i : ℕ) (hasKing serves rewarded : M → W → Prop)
    {c : File M W} (hc : c.NovelIn i) :
    (every i (atomP hasKing serves i) (atom rewarded i)).admits c ↔
      ∀ w ∈ c.prop, ∀ a, hasKing a w := by
  constructor
  · rintro ⟨h, -⟩ w ⟨g, hg⟩ a
    simpa using h (Function.update g i a, w) ((hc g w a).1 hg)
  · rintro h
    exact ⟨λ gw hgw => h gw.2 ⟨gw.1, hgw⟩ _, trivial⟩

/-! ### Indefinites (§3.3) -/

/-- (26)–(27): "A fat man was pushing his bicycle" is the sequence of two open sentences,
    the second presupposing that `xᵢ` has a bicycle. -/
def fatManBicycle (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop) :
    CCP.Partial ((ℕ → M) × W) :=
  seq (atom fatMan i) (atomP hasBicycle pushing i)

/-- Without accommodation, (25) carries the universal presupposition that every fat man had
    a bicycle, by (22): prima facie too strong. -/
theorem fatManBicycle_admits_iff (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    {c : File M W} (hc : c.NovelIn i) :
    (fatManBicycle i fatMan hasBicycle pushing).admits c ↔
      ∀ w ∈ c.prop, ∀ a, fatMan a w → hasBicycle a w := by
  constructor
  · rintro ⟨_, h⟩ w ⟨g, hg⟩ a hf
    have := h (Function.update g i a, w) ⟨(hc g w a).1 hg, by simpa using hf⟩
    simpa using this
  · rintro h
    exact ⟨trivial, λ gw hgw => h gw.2 ⟨gw.1, hgw.1⟩ _ hgw.2⟩

/-- Accommodation in the course of the update: `c + "xᵢ is a fat man"` is amended with
    "xᵢ has a bicycle" before the second sentence is evaluated. -/
def fatManBicycleAcc (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop) :
    CCP.Partial ((ℕ → M) × W) :=
  λ c => atomP hasBicycle pushing i {gw ∈ c | fatMan (gw.1 i) gw.2 ∧ hasBicycle (gw.1 i) gw.2}

/-- The accommodated update is always defined, and its result entails that `xᵢ` was a fat
    man, had a bicycle, and was pushing it. -/
theorem fatManBicycleAcc_admits (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    (c : File M W) : (fatManBicycleAcc i fatMan hasBicycle pushing).admits c :=
  λ _ hgw => hgw.2.2

theorem fatManBicycleAcc_entails (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    {c c' : File M W} (h : c' ∈ fatManBicycleAcc i fatMan hasBicycle pushing c) :
    ∀ gw ∈ c', fatMan (gw.1 i) gw.2 ∧ hasBicycle (gw.1 i) gw.2 ∧ pushing (gw.1 i) gw.2 := by
  rw [fatManBicycleAcc, atomP, Part.mem_mk_iff] at h
  obtain ⟨-, rfl⟩ := h
  exact λ gw hgw => ⟨hgw.1.2.1, hgw.1.2.2, hgw.2⟩

/-- The accommodated result entails nothing about fat men in general: in a two-individual
    model where only one fat man has a bicycle, the update is defined and non-empty. -/
theorem fatManBicycleAcc_not_universal :
    ∃ (c' : File Bool Unit), c' ∈ fatManBicycleAcc 0 (λ _ _ => True) (λ a _ => a = true)
        (λ _ _ => True) Set.univ ∧ c'.TrueIn () ∧
      ¬ ∀ w ∈ c'.prop, ∀ a : Bool, a = true := by
  refine ⟨_, Part.get_mem (fatManBicycleAcc_admits _ _ _ _ _), ⟨λ _ => true, ?_⟩, ?_⟩
  · exact ⟨⟨Set.mem_univ _, trivial, rfl⟩, trivial⟩
  · intro h
    exact Bool.false_ne_true (h () ⟨λ _ => true, ⟨Set.mem_univ _, trivial, rfl⟩, trivial⟩ false)

end Files

/-! ### The conjunction filter of Karttunen (1973) -/

/-- [karttunen-1973]'s filter for conjunction, relativized to the context itself as the set
    of background assumptions, is admittance of the sequenced update. -/
theorem admits_seq_iff_conj {W : Type*} (c : Set W) (p q : PartialProp W) :
    (seq (ofPartialProp p) (ofPartialProp q)).admits c ↔
      ∀ w ∈ c, (Karttunen1973.conj c p q).presup w := by
  rw [admits_seq_ofPartialProp]
  constructor
  · intro h w hw
    exact ⟨(h w hw).1, λ hne => absurd (λ v hv ha => (h v hv).2 ha) hne⟩
  · intro h w hw
    refine ⟨(h w hw).1, λ ha => ?_⟩
    by_contra hq
    exact hq ((h w hw).2 λ he => hq (he w hw ha))

end Heim1983
