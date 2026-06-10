import Linglib.Semantics.Lexical.Roots.Typology

/-!
# Entailment Closure on Roots

[beavers-koontz-garboden-2020] treat roots as *networks* of
entailments, where some atoms entail others, and state two
collocational restrictions as definitional: +result entails +state,
and +cause entails +result.

Two levels of closure:

* **Kind level** (canonical): `Root.closedFeatureSignature` is the
  collocational closure `Root.FeatureSignature.close` of the root's derived
  signature. Both book restrictions hold of closed signatures by
  construction (`closedFeatureSignature_wellFormed`).
* **Atom level** (label-tracking): `Root.closedEntailments` closes the
  labeled atom list under `bkgRules` (`becomesState s ⇒ hasState s`).
  Only the result→state edge is expressible here — `hasCause` is
  nullary, so cause→result lives at kind level only
  (`kind_closedEntailments_le`).

## Main declarations

* `bkgRules`, `bkgClosure`, `Root.closedEntailments`
* `Root.closedFeatureSignature`
* `mem_kind_closedEntailments` — the atom/kind bridge
-/

/-! ### Atom-level rules and closure -/

/-- The documented B&K-G atom-level entailment rule:
    `becomesState s ⇒ hasState s` (a change of state to `s` entails
    the resulting state attribution `s`, label preserved). The
    cause→result restriction is not expressible at atom level
    (`hasCause` carries no label) and is handled by
    `Root.FeatureSignature.close`. -/
def bkgRules : LexEntailment → List LexEntailment
  | .becomesState s => [.hasState s]
  | _ => []

/-- Every atom produced by `bkgRules` is a state atom, produced from a
    result atom. -/
theorem bkgRules_kind {a b : LexEntailment} (h : a ∈ bkgRules b) :
    a.kind = some .state ∧ b.kind = some .result := by
  cases b <;> simp [bkgRules] at h
  subst h; exact ⟨rfl, rfl⟩

/-- Close an atom list under `bkgRules`: adjoin everything the rules
    fire from a member. One step is a fixpoint, since rule outputs
    (state atoms) trigger no rules. -/
def bkgClosure (atoms : List LexEntailment) : List LexEntailment :=
  atoms ++ atoms.flatMap bkgRules

namespace Root

/-- The B&K-G closure of the root's base entailments. -/
def closedEntailments (r : Root) : List LexEntailment :=
  bkgClosure r.entailments

/-! ### Kind-level closure -/

/-- The closed feature signature: the collocational closure of the
    derived signature. Captures both book restrictions (result→state
    and cause→result). -/
def closedFeatureSignature (r : Root) : Root.FeatureSignature :=
  r.featureSignature.close

/-- The closed signature satisfies the collocational constraints by
    construction — what `RootEntailments.WellFormed` used to stipulate
    is a theorem of closure. -/
theorem closedFeatureSignature_wellFormed (r : Root) :
    r.closedFeatureSignature.WellFormed :=
  Root.FeatureSignature.close_wellFormed _

theorem featureSignature_le_closed (r : Root) :
    r.featureSignature ≤ r.closedFeatureSignature :=
  Root.FeatureSignature.le_close _

/-- Both theses are insensitive to the closure edges: a root violates
    Bifurcation iff its closed signature does. -/
theorem closed_violatesBifurcation_iff (r : Root) :
    r.closedFeatureSignature.ViolatesBifurcation ↔ r.ViolatesBifurcation :=
  Root.FeatureSignature.violatesBifurcation_close_iff _

/-! ### The atom/kind bridge -/

/-- Kinds realized by the atom-level closure: the base kinds plus a
    `state` kind whenever a result atom is present. -/
theorem mem_kind_closedEntailments {r : Root} {k : LexKind} :
    k ∈ (r.closedEntailments.filterMap (·.kind)).toFinset ↔
      k ∈ r.featureSignature ∨ (k = .state ∧ r.HasResult) := by
  simp only [List.mem_toFinset, List.mem_filterMap, closedEntailments, bkgClosure,
    List.mem_append, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha | ⟨b, hb, hab⟩, hk⟩
    · exact .inl (Root.mem_featureSignature.mpr ⟨a, ha, hk⟩)
    · obtain ⟨hak, hbk⟩ := bkgRules_kind hab
      refine .inr ⟨by rw [hk] at hak; exact Option.some_inj.mp hak, ?_⟩
      exact Root.mem_featureSignature.mpr ⟨b, hb, hbk⟩
  · rintro (hk | ⟨rfl, hres⟩)
    · obtain ⟨a, ha, hak⟩ := Root.mem_featureSignature.mp hk
      exact ⟨a, .inl ha, hak⟩
    · obtain ⟨b, hb, hbk⟩ := Root.mem_featureSignature.mp hres
      cases b <;> simp [LexEntailment.kind] at hbk
      rename_i lab
      exact ⟨.hasState lab, .inr ⟨_, hb, by simp [bkgRules]⟩, rfl⟩

/-- The atom-level closure realizes at most the kinds of the
    kind-level closure (strictly fewer when a root carries `cause`
    without a result atom — the cause→result edge is kind-level
    only). -/
theorem kind_closedEntailments_le (r : Root) :
    ((r.closedEntailments.filterMap (·.kind)).toFinset : Root.FeatureSignature)
      ≤ r.closedFeatureSignature := by
  intro k hk
  rcases mem_kind_closedEntailments.mp hk with h | ⟨rfl, hres⟩
  · exact featureSignature_le_closed r h
  · exact (Root.FeatureSignature.mem_close_iff _ _).mpr ⟨.result, hres, by decide⟩

end Root
