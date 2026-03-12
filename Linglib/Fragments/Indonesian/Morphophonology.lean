/-!
# Indonesian Morphophonology
@cite{sneddon-1996}

The nasal assimilation rules governing the meN- prefix allomorph
selection, from @cite{sneddon-1996} §1.5.

## meN- allomorph rules

The capital N in *meN-* represents a nasal that assimilates to the
first segment of the base. The nasal can surface as **m**, **n**,
**ny**, **ng**, or **zero**, and in some cases the base-initial
consonant is deleted:

| Base initial       | Prefix  | Deletion? | Example                |
|--------------------|---------|-----------|------------------------|
| vowel, g, k, h     | meng-   | k deleted | *meng-ajar*, *meng-irim* |
| b, p, f            | mem-    | p deleted | *mem-beli*, *mem-akai*   |
| d, t, c, j, z      | men-    | t deleted | *men-dengar*, *men-ulis* |
| s                  | meny-   | s deleted | *meny-ewa*               |
| l, r, m, n, w, y   | me-     | —         | *me-lihat*, *me-masak*   |
-/

namespace Fragments.Indonesian.Morphophonology

/-- The meN- allomorph prefix selected by the initial segment of the root
    (@cite{sneddon-1996} §1.5). The nasal N undergoes assimilation:
    - Before **b, p, f**: *mem-* (bilabial nasal m)
    - Before **d, t, c, j, z**: *men-* (alveolar nasal n)
    - Before **s**: *meny-* (palatal nasal ny; s deleted)
    - Before **l, r, m, n, w, y**: *me-* (N lost)
    - Elsewhere (vowels, **g, k, h**): *meng-* (velar nasal ng) -/
def meNPrefix : Char → String
  | 'b' | 'p' | 'f' => "mem"
  | 'd' | 't' | 'c' | 'j' | 'z' => "men"
  | 's' => "meny"
  | 'l' | 'r' | 'm' | 'n' | 'w' | 'y' => "me"
  | _ => "meng"

/-- Derive the expected meN- form from a root, using the phonological
    rules from @cite{sneddon-1996} §1.5. The result shows the morpheme
    boundary (prefix-root), preserving the root-initial consonant even
    when it is deleted in the surface form (e.g., *mem-pecah* rather
    than *memecah*). -/
def deriveMeN (root : String) : Option String :=
  match root.toList with
  | c :: _ => some (meNPrefix c ++ "-" ++ root)
  | [] => none

-- ============================================================================
-- Per-class verification
-- ============================================================================

/-- Vowel-initial roots get *meng-*. -/
theorem vowel_meng : meNPrefix 'a' = "meng" := rfl

/-- Labial-initial roots get *mem-*. -/
theorem labial_mem : meNPrefix 'b' = "mem" ∧ meNPrefix 'p' = "mem" := ⟨rfl, rfl⟩

/-- Dental-initial roots get *men-*. -/
theorem dental_men : meNPrefix 'd' = "men" ∧ meNPrefix 't' = "men" ∧
    meNPrefix 'c' = "men" ∧ meNPrefix 'j' = "men" := ⟨rfl, rfl, rfl, rfl⟩

/-- Sibilant-initial roots get *meny-*. -/
theorem sibilant_meny : meNPrefix 's' = "meny" := rfl

/-- Sonorant-initial roots get *me-*. -/
theorem sonorant_me : meNPrefix 'l' = "me" ∧ meNPrefix 'r' = "me" ∧
    meNPrefix 'm' = "me" := ⟨rfl, rfl, rfl⟩

/-- Velar-initial roots get *meng-*. -/
theorem velar_meng : meNPrefix 'g' = "meng" ∧ meNPrefix 'k' = "meng" ∧
    meNPrefix 'h' = "meng" := ⟨rfl, rfl, rfl⟩

end Fragments.Indonesian.Morphophonology
