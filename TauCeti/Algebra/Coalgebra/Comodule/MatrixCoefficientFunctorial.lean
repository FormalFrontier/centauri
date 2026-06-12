/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficientAdjoin
import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Functoriality of matrix coefficients

This file records how the matrix coefficients of a right comodule behave under comodule
morphisms. A surjective comodule morphism cannot create new coefficients: every coefficient
of the target is a coefficient of the source, with the functional pulled back along the
morphism. Consequently the coefficient span and coefficient algebra are invariant under
inverse comodule morphisms and under transport of a comodule structure across a linear
equivalence.

These lemmas are bookkeeping for the reductive-groups roadmap's faithful-representation
criterion: faithful representations are detected by whether their matrix coefficients
generate the coordinate Hopf algebra.

## Main declarations

* `TauCeti.Comodule.matrixCoefficient_mem_set_of_map`: coefficients of mapped vectors are
  source coefficients.
* `TauCeti.Comodule.matrixCoefficientSet_subset_of_surjective`: a surjective comodule
  morphism makes target coefficients source coefficients.
* `TauCeti.Comodule.matrixCoefficientSubmodule_le_of_surjective` and
  `TauCeti.Comodule.matrixCoefficientSubalgebra_le_of_surjective`: the corresponding span
  and algebra-generation consequences.
* `TauCeti.Comodule.matrixCoefficientSubmodule_eq_of_inverse_hom` and
  `TauCeti.Comodule.matrixCoefficientSubalgebra_eq_of_inverse_hom`: coefficient objects are
  invariant under inverse comodule morphisms.
* `TauCeti.Comodule.matrixCoefficientSubmodule_transport` and
  `TauCeti.Comodule.matrixCoefficientSubalgebra_transport`: coefficient objects are
  invariant under transported coactions.

## References

This is standard matrix-coefficient functoriality for comodules; see Sweedler, *Hopf
Algebras*, Chapter 2. It supplies a prerequisite for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1, "Faithfulness done right", where
faithful representations are characterized by their matrix coefficients generating the
coordinate Hopf algebra.
-/

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]

section Coalgebra

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The matrix coefficient of the image of a vector under a comodule morphism is a matrix
coefficient of the source comodule. -/
theorem matrixCoefficient_mem_set_of_map (f : Hom R C M N) (φ : N →ₗ[R] R) (m : M) :
    matrixCoefficient (R := R) (C := C) φ (f m) ∈
      matrixCoefficientSet (R := R) (C := C) (M := M) := by
  rw [matrixCoefficient_map]
  exact matrixCoefficient_mem_set (R := R) (C := C) (φ.comp f.toLinearMap) m

/-- If `f : M → N` is a surjective comodule morphism, every matrix coefficient of `N` is a
matrix coefficient of `M`. -/
theorem matrixCoefficientSet_subset_of_surjective (f : Hom R C M N)
    (hf : Function.Surjective f) :
    matrixCoefficientSet (R := R) (C := C) (M := N) ⊆
      matrixCoefficientSet (R := R) (C := C) (M := M) := by
  intro c hc
  rcases (mem_matrixCoefficientSet_iff (R := R) (C := C) (M := N) c).mp hc with
    ⟨φ, n, rfl⟩
  rcases hf n with ⟨m, rfl⟩
  exact matrixCoefficient_mem_set_of_map (R := R) (C := C) f φ m

/-- A surjective comodule morphism makes the coefficient submodule of the target contained in
the coefficient submodule of the source. -/
theorem matrixCoefficientSubmodule_le_of_surjective (f : Hom R C M N)
    (hf : Function.Surjective f) :
    matrixCoefficientSubmodule (R := R) (C := C) (M := N) ≤
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  rw [matrixCoefficientSubmodule, Submodule.span_le]
  intro c hc
  exact Submodule.subset_span (matrixCoefficientSet_subset_of_surjective (R := R) (C := C) f hf hc)

/-- Inverse comodule morphisms identify the coefficient sets. -/
theorem matrixCoefficientSet_eq_of_inverse_hom (f : Hom R C M N) (g : Hom R C N M)
    (hfg : ∀ n, f (g n) = n) (hgf : ∀ m, g (f m) = m) :
    matrixCoefficientSet (R := R) (C := C) (M := M) =
      matrixCoefficientSet (R := R) (C := C) (M := N) := by
  apply Set.Subset.antisymm
  · exact matrixCoefficientSet_subset_of_surjective (R := R) (C := C) g
      (fun m => ⟨f m, hgf m⟩)
  · exact matrixCoefficientSet_subset_of_surjective (R := R) (C := C) f
      (fun n => ⟨g n, hfg n⟩)

/-- Inverse comodule morphisms identify the coefficient submodules. -/
theorem matrixCoefficientSubmodule_eq_of_inverse_hom (f : Hom R C M N) (g : Hom R C N M)
    (hfg : ∀ n, f (g n) = n) (hgf : ∀ m, g (f m) = m) :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := N) := by
  rw [matrixCoefficientSubmodule, matrixCoefficientSubmodule,
    matrixCoefficientSet_eq_of_inverse_hom f g hfg hgf]

end Coalgebra

section Algebra

variable [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- A surjective comodule morphism makes the coefficient algebra of the target contained in
the coefficient algebra of the source. -/
theorem matrixCoefficientSubalgebra_le_of_surjective (f : Hom R C M N)
    (hf : Function.Surjective f) :
    matrixCoefficientSubalgebra (R := R) (C := C) (M := N) ≤
      matrixCoefficientSubalgebra (R := R) (C := C) (M := M) := by
  rw [matrixCoefficientSubalgebra, Algebra.adjoin_le_iff]
  intro c hc
  exact Algebra.subset_adjoin (matrixCoefficientSet_subset_of_surjective (R := R) (C := C) f hf hc)

/-- Inverse comodule morphisms identify the coefficient algebras. -/
theorem matrixCoefficientSubalgebra_eq_of_inverse_hom (f : Hom R C M N) (g : Hom R C N M)
    (hfg : ∀ n, f (g n) = n) (hgf : ∀ m, g (f m) = m) :
    matrixCoefficientSubalgebra (R := R) (C := C) (M := M) =
      matrixCoefficientSubalgebra (R := R) (C := C) (M := N) := by
  rw [matrixCoefficientSubalgebra, matrixCoefficientSubalgebra,
    matrixCoefficientSet_eq_of_inverse_hom f g hfg hgf]

end Algebra

section Transport

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N₀ : Type x} [AddCommMonoid N₀] [Module R N₀]

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient set. -/
theorem matrixCoefficientSet_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSet (R := R) (C := C) (M := N₀) =
      matrixCoefficientSet (R := R) (C := C) (M := M) := by
  letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  exact (matrixCoefficientSet_eq_of_inverse_hom
    (R := R) (C := C) (M := M) (N := N₀)
    (transportToHom (R := R) (C := C) (M := M) (N := N₀) e)
    (transportInvHom (R := R) (C := C) (M := M) (N := N₀) e)
    (fun n => e.apply_symm_apply n) (fun m => e.symm_apply_apply m)).symm

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient submodule. -/
theorem matrixCoefficientSubmodule_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSubmodule (R := R) (C := C) (M := N₀) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  rw [matrixCoefficientSubmodule, matrixCoefficientSubmodule, matrixCoefficientSet_transport]

end Transport

section AlgebraTransport

variable [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N₀ : Type x} [AddCommMonoid N₀] [Module R N₀]

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient algebra. -/
theorem matrixCoefficientSubalgebra_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSubalgebra (R := R) (C := C) (M := N₀) =
      matrixCoefficientSubalgebra (R := R) (C := C) (M := M) := by
  letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  rw [matrixCoefficientSubalgebra, matrixCoefficientSubalgebra, matrixCoefficientSet_transport]

end AlgebraTransport

end Comodule

end TauCeti
