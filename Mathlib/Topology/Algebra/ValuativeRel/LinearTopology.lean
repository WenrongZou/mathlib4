/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Valuative topologies are linear
We show that the topology of a ring `R` carrying a valuative topology is linear over the ring of
integers `(valuation R).integer`, both as a topology on `R` and as a topology on the ring of
integers itself: in both cases the open balls form a basis of neighborhoods of zero made of
submodules.
## Main results
* `IsLinearTopology.of_isOpenEmbedding`: if a linearly topologized ring `R` embeds into a
  topological ring `K` as an open subring, then the topology of `K` is `R`-linear.
* `IsLinearTopology.of_isInducing`: a linear topology can be pulled back along a linear map
  inducing the topology of its source.
* `IsLinearTopology (valuation R).integer R` and
  `IsLinearTopology (valuation R).integer (valuation R).integer`, as instances.
-/

@[expose] public section

open Topology ValuativeRel Valuation

namespace IsLinearTopology

section Inducing

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- If the topology of `N` is `R`-linear and if `f : M →ₗ[R] N` induces the topology of `M`,
then the topology of `M` is `R`-linear: the preimages of the `R`-submodules of `N` form a basis
of neighborhoods of zero made of `R`-submodules of `M`. -/
lemma of_isInducing [IsLinearTopology R N] (f : M →ₗ[R] N) (hf : IsInducing f) :
    IsLinearTopology R M := by
  have hb := (hasBasis_submodule R).comap f
  rw [← map_zero f, ← hf.nhds_eq_comap] at hb
  exact .mk_of_hasBasis R (s := fun P : Submodule R N ↦ P.comap f) hb

end Inducing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- If a linearly topologized ring `R` embeds into a topological ring `K` as an open subring, then
the topology of `K` is `R`-linear: the images of the open ideals of `R` form a basis of
neighborhoods of zero made of `R`-submodules of `K`. -/
lemma of_isOpenEmbedding [ContinuousAdd R] [IsLinearTopology R R]
    {K : Type*} [CommRing K] [TopologicalSpace K] [ContinuousAdd K] [Algebra R K]
    (h : IsOpenEmbedding (algebraMap R K)) : IsLinearTopology R K := by
  rw [isLinearTopology_iff_hasBasis_open_submodule] at *
  rw [← algebraMap.coe_zero (R := R), ← h.isOpenMap.map_nhds_eq h.continuous.continuousAt]
  refine (‹(𝓝 (0 : R)).HasBasis _ _›.map _).to_hasBasis (fun I hI ↦ ?_) fun I hI ↦ ?_
  · exact ⟨I.map (Algebra.linearMap R K), h.isOpen_iff_image_isOpen.mp hI, subset_rfl⟩
  · exact ⟨I.comap (Algebra.linearMap R K), h.continuous.isOpen_preimage _ hI,
      Set.image_subset_iff.mpr subset_rfl⟩

variable (R : Type*) [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

instance : IsLinearTopology (valuation R).integer R :=
  .mk_of_hasBasis _ (s := (valuation R).ltSubmodule) (p := fun _ ↦ True)
    <| IsValuativeTopology.hasBasis_nhds_zero R

instance : IsLinearTopology (valuation R).integer (valuation R).integer :=
  .of_isInducing ⟨⟨Subtype.val, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ IsInducing.subtypeVal

end IsLinearTopology
