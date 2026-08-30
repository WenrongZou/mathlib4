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
* `IsLinearTopology (valuation R).integer R` and
  `IsLinearTopology (valuation R).integer (valuation R).integer`, as instances.
-/

@[expose] public section

open Topology ValuativeRel Valuation

namespace IsLinearTopology

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- If a linearly topologized ring `R` embeds into a topological ring `K` as an open subring, then
the topology of `K` is `R`-linear: the images of the open ideals of `R` form a basis of
neighborhoods of zero made of `R`-submodules of `K`. -/
lemma of_isOpenEmbedding [ContinuousAdd R] [IsLinearTopology R R]
    {K : Type*} [CommRing K] [TopologicalSpace K] [ContinuousAdd K] [Algebra R K]
    (h : IsOpenEmbedding (algebraMap R K)) :
    IsLinearTopology R K := by
  rw [isLinearTopology_iff_hasBasis_open_submodule] at *
  rw [← algebraMap.coe_zero (R := R), ← h.isOpenMap.map_nhds_eq h.continuous.continuousAt]
  refine (‹(𝓝 (0 : R)).HasBasis _ _›.map (algebraMap R K)).to_hasBasis (fun I hI ↦ ?_)
    (fun I hI ↦ ⟨I.comap (Algebra.linearMap R K), h.continuous.isOpen_preimage _ hI,
      Set.image_subset_iff.mpr subset_rfl⟩)
  exact ⟨I.map (Algebra.linearMap R K), h.isOpen_iff_image_isOpen.mp hI, subset_rfl⟩

end IsLinearTopology

namespace IsValuativeTopology

variable (R : Type*) [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

variable {R}

/-- The topology on the ring of integers of a ring `R` carrying a valuative topology is linear:
the open balls `Valuation.ltIdeal (valuation R) γ` form a basis of neighborhoods of zero
made of ideals. -/
instance : IsLinearTopology (valuation R).integer (valuation R).integer := by
  refine IsLinearTopology.mk_of_hasBasis _
    (p := fun _ : (ValueGroupWithZero R)ˣ ↦ True) (s := (valuation R).ltIdeal) ?_
  rw [nhds_subtype_eq_comap]
  exact (IsValuativeTopology.hasBasis_nhds_zero R).comap _

/-- The topology on a ring `R` carrying a valuative topology is linear over its ring of integers:
the open balls `Valuation.ltSubmodule (valuation R) γ` form a basis of neighborhoods of zero
made of `(valuation R).integer`-submodules. -/
instance : IsLinearTopology (valuation R).integer R :=
  IsLinearTopology.mk_of_hasBasis _ (p := fun _ : (ValueGroupWithZero R)ˣ ↦ True)
    (s := (valuation R).ltSubmodule) (IsValuativeTopology.hasBasis_nhds_zero R)

end IsValuativeTopology
