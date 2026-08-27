/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# `ℤ_[p]` is the valuation ring of `ℚ_[p]`, and both have a linear topology

## Main results

* `(ValuationRing.valuation ℤ_[p] ℚ_[p]).Compatible`: the valuation that `ℤ_[p]` induces on its
  fraction field agrees with the valuative relation on `ℚ_[p]`.
* `PadicInt.integers`: `ℤ_[p]` is a ring of integers of the valuative relation on `ℚ_[p]`, in the
  sense of `Valuation.Integers`.
* `IsLinearTopology ℤ_[p] ℚ_[p]` and `IsLinearTopology ℤ_[p] ℤ_[p]`.

## Implementation details

`ℤ_[p]` is *not* definitionally equal to `(ValuativeRel.valuation ℚ_[p]).integer`: the former is
defined by `‖·‖ ≤ 1` and the latter by `ValuativeRel.valuation ℚ_[p] · ≤ 1`. So these instances
cannot be obtained by `inferInstanceAs` from the ones on `(valuation ℚ_[p]).integer`.

Instead, everything goes through the typeclass-level characterization of `ℤ_[p]` as a valuation
ring with fraction field `ℚ_[p]`: the instances `ValuationRing ℤ_[p]` and
`IsFractionRing ℤ_[p] ℚ_[p]` already exist, so the only thing to provide is the compatibility of
the induced valuation with the valuative relation, after which
`ValuationRing.isLinearTopology` applies by typeclass inference.
-/

public section

open ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

/-- The valuation induced by the valuation ring `ℤ_[p]` on its fraction field is compatible with
the valuative relation of `ℚ_[p]`. -/
instance : (ValuationRing.valuation ℤ_[p] ℚ_[p]).Compatible :=
  .of_isEquiv <| Valuation.isEquiv_iff_val_le_one.mpr fun {x} ↦ by
      rw [Padic.valuation_le_one_iff_norm_le_one, ← Valuation.mem_integer_iff,
        ValuationRing.mem_integer_iff]
      exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.2⟩

/-- `ℤ_[p]` is a ring of integers of the valuative relation on `ℚ_[p]`. -/
lemma integers : Valuation.Integers (ValuativeRel.valuation ℚ_[p]) ℤ_[p] :=
  (ValuationRing.integers ℤ_[p] ℚ_[p]).of_compatible

/-- The topology of `ℤ_[p]` is linear. -/
instance : IsLinearTopology ℤ_[p] ℤ_[p] :=
  ValuationRing.isLinearTopology_self isOpenEmbedding_coe.isInducing

-- `IsLinearTopology ℤ_[p] ℚ_[p]` is found by typeclass inference,
-- through `ValuationRing.isLinearTopology`.
example : IsLinearTopology ℤ_[p] ℚ_[p] := inferInstance

end PadicInt
