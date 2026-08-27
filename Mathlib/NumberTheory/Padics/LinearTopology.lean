/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# `ℤ_[p]` is the ring of integers of `ℚ_[p]`, and both have a linear topology

## Main results

* `PadicInt.integers`: `ℤ_[p]` is a ring of integers of the valuative relation on `ℚ_[p]`,
  in the sense of `Valuation.Integers`.
* `IsLinearTopology ℤ_[p] ℚ_[p]` and `IsLinearTopology ℤ_[p] ℤ_[p]`, as instances.

## Implementation details

`ℤ_[p]` is *not* definitionally equal to `(ValuativeRel.valuation ℚ_[p]).integer`: the former is
defined by `‖·‖ ≤ 1` and the latter by `ValuativeRel.valuation ℚ_[p] · ≤ 1`. So the instances
below cannot be obtained by `inferInstanceAs` from the ones on `(valuation ℚ_[p]).integer`, and
are instead deduced from `PadicInt.integers` through
`Valuation.Integers.isLinearTopology` and `Valuation.Integers.isLinearTopology_self`, which only
require `ℤ_[p]` to be *propositionally* the ring of integers.
-/

public section

open ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

/-- `ℤ_[p]` is a ring of integers of the valuative relation on `ℚ_[p]`. -/
lemma integers : Valuation.Integers (ValuativeRel.valuation ℚ_[p]) ℤ_[p] where
  hom_inj _ _ := PadicInt.ext
  map_le_one x := Padic.valuation_le_one_iff_norm_le_one.mpr x.2
  exists_of_le_one {r} hr := ⟨⟨r, Padic.valuation_le_one_iff_norm_le_one.mp hr⟩, rfl⟩

/-- The topology of `ℚ_[p]` is linear over `ℤ_[p]`. -/
instance : IsLinearTopology ℤ_[p] ℚ_[p] :=
  integers.isLinearTopology

/-- The topology of `ℤ_[p]` is linear. -/
instance : IsLinearTopology ℤ_[p] ℤ_[p] :=
  integers.isLinearTopology_self isOpenEmbedding_coe.isInducing

end PadicInt
