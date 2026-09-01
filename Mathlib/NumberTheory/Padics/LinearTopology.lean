/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# The topologies of `ℚ_[p]` and `ℤ_[p]` are `ℤ_[p]`-linear

## Main results

* `PadicInt.integers`: `ℤ_[p]` is a ring of integers of the valuative relation on `ℚ_[p]`, in the
  sense of `Valuation.Integers`.
* `IsLinearTopology ℤ_[p] ℚ_[p]` and `IsLinearTopology ℤ_[p] ℤ_[p]`, as instances.

## Implementation details

`ℤ_[p]` is *not* definitionally equal to `(ValuativeRel.valuation ℚ_[p]).integer`: the former is
defined by `‖·‖ ≤ 1`, the latter by `ValuativeRel.valuation ℚ_[p] · ≤ 1`. So these instances
cannot be obtained by `inferInstanceAs` from the ones on `(valuation ℚ_[p]).integer`, and are
instead deduced from `PadicInt.integers` through `Valuation.Integers.isLinearTopology` and
`Valuation.Integers.isLinearTopology_self`, which only need `ℤ_[p]` to be *propositionally* the
ring of integers.
-/

@[expose] public section

open ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

/-- `ℤ_[p]` is a ring of integers of the valuative relation on `ℚ_[p]`. -/
lemma integers : Valuation.Integers (ValuativeRel.valuation ℚ_[p]) ℤ_[p] where
  hom_inj _ _ := PadicInt.ext
  map_le_one x := Padic.valuation_le_one_iff_norm_le_one.mpr x.2
  exists_of_le_one {r} hr := ⟨⟨r, Padic.valuation_le_one_iff_norm_le_one.mp hr⟩, rfl⟩

/-- The valuative relation on `ℤ_[p]`, pulled back from `ℚ_[p]` along the inclusion. -/
noncomputable instance : ValuativeRel ℤ_[p] :=
  .ofValuation ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p]))

instance : ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p])).Compatible :=
  ⟨fun _ _ ↦ Iff.rfl⟩

/-- `ℤ_[p]` is its own ring of integers for its `p`-adic valuative relation. -/
instance : ValuativeRel.IsIntegerRing ℤ_[p] :=
  .of_forall_smul_one_vle_one fun x ↦ by
    rw [smul_eq_mul, mul_one,
      Valuation.vle_one_iff ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p]))]
    exact Padic.mulValuation_le_one_iff_norm_le_one.mpr x.2

/-- The valuative relation on `ℤ_[p]` is the restriction of the one on `ℚ_[p]`. -/
instance : ValuativeExtension ℤ_[p] ℚ_[p] where
  vle_iff_vle _ _ := Iff.rfl

-- /-- The topology of `ℚ_[p]` is `ℤ_[p]`-linear. -/
set_option trace.Meta.synthInstance true in
instance : IsLinearTopology ℤ_[p] ℚ_[p] := inferInstance
  -- integers.isLinearTopology

/-- The `p`-adic topology of `ℤ_[p]` is the topology of its valuative relation. -/
instance : IsValuativeTopology ℤ_[p] := by
  refine IsValuativeTopology.of_mem_nhds_zero_iff_vle
    ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p])) fun {s} ↦ ?_
  rw [Metric.mem_nhds_iff]
  have h1p : (1 : ℝ) < p := mod_cast hp.out.one_lt
  constructor
  · -- A metric ball `‖·‖ < ε` contains the valuation ball of radius `v (p ^ n)` for large `n`.
    rintro ⟨ε, hε, hball⟩
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1p)
    have ha0 : (p : ℤ_[p]) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    have hnorm : ‖(p : ℤ_[p]) ^ n‖ < ε := by simpa [norm_pow, PadicInt.norm_p] using hn
    refine ⟨Units.mk0 (Valuation.restrict _ ((p : ℤ_[p]) ^ n)) (by simpa using ha0),
      fun z hz ↦ hball (mem_ball_zero_iff.mpr ?_)⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
    rw [PadicInt.norm_def]
    exact ((Padic.norm_lt_norm_iff_mulValuation_lt
      (PadicInt.coe_ne_zero.mpr ha0)).mpr hz).trans hnorm
  · -- Conversely, a valuation ball `v · < γ` is the metric ball of radius `p ^ log γ`.
    rintro ⟨γ, hγ⟩
    refine ⟨p ^ WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val),
      zpow_pos (by positivity) _, fun z hz ↦ hγ ?_⟩
    rw [mem_ball_zero_iff, PadicInt.norm_def, Padic.norm_lt_zpow_iff_mulValuation_lt_exp,
      WithZero.exp_log (by simp)] at hz
    simpa [Valuation.restrict_lt_iff_lt_embedding] using hz

-- /-- The topology of `ℤ_[p]` is linear. -/
set_option trace.Meta.synthInstance true in
instance : IsLinearTopology ℤ_[p] ℤ_[p] := inferInstance

end PadicInt
