/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.FormalGroup.AddInv

@[expose] public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R σ : Type*} {p : ℕ} [CommRing R] [CharP R p] (F G : FormalGroup R)

lemma constCoeff_nsmul {f : F.Point σ} {n : ℕ} (hf : f.val.constantCoeff = 0) :
    constantCoeff (n • f).val = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [add_nsmul, F.add_apply, constantCoeff_subst_eq_zero, hasSubst_of_constantCoeff_zero, ih,
      hf, F.zero_constantCoeff]

lemma nsmul_apply {f : F.Point σ} {n : ℕ} :
    PowerSeries.subst f.val (n • ⟨PowerSeries.X, PowerSeries.HasSubst.X _⟩ : F.Point Unit).val
      = (n • f).val := by
  induction n with
  | zero => simp [← PowerSeries.coe_substAlgHom f.prop]
  | succ k ih =>
    simp_rw [add_nsmul, one_smul, F.add_apply]
    rw [PowerSeries.subst, subst_comp_subst_apply _ f.prop.const]
    · congr! 2 with s
      fin_cases s
      · simp [← ih, PowerSeries.subst]
      · simp [subst, PowerSeries.X]
    · refine hasSubst_of_constantCoeff_zero ?_
      simp [PowerSeries.X, constCoeff_nsmul]

lemma nsmul_toMvPowerSeries {n : ℕ} {i : σ} :
    (n • ⟨X i, PowerSeries.HasSubst.X _⟩ : F.Point σ).val = PowerSeries.toMvPowerSeries i
        (n • ⟨PowerSeries.X, PowerSeries.HasSubst.X _⟩ : F.Point Unit).val := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp_rw [add_nsmul, one_smul, F.add_apply, PowerSeries.toMvPowerSeries_eq_subst,
      PowerSeries.subst]
    rw [subst_comp_subst_apply _ (PowerSeries.HasSubst.X i).const ]
    · congr! 2 with s
      fin_cases s
      · simp [ih, PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.subst]
      · simp [subst, PowerSeries.X]
    · simp [hasSubst_of_constantCoeff_zero, constCoeff_nsmul, PowerSeries.X]

variable [F.IsComm]

def series (n : ℕ) : FormalGroupHom F F where
  toPowerSeries := (n • ⟨PowerSeries.X, PowerSeries.HasSubst.X _⟩ : F.Point Unit).val
  zero_constantCoeff := by simp [PowerSeries.constantCoeff, constCoeff_nsmul, PowerSeries.X]
  hom := by
    have : F.toPowerSeries = (⟨X 0, PowerSeries.HasSubst.X _⟩
        + ⟨X 1, PowerSeries.HasSubst.X _⟩ : F.Point _).val := by
      have : ![X (0 : Fin 2), X 1] = X (R := R) := List.ofFn_inj.mp rfl
      simp [this, ← map_algebraMap_eq_subst_X]
    rw [this, nsmul_apply, nsmul_add, add_apply, ← this]
    congr! 2 with s
    fin_cases s <;> simp [nsmul_toMvPowerSeries]


theorem exist_coeff_pow_ne_zero_iff_ne_zero :
    (∃ n, (F.series p).toPowerSeries.coeff (p ^ n) ≠ 0) ↔ (F.series p).toPowerSeries ≠ 0 :=
  sorry
  -- ⟨fun ⟨n, hn⟩ => ne_of_apply_ne (coeff (p ^ n)) (hn · ),
  --   exist_coeff_pow_ne_zero_of_ne_zero _⟩

/-- the height of a formal group. -/
def height : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq (PowerSeries R)
  if h : (F.series p).toPowerSeries = 0 then ⊤ else
    Nat.find ((F.exist_coeff_pow_ne_zero_iff_ne_zero).mpr h)

end FormalGroup

end
