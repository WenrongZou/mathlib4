/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Renaming variables of multivariate power series

This file establishes the `rename` operation on multivariate power series,
which modifies the set of variables.

## Main declarations

* `MvPowerSeries.rename`
* `MvPowerSeries.renameEquiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommRing R]` `[CommRing S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPowerSeries σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPowerSeries σ α`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

variable {σ τ α R S : Type*} [CommRing R] [CommRing S] [Finite σ] (f : σ → τ) (g : τ → α)
  (φ : R →+* S) (p : MvPowerSeries σ R)

namespace MvPowerSeries

section Rename

lemma HasSubst.rename : HasSubst ((X (R := R)) ∘ f) :=
  hasSubst_of_constantCoeff_zero (by simp)

/-- Rename all the variables in a multivariable power series. -/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R :=
  substAlgHom (HasSubst.rename f)

theorem rename_apply : p.rename f = p.subst (X ∘ f) := by simp [rename]

theorem rename_C (r : R) : rename f (C r) = C r := by simp [rename]

@[simp]
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simp [rename, subst_X (HasSubst.rename _)]

theorem map_rename : map φ (rename f p) = rename f (map φ p) := by
  simp_rw [rename_apply, map_subst (HasSubst.rename _), comp_apply, map_X]
  congr

lemma map_comp_rename : (map φ).comp (rename f).toRingHom = (rename f).toRingHom.comp (map φ) :=
  RingHom.ext fun p ↦ map_rename f _ p

@[simp]
theorem rename_rename [Finite τ] :
    rename g (rename f p) = rename (g ∘ f) p := by
  simp_rw [rename_apply, subst_comp_subst_apply (HasSubst.rename _) (HasSubst.rename _),
    comp_apply, subst_X (HasSubst.rename _)]
  congr

lemma rename_comp_rename [Finite τ] :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
theorem rename_id : rename id = AlgHom.id R (MvPowerSeries σ R) :=
  AlgHom.ext fun p ↦ by simp [rename, ← map_algebraMap_eq_subst_X]

lemma rename_id_apply : rename id p = p := by
  simp

theorem rename_monomial (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  rw [rename_apply, subst_monomial (HasSubst.rename _), monomial_eq',
    Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero (X _)) (fun n i₁ i₂ => pow_add _ _ _)]
  rfl

theorem _root_.MvPowerSeries.monomial_mapDomain {x : σ →₀ ℕ} :
    monomial (x.mapDomain f) (1 : R) = x.prod fun s e ↦ X (f s) ^ e := by
  simp [← rename_monomial, rename_apply, subst_monomial (HasSubst.rename _)]

section Coeff

@[simp]
theorem coeff_rename_mapDomain (hf : Function.Injective f) (d : σ →₀ ℕ) :
    coeff (d.mapDomain f) (rename f p) = coeff d p := by
  rw [rename_apply, coeff_subst (HasSubst.rename _), finsum_eq_single _ d]
  · simp_rw [comp_apply, ← monomial_mapDomain, coeff_monomial_same, smul_eq_mul, mul_one]
  intro x hx
  simp_rw [comp_apply, ← monomial_mapDomain, coeff_monomial_ne
    (fun h => hx.symm (Finsupp.mapDomain_injective hf h)), smul_eq_mul, mul_zero]

@[simp]
theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    (rename f φ).coeff (d.embDomain f) = φ.coeff d := by
  rw [Finsupp.embDomain_eq_mapDomain f, coeff_rename_mapDomain _ _ f.injective]

theorem coeff_rename_eq_zero (φ : MvPowerSeries σ R) (d : τ →₀ ℕ)
    (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
  rw [rename_apply, coeff_subst (HasSubst.rename _), finsum_eq_zero_of_forall_eq_zero]
  intro u
  by_cases hu : u.mapDomain f = d
  · rw [h _ hu, zero_smul]
  simp_rw [comp_apply, ← monomial_mapDomain, coeff_monomial_ne (Ne.symm hu), smul_eq_mul, mul_zero]

theorem coeff_rename_ne_zero (f : σ → τ) (φ : MvPowerSeries σ R) (d : τ →₀ ℕ)
    (h : (rename f φ).coeff d ≠ 0) : ∃ u : σ →₀ ℕ, u.mapDomain f = d ∧ φ.coeff u ≠ 0 := by
  contrapose! h
  apply coeff_rename_eq_zero _ _ _ h

@[simp]
theorem constantCoeff_rename {τ : Type*} (f : σ → τ) (φ : MvPowerSeries σ R) :
    constantCoeff (rename f φ) = constantCoeff φ := by
  classical
  rw [rename_apply, constantCoeff_subst (HasSubst.rename _), finsum_eq_single _ 0]
  · simp
  intro d hd
  simp only [comp_apply, ← monomial_mapDomain, smul_eq_mul]
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial_ne, mul_zero]
  intro h
  have h_eq : Finsupp.mapDomain f d = 0 := h.symm

  -- Prove d = 0 to contradict hd
  apply hd
  ext s

  -- Evaluate the mapped Finsupp at the target point `f s`
  have h_eval : (Finsupp.mapDomain f d) (f s) = 0 := by
    rw [h_eq]
    rfl

  -- Expand the definition of mapDomain evaluation into a Finset sum
  have h_sum : (d.support.filter (fun x ↦ f x = f s)).sum (fun x ↦ d x) = 0 := by
    simp only [Finset.sum_eq_zero_iff, Finset.mem_filter, mem_support_iff, ne_eq, and_imp]
    intro i hi heq
    simp only [← heq] at h_eval
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum] at h_eval
    obtain h' := (Finset.sum_eq_zero_iff_of_nonneg (by simp)).mp h_eval

    have : ∀ a₁ b, (Finsupp.single (f a₁) b) (f i) = 0 := by
      obtain h' := (Finset.sum_eq_zero_iff_of_nonneg (by simp)).mp h_eval

      sorry
    -- rw [← Finsupp.mapDomain_apply]
    -- exact h_eval
    sorry
  -- In ℕ, a sum is 0 if and only if every individual term is 0.
  -- We split by whether `s` is actually in the support of `d`.
  by_cases hs : s ∈ d.support

  · -- Case 1: `s` is in the support.
    -- It must also be in our filtered sum because f s = f s.
    have hs_in_filter : s ∈ d.support.filter (fun x ↦ f x = f s) := by
      rw [Finset.mem_filter]
      exact ⟨hs, rfl⟩

    -- Extract the specific term `d s` from the sum being 0
    exact Finset.sum_eq_zero_iff.mp h_sum s hs_in_filter

  · -- Case 2: `s` is not in the support.
    -- By definition of Finsupp, its value is 0.
    simpa using notMem_support_iff.mp hs
  -- refine Finsupp.ne_iff.mpr ?_
  -- by_contra! hc
  -- simp only [coe_zero, Pi.zero_apply] at hc
  -- have : d = 0 := by
  --   sorry
  -- simp [Finsupp.mapDomain]
  -- exact (fun h => hd.symm (Finsupp.mapDomain_injective hf h))


  -- sorry
  -- apply φ.induction_on
  -- · intro a
  --   simp only [constantCoeff_C, rename_C]
  -- · intro p q hp hq
  --   simp only [hp, hq, map_add]
  -- · intro p n hp
  --   simp only [hp, rename_X, constantCoeff_X, map_mul]

end Coeff

section Support

theorem support_rename_of_injective {p : MvPowerSeries σ R} {f : σ → τ} [DecidableEq τ]
    (h : Function.Injective f) :
    (rename f p).support = Set.image (Finsupp.mapDomain f) p.support := by
  sorry
  -- rw [rename_eq]
  -- exact Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

end Support

theorem rename_injective (hf : Function.Injective f) :
    Function.Injective (rename f : MvPowerSeries σ R → MvPowerSeries τ R) := by
  intro p q h
  ext d
  simp_rw [← coeff_rename_mapDomain _ _ hf d, h]

theorem rename_leftInverse {f : σ → τ} {g : τ → σ} [Finite τ] (hf : Function.LeftInverse f g) :
    Function.LeftInverse (rename f (R := R)) (rename g) :=
  fun x => by simp [hf.comp_eq_id]

theorem rename_rightInverse {f : σ → τ} {g : τ → σ} [Finite τ] (hf : Function.RightInverse f g) :
    Function.RightInverse (rename f (R := R)) (rename g) := rename_leftInverse hf

theorem rename_surjective (f : σ → τ) [Finite τ] (hf : Function.Surjective f) :
    Function.Surjective (rename f (R := R)) :=
  let ⟨_, hf⟩ := hf.hasRightInverse; rename_rightInverse hf |>.surjective

section

variable {f : σ → τ} (hf : Function.Injective f)

instance {i : τ} : Decidable (i ∈ range f) := by
  exact Classical.propDecidable (i ∈ range f)

lemma HasSubst.killCompl : HasSubst <| fun i => if h : i ∈ Set.range f
    then X <| (Equiv.ofInjective f hf).symm ⟨i, h⟩ else (0 : MvPowerSeries σ R) where
  const_coeff s := by split_ifs with h <;> simp
  coeff_zero d := Set.Finite.subset ((finite_range_iff hf).mpr inferInstance) fun x hx => by
    by_contra hc
    simp [mem_range, ne_eq, mem_setOf_eq, dif_neg hc] at hx

open Classical in
/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
  `MvPowerSeries.killCompl hf` is the `AlgHom` from `R⟦τ⟧` to `R⟦σ⟧` that is left inverse to
  `rename f : R⟦σ⟧ → R⟦τ⟧` and sends the variables in the complement of the range of `f` to `0`. -/
def killCompl : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.killCompl hf)

theorem killCompl_C (r : R) : killCompl hf (C r) = C r := by simp [killCompl]

theorem killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _ := by
  ext p : 1
  simp [killCompl, rename, subst_comp_subst_apply (HasSubst.rename _) (HasSubst.killCompl hf),
    comp_apply, subst_X (HasSubst.killCompl _), ← map_algebraMap_eq_subst_X]

@[simp]
theorem killCompl_rename_app : killCompl hf (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p

lemma killCompl_map (φ : R →+* S) (q : MvPowerSeries τ R) :
    (q.map φ).killCompl hf = (q.killCompl hf).map φ := by
  simp only [killCompl, mem_range, substAlgHom_apply, map_subst (HasSubst.killCompl _)]
  congr
  ext i : 1
  by_cases h : i ∈ Set.range f
  · simp [dif_pos h]
  simp [dif_neg h]

end

section

variable (R) [Finite τ] [Finite α]

/-- `MvPowerSeries.rename e` is an equivalence when `e` is. -/
@[simps apply]
def renameEquiv (f : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id_apply]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id_apply] }

@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl

@[simp]
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext <| by simp

end

end Rename

-- section Coeff

-- @[simp]
-- theorem coeff_rename_mapDomain (f : σ → τ) (hf : Injective f) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
--     (rename f φ).coeff (d.mapDomain f) = φ.coeff d := by
--   classical
--   apply φ.induction_on' (P := fun ψ => coeff (Finsupp.mapDomain f d) ((rename f) ψ) = coeff d ψ)
--   -- Lean could no longer infer the motive
--   · intro u r
--     rw [rename_monomial, coeff_monomial, coeff_monomial]
--     simp only [(Finsupp.mapDomain_injective hf).eq_iff]
--   · intros
--     simp only [*, map_add, coeff_add]

-- @[simp]
-- theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
--     (rename f φ).coeff (d.embDomain f) = φ.coeff d := by
--   rw [Finsupp.embDomain_eq_mapDomain f, coeff_rename_mapDomain f f.injective]

-- theorem coeff_rename_eq_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
--     (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
--   classical
--   rw [rename_eq, ← notMem_support_iff]
--   intro H
--   replace H := mapDomain_support H
--   rw [Finset.mem_image] at H
--   obtain ⟨u, hu, rfl⟩ := H
--   specialize h u rfl
--   rw [Finsupp.mem_support_iff] at hu
--   contradiction

-- theorem coeff_rename_ne_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
--     (h : (rename f φ).coeff d ≠ 0) : ∃ u : σ →₀ ℕ, u.mapDomain f = d ∧ φ.coeff u ≠ 0 := by
--   contrapose! h
--   apply coeff_rename_eq_zero _ _ _ h

-- @[simp]
-- theorem constantCoeff_rename {τ : Type*} (f : σ → τ) (φ : MvPolynomial σ R) :
--     constantCoeff (rename f φ) = constantCoeff φ := by
--   apply φ.induction_on
--   · intro a
--     simp only [constantCoeff_C, rename_C]
--   · intro p q hp hq
--     simp only [hp, hq, map_add]
--   · intro p n hp
--     simp only [hp, rename_X, constantCoeff_X, map_mul]

-- end Coeff

-- section Support

-- theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} [DecidableEq τ]
--     (h : Function.Injective f) :
--     (rename f p).support = Finset.image (Finsupp.mapDomain f) p.support := by
--   rw [rename_eq]
--   exact Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

-- end Support

end MvPowerSeries
