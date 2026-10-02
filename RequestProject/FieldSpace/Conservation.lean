module

public import Mathlib

/-!
# FS-C03: conservation closure for the gauge equations

Every gauge block of the source contains a dynamical equation of the form

`∇_μ F^{μν} = κ_ME J_E^ν + κ_MF φ_F ∇^ν φ_F + κ_MEF Ξ^ν`.

Because `F^{μν}` is antisymmetric, the divergence of the left side vanishes identically
(`∂_ν ∂_μ F^{μν} = 0`). So the right side must be a conserved current. We prove this in flat
coordinates on `ℝⁿ` with a constant diagonal metric `η` (any signature), and derive the
consequence for the scalar term `κ φ ∂^ν φ`: it forces `κ (φ □φ + (∂φ)²) = 0`, i.e.
`κ □(φ²) = 0`, wherever the other currents are conserved. Combined with the scalar equation
`□φ + m² φ + s = 0` this gives the extra constraint `κ ((∂φ)² - m² φ² - φ s) = 0`, which the
source does not list.
-/

@[expose] public section

namespace FieldSpace

open scoped ContDiff

variable {n : ℕ}

/-- Partial derivative along the `μ`-th coordinate of `ℝⁿ`. -/
noncomputable def pd (μ : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single μ 1)

lemma contDiff_pd {f : (Fin n → ℝ) → ℝ} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) (μ : Fin n) :
    ContDiff ℝ k (pd μ f) :=
  (hf.fderiv_right (m := k) le_rfl).clm_apply contDiff_const

lemma differentiable_pd {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (μ : Fin n) :
    Differentiable ℝ (pd μ f) :=
  (contDiff_pd (k := 1) hf μ).differentiable one_ne_zero

/-- Equality of mixed partial derivatives (Schwarz) for `C²` functions. -/
lemma pd_comm {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (μ ν : Fin n) :
    pd ν (pd μ f) = pd μ (pd ν f) := by
  ext x
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
  have key : ∀ a b : Fin n, pd b (pd a f) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single b 1) (Pi.single a 1) := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single a 1)) x (Pi.single b 1) = _
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]))
    _ _

lemma pd_neg (f : (Fin n → ℝ) → ℝ) (μ : Fin n) : pd μ (-f) = -pd μ f := by
  ext x; simp [pd, fderiv_neg]

lemma pd_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin n → ℝ) → ℝ)
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) (μ : Fin n) (x : Fin n → ℝ) :
    pd μ (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, pd μ (g i) x := by
  simp only [pd]
  rw [fderiv_fun_sum (fun i hi => (hg i hi) x)]
  simp

/-- The divergence of the divergence of an antisymmetric `C²` tensor vanishes identically:
`∂_ν ∂_μ F^{μν} = 0`. -/
theorem div_div_antisymm (F : Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hF : ∀ μ ν, ContDiff ℝ 2 (F μ ν)) (hanti : ∀ μ ν, F ν μ = -F μ ν) (x : Fin n → ℝ) :
    ∑ ν, pd ν (fun y => ∑ μ, pd μ (F μ ν) y) x = 0 := by
  have h1 : ∑ ν, pd ν (fun y => ∑ μ, pd μ (F μ ν) y) x =
      ∑ ν, ∑ μ, pd ν (pd μ (F μ ν)) x := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    exact pd_sum _ _ (fun μ _ => differentiable_pd (hF μ ν) μ) ν x
  set S := ∑ ν, ∑ μ, pd ν (pd μ (F μ ν)) x
  have h2 : S = -S := by
    calc S = ∑ ν, ∑ μ, pd μ (pd ν (F μ ν)) x := by
            simp only [S]
            refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
            rw [pd_comm (hF μ ν)]
      _ = ∑ μ, ∑ ν, pd μ (pd ν (F μ ν)) x := Finset.sum_comm
      _ = ∑ ν, ∑ μ, pd ν (pd μ (F ν μ)) x := rfl
      _ = -S := by
            simp only [S, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
            rw [hanti μ ν, pd_neg, pd_neg]
            rfl
  rw [h1]
  linarith

/-- d'Alembertian (or Laplacian) for the constant diagonal metric `η`. -/
noncomputable def box (η : Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ ν, η ν * pd ν (pd ν φ) x

/-- `(∂φ)² = η^{νν} (∂_ν φ)²`. -/
noncomputable def gradSq (η : Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ ν, η ν * pd ν φ x ^ 2

lemma pd_scalar_current {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (J : (Fin n → ℝ) → ℝ)
    (hJ : Differentiable ℝ J) (κ c : ℝ) (ν : Fin n) (x : Fin n → ℝ) :
    pd ν (fun y => κ * c * φ y * pd ν φ y + J y) x =
      κ * c * (pd ν φ x ^ 2 + φ x * pd ν (pd ν φ) x) + pd ν J x := by
  have hφd : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hp := differentiable_pd hφ ν
  show fderiv ℝ (fun y => κ * c * φ y * pd ν φ y + J y) x (Pi.single ν 1) = _
  rw [fderiv_fun_add (by fun_prop : DifferentiableAt ℝ (fun y => κ * c * φ y * pd ν φ y) x) (hJ x),
    fderiv_fun_mul ((hφd x).const_mul (κ * c)) (hp x), fderiv_const_mul (hφd x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, pd]
  ring

/-- **FS-C03 (conservation closure), scalar-current form.** Suppose a gauge field strength
`F^{μν}` (antisymmetric, `C²`) obeys a source-style gauge equation
`∂_μ F^{μν} = κ φ ∂^ν φ + J^ν` with `∂^ν = η^{νν} ∂_ν`, where `J` collects the other currents
and is conserved. Then `κ (φ □φ + (∂φ)²) = 0` everywhere, i.e. `κ □(φ²) = 0`. -/
theorem scalar_current_constraint (η : Fin n → ℝ) (κ : ℝ)
    (F : Fin n → Fin n → (Fin n → ℝ) → ℝ) (hF : ∀ μ ν, ContDiff ℝ 2 (F μ ν))
    (hanti : ∀ μ ν, F ν μ = -F μ ν)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (J : Fin n → (Fin n → ℝ) → ℝ) (hJd : ∀ ν, Differentiable ℝ (J ν))
    (hJ : ∀ x, ∑ ν, pd ν (J ν) x = 0)
    (hEq : ∀ ν x, ∑ μ, pd μ (F μ ν) x = κ * η ν * φ x * pd ν φ x + J ν x) (x : Fin n → ℝ) :
    κ * (φ x * box η φ x + gradSq η φ x) = 0 := by
  have h0 := div_div_antisymm F hF hanti x
  have hfun : ∀ ν, (fun y => ∑ μ, pd μ (F μ ν) y) =
      fun y => κ * η ν * φ y * pd ν φ y + J ν y := fun ν => funext (hEq ν)
  simp only [hfun] at h0
  simp only [pd_scalar_current hφ _ (hJd _), Finset.sum_add_distrib, hJ x, add_zero] at h0
  rw [← h0]
  simp only [box, gradSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- Combining with the scalar equation `□φ + m² φ + s = 0` (where `s` stands for the remaining
source terms, e.g. `λ F_{αβ} F^{αβ}`), every solution of the coupled system must also satisfy
`κ ((∂φ)² - m² φ² - φ s) = 0`. If `κ ≠ 0`, this is an extra equation not present in the
source: `(∂φ)² = m² φ² + φ s`. -/
theorem scalar_current_extra_equation (η : Fin n → ℝ) (κ m2 : ℝ)
    (F : Fin n → Fin n → (Fin n → ℝ) → ℝ) (hF : ∀ μ ν, ContDiff ℝ 2 (F μ ν))
    (hanti : ∀ μ ν, F ν μ = -F μ ν)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (s : (Fin n → ℝ) → ℝ)
    (hscalar : ∀ x, box η φ x + m2 * φ x + s x = 0)
    (J : Fin n → (Fin n → ℝ) → ℝ) (hJd : ∀ ν, Differentiable ℝ (J ν))
    (hJ : ∀ x, ∑ ν, pd ν (J ν) x = 0)
    (hEq : ∀ ν x, ∑ μ, pd μ (F μ ν) x = κ * η ν * φ x * pd ν φ x + J ν x) (hκ : κ ≠ 0)
    (x : Fin n → ℝ) :
    gradSq η φ x = m2 * φ x ^ 2 + φ x * s x := by
  have h := scalar_current_constraint η κ F hF hanti φ hφ J hJd hJ hEq x
  have h' : φ x * box η φ x + gradSq η φ x = 0 := (mul_eq_zero.1 h).resolve_left hκ
  have hb : box η φ x = -(m2 * φ x) - s x := by linarith [hscalar x]
  rw [hb] at h'
  linarith

lemma pd_coord (i ν : Fin n) : pd ν (fun x => x i) = fun _ => if ν = i then 1 else 0 := by
  ext x
  have : fderiv ℝ (fun x : Fin n → ℝ => x i) x = ContinuousLinearMap.proj i :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).fderiv
  simp only [pd, this, ContinuousLinearMap.proj_apply, Pi.single_apply, eq_comm]

/-- A concrete instance of the obstruction. The linear profile `φ = xᵢ` along any direction with
`ηᵢᵢ ≠ 0` solves the massless, source-free scalar equation `□φ = 0`, yet no gauge field `F` and
conserved current `J` can satisfy `∂_μ F^{μν} = κ φ ∂^ν φ + J^ν` with this `φ` when `κ ≠ 0`. -/
theorem linear_profile_obstruction (η : Fin n → ℝ) (i : Fin n) (hη : η i ≠ 0) (κ : ℝ)
    (hκ : κ ≠ 0) :
    box η (fun x => x i) = 0 ∧
    ¬ ∃ (F : Fin n → Fin n → (Fin n → ℝ) → ℝ) (J : Fin n → (Fin n → ℝ) → ℝ),
      (∀ μ ν, ContDiff ℝ 2 (F μ ν)) ∧ (∀ μ ν, F ν μ = -F μ ν) ∧
      (∀ ν, Differentiable ℝ (J ν)) ∧ (∀ x, ∑ ν, pd ν (J ν) x = 0) ∧
      (∀ ν x, ∑ μ, pd μ (F μ ν) x = κ * η ν * x i * pd ν (fun y => y i) x + J ν x) := by
  have hbox : box η (fun x => x i) = 0 := by
    ext x
    simp only [box, pd_coord]
    simp [pd]
  refine ⟨hbox, ?_⟩
  rintro ⟨F, J, hF, hanti, hJd, hJ, hEq⟩
  have hφ : ContDiff ℝ 2 (fun x : Fin n → ℝ => x i) := contDiff_apply ℝ ℝ i
  have h := scalar_current_extra_equation η κ 0 F hF hanti (fun x => x i) hφ 0
    (fun x => by simp [hbox]) J hJd hJ hEq hκ 0
  simp [gradSq, pd_coord] at h
  exact hη h

end FieldSpace
