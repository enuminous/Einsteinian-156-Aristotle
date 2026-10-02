module

public import Mathlib

/-!
# FS-T08 / FS-T09: algebra of the scalar triplet residual

The source's scalar equations in a triplet `{i, j, k}` have the shape

`R_i = B_i + λ_ij φ_j + λ_ik φ_k + λ_ijk φ_j φ_k`.

We model this over an arbitrary commutative ring (the real-valued case is the
specialisation `R := ℝ`).
-/

@[expose] public section

namespace FieldSpace

variable {R : Type*} [CommRing R]

/-- The generic scalar residual of the source grammar, for one scalar sector `i` in a triplet
`{i, j, k}`: base term, two pair couplings, one three-way coupling. -/
def scalarTripletResidual (base lij lik lijk phij phik : R) : R :=
  base + lij * phij + lik * phik + lijk * phij * phik

/-- **FS-T08** (trilinear null-slice law): the three-way term vanishes as soon as either
participating field vanishes, so the three-way coefficient has no effect on the residual there. -/
theorem trilinear_null_slice (lijk lijk' phij phik : R) (h : phij = 0 ∨ phik = 0) :
    scalarTripletResidual 0 0 0 lijk phij phik = 0 ∧
      ∀ base lij lik : R, scalarTripletResidual base lij lik lijk phij phik =
        scalarTripletResidual base lij lik lijk' phij phik := by
  rcases h with rfl | rfl <;> refine ⟨by simp [scalarTripletResidual], fun _ _ _ => ?_⟩ <;>
    simp [scalarTripletResidual]

/-- Restricting to the slice `φ_k = 0` leaves the `i`–`j` pair residual. -/
theorem restrict_third_zero (base lij lik lijk phij : R) :
    scalarTripletResidual base lij lik lijk phij 0 = base + lij * phij := by
  simp [scalarTripletResidual]

/-- Restricting to the slice `φ_j = 0` leaves the `i`–`k` pair residual. -/
theorem restrict_second_zero (base lij lik lijk phik : R) :
    scalarTripletResidual base lij lik lijk 0 phik = base + lik * phik := by
  simp [scalarTripletResidual]

/-- **FS-T09** (shared-pair overlap consistency): two triplets `{i,j,k}` and `{i,j,l}` with the
same base term and the same `i`–`j` coefficient give the same residual for `φ_i` on the slices
where their respective third fields vanish. -/
theorem shared_pair_overlap_consistency (base lij lik lijk lil lijl phij : R) :
    scalarTripletResidual base lij lik lijk phij 0 =
      scalarTripletResidual base lij lil lijl phij 0 := by
  simp [scalarTripletResidual]

/-- Conversely, the gluing condition is necessary: if the two restricted residuals agree for
all values of `φ_j` (as polynomial functions), then the base terms and the pair coefficients
must coincide. This only needs the ring to contain `0` and `1`. -/
theorem shared_pair_overlap_iff (base base' lij lij' lik lijk lil lijl : R) :
    (∀ phij : R, scalarTripletResidual base lij lik lijk phij 0 =
      scalarTripletResidual base' lij' lil lijl phij 0) ↔ base = base' ∧ lij = lij' := by
  simp only [restrict_third_zero]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [mul_zero, add_zero, mul_one] at h0 h1
    exact ⟨h0, by rw [h0] at h1; exact add_left_cancel h1⟩
  · rintro ⟨rfl, rfl⟩ _
    rfl

/-- Removing the three-way term changes the residual by exactly that term. -/
theorem triple_ablation_difference (base lij lik lijk phij phik : R) :
    scalarTripletResidual base lij lik lijk phij phik -
      scalarTripletResidual base lij lik 0 phij phik = lijk * phij * phik := by
  unfold scalarTripletResidual
  ring

end FieldSpace
