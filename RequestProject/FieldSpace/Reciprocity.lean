module

public import RequestProject.FieldSpace.Basic

/-!
# FS-C02: master-action reciprocity for a scalar triplet

In a three-scalar triplet `{x, y, z}` the source writes the non-derivative part of the
three scalar equations as

* `R_x = m_x φ_x + λ_xy φ_y + λ_xz φ_z + λ_xyz φ_y φ_z`
* `R_y = m_y φ_y + λ_yx φ_x + λ_yz φ_z + λ_yxz φ_x φ_z`
* `R_z = m_z φ_z + λ_zx φ_x + λ_zy φ_y + λ_zxy φ_x φ_y`

with nine independently named coupling symbols. If the equations are the Euler–Lagrange
equations of one action `∫ (½ ∑ (∂φ)² - V(φ))`, then `R_i = ∂V/∂φ_i` for one potential `V`.
We prove that such a potential exists **if and only if** the couplings are reciprocal:
`λ_xy = λ_yx`, `λ_xz = λ_zx`, `λ_yz = λ_zy` and `λ_xyz = λ_yxz = λ_zxy`.
-/

@[expose] public section

namespace FieldSpace

/-- The coupling symbols of one three-scalar triplet as written in the source:
three mass terms, six directional pair couplings and three three-way couplings. -/
structure ScalarTripletCouplings where
  mx : ℝ
  my : ℝ
  mz : ℝ
  lxy : ℝ
  lxz : ℝ
  lyx : ℝ
  lyz : ℝ
  lzx : ℝ
  lzy : ℝ
  txyz : ℝ
  tyxz : ℝ
  tzxy : ℝ

namespace ScalarTripletCouplings

variable (c : ScalarTripletCouplings)

/-- Non-derivative part of the `φ_x` equation. -/
def resX (x y z : ℝ) : ℝ := c.mx * x + c.lxy * y + c.lxz * z + c.txyz * y * z
/-- Non-derivative part of the `φ_y` equation. -/
def resY (x y z : ℝ) : ℝ := c.my * y + c.lyx * x + c.lyz * z + c.tyxz * x * z
/-- Non-derivative part of the `φ_z` equation. -/
def resZ (x y z : ℝ) : ℝ := c.mz * z + c.lzx * x + c.lzy * y + c.tzxy * x * y

/-- `V` is a potential for the triplet: its three partial derivatives are the three residuals. -/
def IsPotential (V : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x y z : ℝ, HasDerivAt (fun s => V s y z) (c.resX x y z) x ∧
    HasDerivAt (fun s => V x s z) (c.resY x y z) y ∧
    HasDerivAt (fun s => V x y s) (c.resZ x y z) z

/-- Reciprocity of the couplings. -/
def Reciprocal : Prop :=
  c.lxy = c.lyx ∧ c.lxz = c.lzx ∧ c.lyz = c.lzy ∧ c.txyz = c.tyxz ∧ c.txyz = c.tzxy

end ScalarTripletCouplings

lemma hasDerivAt_quadratic (a b d s : ℝ) :
    HasDerivAt (fun t : ℝ => a * t ^ 2 + b * t + d) (2 * a * s + b) s := by
  have := (((hasDerivAt_id s).pow 2).const_mul a).add ((hasDerivAt_id s).const_mul b)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this.add_const d

lemma eq_of_hasDerivAt_affine {f : ℝ → ℝ} {a b : ℝ} (h : ∀ s, HasDerivAt f (a * s + b) s)
    (s : ℝ) : f s = f 0 + a / 2 * s ^ 2 + b * s := by
  set g : ℝ → ℝ := fun t => f t - (a / 2 * t ^ 2 + b * t) with hg
  have hd : ∀ t, HasDerivAt g 0 t := fun t => by
    have := (h t).sub (hasDerivAt_quadratic (a / 2) b 0 t)
    convert this using 1
    · ext u; simp [hg]
    · ring
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0
  simp only [hg] at this
  linarith

namespace ScalarTripletCouplings

variable {c : ScalarTripletCouplings}

lemma potential_eq_x {V : ℝ → ℝ → ℝ → ℝ} (hV : c.IsPotential V) (x y z : ℝ) :
    V x y z = V 0 y z + c.mx / 2 * x ^ 2 + (c.lxy * y + c.lxz * z + c.txyz * y * z) * x :=
  eq_of_hasDerivAt_affine (f := fun s => V s y z) (fun s => by
    convert (hV s y z).1 using 1; simp [resX]; ring) x

lemma potential_eq_y {V : ℝ → ℝ → ℝ → ℝ} (hV : c.IsPotential V) (x y z : ℝ) :
    V x y z = V x 0 z + c.my / 2 * y ^ 2 + (c.lyx * x + c.lyz * z + c.tyxz * x * z) * y :=
  eq_of_hasDerivAt_affine (f := fun s => V x s z) (fun s => by
    convert (hV x s z).2.1 using 1; simp [resY]; ring) y

/-- A potential forces reciprocity. -/
theorem reciprocal_of_potential {V : ℝ → ℝ → ℝ → ℝ} (hV : c.IsPotential V) : c.Reciprocal := by
  -- `∂_y` of the decomposition `V = V(0,y,z) + …` along `x`
  have hy : ∀ x y z : ℝ, c.resY x y z = c.resY 0 y z + (c.lxy + c.txyz * z) * x := by
    intro x y z
    have h1 := (hV x y z).2.1
    have h2 : HasDerivAt (fun s => V 0 s z + c.mx / 2 * x ^ 2 +
        (c.lxy * s + c.lxz * z + c.txyz * s * z) * x)
        (c.resY 0 y z + (c.lxy + c.txyz * z) * x) y := by
      have := (((((hasDerivAt_id y).const_mul c.lxy).add_const (c.lxz * z)).add
        (((hasDerivAt_id y).const_mul c.txyz).mul_const z)).mul_const x)
      convert ((hV 0 y z).2.1.add_const (c.mx / 2 * x ^ 2)).add this using 1
      simp
    have heq : (fun s => V x s z) = fun s => V 0 s z + c.mx / 2 * x ^ 2 +
        (c.lxy * s + c.lxz * z + c.txyz * s * z) * x := by
      ext s; exact potential_eq_x hV x s z
    rw [heq] at h1
    exact h1.unique h2
  have hz : ∀ x y z : ℝ, c.resZ x y z = c.resZ 0 y z + (c.lxz + c.txyz * y) * x := by
    intro x y z
    have h1 := (hV x y z).2.2
    have h2 : HasDerivAt (fun s => V 0 y s + c.mx / 2 * x ^ 2 +
        (c.lxy * y + c.lxz * s + c.txyz * y * s) * x)
        (c.resZ 0 y z + (c.lxz + c.txyz * y) * x) z := by
      have := ((((hasDerivAt_id z).const_mul c.lxz).const_add (c.lxy * y)).add
        ((hasDerivAt_id z).const_mul (c.txyz * y))).mul_const x
      convert ((hV 0 y z).2.2.add_const (c.mx / 2 * x ^ 2)).add this using 1
      simp
    have heq : (fun s => V x y s) = fun s => V 0 y s + c.mx / 2 * x ^ 2 +
        (c.lxy * y + c.lxz * s + c.txyz * y * s) * x := by
      ext s; exact potential_eq_x hV x y s
    rw [heq] at h1
    exact h1.unique h2
  have hz' : ∀ x y z : ℝ, c.resZ x y z = c.resZ x 0 z + (c.lyz + c.tyxz * x) * y := by
    intro x y z
    have h1 := (hV x y z).2.2
    have h2 : HasDerivAt (fun s => V x 0 s + c.my / 2 * y ^ 2 +
        (c.lyx * x + c.lyz * s + c.tyxz * x * s) * y)
        (c.resZ x 0 z + (c.lyz + c.tyxz * x) * y) z := by
      have := ((((hasDerivAt_id z).const_mul c.lyz).const_add (c.lyx * x)).add
        ((hasDerivAt_id z).const_mul (c.tyxz * x))).mul_const y
      convert ((hV x 0 z).2.2.add_const (c.my / 2 * y ^ 2)).add this using 1
      simp
    have heq : (fun s => V x y s) = fun s => V x 0 s + c.my / 2 * y ^ 2 +
        (c.lyx * x + c.lyz * s + c.tyxz * x * s) * y := by
      ext s; exact potential_eq_y hV x y s
    rw [heq] at h1
    exact h1.unique h2
  have a1 := hy 1 0 0
  have a2 := hy 1 0 1
  have a3 := hz 1 0 0
  have a4 := hz 1 1 0
  have a5 := hz' 0 1 0
  simp only [resY, resZ] at a1 a2 a3 a4 a5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The explicit cubic potential generated by reciprocal couplings. -/
noncomputable def masterPotential (c : ScalarTripletCouplings) (x y z : ℝ) : ℝ :=
  c.mx / 2 * x ^ 2 + c.my / 2 * y ^ 2 + c.mz / 2 * z ^ 2 +
    c.lxy * x * y + c.lxz * x * z + c.lyz * y * z + c.txyz * x * y * z

/-- Reciprocal couplings come from a potential, namely `masterPotential`. -/
theorem masterPotential_isPotential (h : c.Reciprocal) : c.IsPotential c.masterPotential := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  intro x y z
  refine ⟨?_, ?_, ?_⟩
  · convert hasDerivAt_quadratic (c.mx / 2) (c.lxy * y + c.lxz * z + c.txyz * y * z)
      (c.my / 2 * y ^ 2 + c.mz / 2 * z ^ 2 + c.lyz * y * z) x using 1
    · ext s; simp [masterPotential]; ring
    · simp [resX]; ring
  · convert hasDerivAt_quadratic (c.my / 2) (c.lxy * x + c.lyz * z + c.txyz * x * z)
      (c.mx / 2 * x ^ 2 + c.mz / 2 * z ^ 2 + c.lxz * x * z) y using 1
    · ext s; simp [masterPotential]; ring
    · simp [resY, h1, h4]; ring
  · convert hasDerivAt_quadratic (c.mz / 2) (c.lxz * x + c.lyz * y + c.txyz * x * y)
      (c.mx / 2 * x ^ 2 + c.my / 2 * y ^ 2 + c.lxy * x * y) z using 1
    · ext s; simp [masterPotential]; ring
    · simp [resZ, h2, h3, h5]; ring

/-- **FS-C02** (master-action reciprocity), for a three-scalar triplet: the non-derivative
parts of the three scalar equations are the partial derivatives of a single potential
if and only if the couplings are reciprocal. -/
theorem exists_potential_iff_reciprocal :
    (∃ V : ℝ → ℝ → ℝ → ℝ, c.IsPotential V) ↔ c.Reciprocal :=
  ⟨fun ⟨_, hV⟩ => reciprocal_of_potential hV, fun h => ⟨_, masterPotential_isPotential h⟩⟩

end ScalarTripletCouplings

/-! ## FS-C04: what reciprocity saves on the scalar sectors

The source names pair couplings directionally (`λ_ij` in the `φ_i` equation, `λ_ji` in the
`φ_j` equation) and three-way couplings by their equation (`λ_ijk`, `λ_jik`, `λ_kij` in a
three-scalar triplet). -/

open Sector

/-- The eight scalar sectors. -/
def scalarSectors : Finset Sector := Finset.univ.filter (fun s => s.kind = .scalar)

/-- Directional scalar–scalar pair symbols `λ_ij`, `i ≠ j`. -/
def directionalPairSymbols : Finset (Sector × Sector) :=
  (scalarSectors ×ˢ scalarSectors).filter (fun p => p.1 ≠ p.2)

/-- Three-way symbols in three-scalar triplets: one per (triplet, equation) pair. -/
def directionalTripleSymbols : Finset (Finset Sector × Sector) :=
  ((tripletClass 0 0) ×ˢ scalarSectors).filter (fun p => p.2 ∈ p.1)

/-- Counting: 56 directional pair symbols and 168 three-way symbols in the source, versus
28 unordered pairs and 56 triplets once reciprocity identifies them: 224 parameters become 84. -/
theorem scalar_parameter_economy :
    directionalPairSymbols.card = 56 ∧ (scalarSectors.powersetCard 2).card = 28 ∧
      directionalTripleSymbols.card = 168 ∧ (tripletClass 0 0).card = 56 := by
  refine ⟨by decide, by decide, by decide +kernel, class_three_scalars⟩

end FieldSpace
