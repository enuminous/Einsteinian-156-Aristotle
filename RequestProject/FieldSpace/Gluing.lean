module

public import RequestProject.FieldSpace.Basic

/-!
# FS-C01: the atlas gluing law

The register's candidate law FS-C01 asks that "all triplet equations that share a lower-order
sector subset agree when every field outside that subset is set to zero", and says that failure
"would mean the catalog cannot be interpreted as projections of one global theory".

We make this precise and prove it in full generality.

* A *field configuration* is a map `φ : ι → R` (one value per sector).
* `restrict U φ` sets every field outside `U` to zero.
* A *local equation* on a chart `T` is any function `f T : (ι → R) → M` (the residual, with
  values in an additive group `M`; nothing about its shape is assumed).
* A family of local equations on the `k`-element charts is `GluingCompatible` if any two charts
  agree on configurations supported on their overlap. This is exactly FS-C01.
* A global theory `F : (ι → R) → M` is `IsKBody k` if it is a sum of terms each of which only
  depends on the fields of at most `k` sectors.

**Theorem** (`atlas_gluing`, `atlas_gluing_unique`). If `k ≤ |ι|`, a family of local equations on
the `k`-element charts satisfies the gluing law if and only if it is the family of chart
restrictions of a global `k`-body theory, and that global theory is unique.

The proof is Möbius inversion on the Boolean lattice of sector subsets.
-/

@[expose] public section

namespace FieldSpace

open Finset

variable {ι R M : Type*} [DecidableEq ι] [Zero R] [AddCommGroup M]

/-- Set every field outside `U` to zero. -/
def restrict (U : Finset ι) (φ : ι → R) : ι → R := fun i => if i ∈ U then φ i else 0

omit [AddCommGroup M] in
theorem restrict_restrict (U V : Finset ι) (φ : ι → R) :
    restrict U (restrict V φ) = restrict (U ∩ V) φ := by
  funext i
  by_cases hU : i ∈ U <;> by_cases hV : i ∈ V <;> simp [restrict, hU, hV]

omit [AddCommGroup M] in
theorem restrict_of_subset {U V : Finset ι} (h : U ⊆ V) (φ : ι → R) :
    restrict U (restrict V φ) = restrict U φ := by
  rw [restrict_restrict, inter_eq_left.mpr h]

omit [AddCommGroup M] in
theorem restrict_of_superset {U V : Finset ι} (h : U ⊆ V) (φ : ι → R) :
    restrict V (restrict U φ) = restrict U φ := by
  rw [restrict_restrict, inter_eq_right.mpr h]

/-- Möbius transform of a set function on the Boolean lattice. -/
def mobius (a : Finset ι → M) (S : Finset ι) : M :=
  ∑ U ∈ S.powerset, ((-1 : ℤ) ^ (S.card - U.card)) • a U

omit [DecidableEq ι] in
theorem mobius_congr [DecidableEq ι] {a b : Finset ι → M} {S : Finset ι}
    (h : ∀ U ⊆ S, a U = b U) : mobius a S = mobius b S := by
  unfold mobius
  exact sum_congr rfl fun U hU => by rw [h U (mem_powerset.mp hU)]

theorem mobius_insert (a : Finset ι → M) {i : ι} {S : Finset ι} (hi : i ∉ S) :
    mobius a (insert i S) = mobius (fun U => a (insert i U)) S - mobius a S := by
  unfold mobius
  rw [card_insert_of_notMem hi, sum_powerset_insert hi, sub_eq_add_neg, add_comm,
    ← sum_neg_distrib]
  congr 1 <;> refine sum_congr rfl fun U hU => ?_
  · rw [card_insert_of_notMem (fun h => hi (mem_powerset.mp hU h)), Nat.add_sub_add_right]
  · have hle := card_le_card (mem_powerset.mp hU)
    rw [show #S + 1 - #U = (#S - #U) + 1 by omega, pow_succ]
    simp

theorem sum_mobius_powerset (a : Finset ι → M) (T : Finset ι) :
    ∑ S ∈ T.powerset, mobius a S = a T := by
  induction T using Finset.induction_on generalizing a with
  | empty => simp [mobius]
  | insert i T hi ih =>
    rw [sum_powerset_insert hi,
      sum_congr rfl (fun S hS => mobius_insert a (fun h => hi (mem_powerset.mp hS h))),
      sum_sub_distrib, ih, ih]
    abel

theorem mobius_eq_zero_of_not_subset {a : Finset ι → M} {S T : Finset ι}
    (ha : ∀ U, a U = a (U ∩ T)) (hS : ¬ S ⊆ T) : mobius a S = 0 := by
  obtain ⟨i, hiS, hiT⟩ := not_subset.mp hS
  rw [← insert_erase hiS, mobius_insert a (notMem_erase i S), sub_eq_zero]
  refine mobius_congr fun U _ => ?_
  rw [ha (insert i U), ha U, insert_inter_of_notMem hiT]

theorem sum_mobius_le (k : ℕ) [Fintype ι] {a : Finset ι → M} {T : Finset ι}
    (hT : T.card ≤ k) (ha : ∀ U, a U = a (U ∩ T)) :
    ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k), mobius a S = a T := by
  rw [← sum_subset (s₁ := T.powerset), sum_mobius_powerset]
  · intro S hS
    simpa using (card_le_card (mem_powerset.mp hS)).trans hT
  · intro S _ hS
    exact mobius_eq_zero_of_not_subset ha (fun h => hS (mem_powerset.mpr h))

omit [DecidableEq ι] in
theorem mobius_sum {κ : Type*} (s : Finset κ) (b : κ → Finset ι → M) (S : Finset ι) :
    mobius (fun U => ∑ j ∈ s, b j U) S = ∑ j ∈ s, mobius (b j) S := by
  unfold mobius
  simp_rw [smul_sum]
  exact sum_comm

/-- A function of the fields that only depends on the fields of the sectors in `S`. -/
def DependsOn (S : Finset ι) (h : (ι → R) → M) : Prop := ∀ φ, h φ = h (restrict S φ)

/-- A global theory built out of interaction terms that each involve at most `k` sectors. -/
def IsKBody [Fintype ι] (k : ℕ) (F : (ι → R) → M) : Prop :=
  ∃ h : Finset ι → (ι → R) → M, (∀ S, DependsOn S (h S)) ∧
    ∀ φ, F φ = ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k), h S φ

/-- **FS-C01, the gluing law.** Local equations on the `k`-element charts agree on every
configuration in which all fields outside the shared sector subset are zero. -/
def GluingCompatible (k : ℕ) (f : Finset ι → (ι → R) → M) : Prop :=
  ∀ T T' : Finset ι, T.card = k → T'.card = k → ∀ φ : ι → R,
    f T (restrict (T ∩ T') φ) = f T' (restrict (T ∩ T') φ)

/-- `F` restricts to the local equation `f T` on every `k`-element chart `T`. -/
def RestrictsTo (k : ℕ) (F : (ι → R) → M) (f : Finset ι → (ι → R) → M) : Prop :=
  ∀ T : Finset ι, T.card = k → ∀ φ : ι → R, F (restrict T φ) = f T (restrict T φ)

/-- A `k`-body theory is recovered from its restrictions to sector subsets of size at most `k`
by Möbius inversion. -/
theorem IsKBody.eq_sum_mobius [Fintype ι] {k : ℕ} {F : (ι → R) → M} (hF : IsKBody k F)
    (φ : ι → R) :
    F φ = ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k),
      mobius (fun U => F (restrict U φ)) S := by
  obtain ⟨h, hdep, hsum⟩ := hF
  simp only [hsum, mobius_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S0 hS0 => ?_
  rw [sum_mobius_le k (T := S0) (mem_filter.mp hS0).2, ← hdep]
  intro U
  rw [hdep S0 (restrict U φ), restrict_restrict, hdep S0 (restrict (U ∩ S0) φ),
    restrict_restrict, ← inter_assoc, inter_comm S0 U, inter_assoc, inter_self]

omit [AddCommGroup M] in
/-- Restrictions of any single global theory satisfy the gluing law. -/
theorem gluingCompatible_of_restrictsTo {k : ℕ} {F : (ι → R) → M}
    {f : Finset ι → (ι → R) → M} (hF : RestrictsTo k F f) : GluingCompatible k f := by
  intro T T' hT hT' φ
  have h1 : restrict T (restrict (T ∩ T') φ) = restrict (T ∩ T') φ := by
    rw [restrict_restrict, ← inter_assoc, inter_self]
  have h2 : restrict T' (restrict (T ∩ T') φ) = restrict (T ∩ T') φ := by
    rw [restrict_restrict, inter_comm T T', ← inter_assoc, inter_self]
  calc f T (restrict (T ∩ T') φ) = f T (restrict T (restrict (T ∩ T') φ)) := by rw [h1]
    _ = F (restrict T (restrict (T ∩ T') φ)) := (hF T hT _).symm
    _ = F (restrict T' (restrict (T ∩ T') φ)) := by rw [h1, h2]
    _ = f T' (restrict T' (restrict (T ∩ T') φ)) := hF T' hT' _
    _ = f T' (restrict (T ∩ T') φ) := by rw [h2]

/-- A family satisfying the gluing law is the family of restrictions of a global `k`-body
theory. -/
theorem exists_kBody_of_gluingCompatible [Fintype ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    {f : Finset ι → (ι → R) → M} (hf : GluingCompatible k f) :
    ∃ F, IsKBody k F ∧ RestrictsTo k F f := by
  have hex : ∀ S : Finset ι, ∃ T : Finset ι, S.card ≤ k → S ⊆ T ∧ T.card = k := by
    intro S
    by_cases hS : S.card ≤ k
    · obtain ⟨T, hST, hT⟩ := exists_superset_card_eq hS hk
      exact ⟨T, fun _ => ⟨hST, hT⟩⟩
    · exact ⟨S, fun h => absurd h hS⟩
  choose τ hτ using hex
  let loc : Finset ι → (ι → R) → M := fun S φ => mobius (fun U => f (τ S) (restrict U φ)) S
  refine ⟨fun φ => ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k), loc S φ,
    ⟨loc, fun S φ => mobius_congr fun U hU => by rw [restrict_of_subset hU], fun _ => rfl⟩, ?_⟩
  intro T hT φ
  have ha : ∀ (X U : Finset ι), f X (restrict U (restrict T φ)) =
      f X (restrict (U ∩ T) (restrict T φ)) := by
    intro X U
    rw [restrict_restrict, restrict_restrict, inter_assoc, inter_self]
  have key : ∀ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k),
      loc S (restrict T φ) = mobius (fun U => f T (restrict U (restrict T φ))) S := by
    intro S hS
    have hS' := (mem_filter.mp hS).2
    by_cases hST : S ⊆ T
    · refine mobius_congr fun U hU => ?_
      have hsub : U ⊆ τ S ∩ T := subset_inter (hU.trans (hτ S hS').1) (hU.trans hST)
      have := hf (τ S) T (hτ S hS').2 hT (restrict U φ)
      rw [restrict_of_superset hsub] at this
      rw [restrict_of_subset (hU.trans hST), this]
    · show mobius (fun U => f (τ S) (restrict U (restrict T φ))) S = _
      rw [mobius_eq_zero_of_not_subset (ha (τ S)) hST,
        mobius_eq_zero_of_not_subset (ha T) hST]
  simp only
  rw [sum_congr rfl key, sum_mobius_le k hT.le (ha T), restrict_of_subset subset_rfl]

/-- **FS-C01 (existence).** For `k ≤ |ι|`, a family of local equations on the `k`-element charts
satisfies the gluing law if and only if it consists of the chart restrictions of one global
`k`-body theory. -/
theorem atlas_gluing [Fintype ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    (f : Finset ι → (ι → R) → M) :
    GluingCompatible k f ↔ ∃ F, IsKBody k F ∧ RestrictsTo k F f :=
  ⟨exists_kBody_of_gluingCompatible hk, fun ⟨_, _, hF⟩ => gluingCompatible_of_restrictsTo hF⟩

/-- **FS-C01 (uniqueness).** For `k ≤ |ι|`, a global `k`-body theory is determined by its
restrictions to the `k`-element charts. -/
theorem atlas_gluing_unique [Fintype ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    {F G : (ι → R) → M} (hF : IsKBody k F) (hG : IsKBody k G)
    (h : ∀ T : Finset ι, T.card = k → ∀ φ, F (restrict T φ) = G (restrict T φ)) : F = G := by
  funext φ
  rw [hF.eq_sum_mobius, hG.eq_sum_mobius]
  refine sum_congr rfl fun S hS => mobius_congr fun U hU => ?_
  obtain ⟨T, hUT, hT⟩ := exists_superset_card_eq
    ((card_le_card hU).trans (mem_filter.mp hS).2) hk
  have e : restrict T (restrict U φ) = restrict U φ := by
    rw [restrict_restrict, inter_eq_right.mpr hUT]
  rw [← e]
  exact h T hT _

/-- **FS-C01 for the FieldSpace atlas.** A family of local equations on the 165 triplets
satisfies the gluing law if and only if it is the family of triplet restrictions of a global
theory built from interactions of at most three sectors; that global theory is unique. -/
theorem fieldSpace_atlas_gluing (f : Finset Sector → (Sector → R) → M) :
    GluingCompatible 3 f ↔ ∃! F : (Sector → R) → M, IsKBody 3 F ∧ RestrictsTo 3 F f := by
  have hk : 3 ≤ Fintype.card Sector := by simp [card_sector]
  rw [atlas_gluing hk]
  refine ⟨fun ⟨F, hF⟩ => ⟨F, hF, fun G hG => atlas_gluing_unique hk hG.1 hF.1 ?_⟩,
    fun ⟨F, hF, _⟩ => ⟨F, hF⟩⟩
  intro T hT φ
  rw [hG.2 T hT, hF.2 T hT]

end FieldSpace
