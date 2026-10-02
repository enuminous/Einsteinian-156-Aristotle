# FieldSpace: findings and the full list of theorems

Source: https://github.com/enuminous/FieldSpace (commit `a07c0b7`). The equation file is copied
unchanged to `source/EFMW_165_field_equations.txt`.

**Status.** There are 71 theorems and lemmas in total. All of them are in namespace `FieldSpace`,
in `RequestProject/FieldSpace/`, and they cover every register item, FS-T01 to FS-T09 and FS-C01
to FS-C04. `lake build` succeeds and the code contains no `sorry`. I ran `#print axioms` on all 71:
they use only `propext`, `Classical.choice` and `Quot.sound`, and some use none of these. No
`native_decide` is used; finite checks are run by the kernel (`decide` / `decide +kernel`).

**One unverified step.** A script copied each block's heading and statement kinds from the
equation file into `SourceData.lean`, and Lean does not check that copying. Lean does check
every theorem about the copied data.

---

## Findings at a glance

| # | Finding | Key theorem |
|---|---|---|
| 1 | 11 sectors give 165 triplets. Each sector is in 45 of them, and each pair of distinct sectors is in 9 (FS-T01–T03). | `atlas_card`, `sector_incidence`, `pair_incidence` |
| 2 | The six classes have sizes 56/56/28/16/8/1 and partition the atlas. The only triplet with gravity and two gauge sectors is {E, M, S} (FS-T04). | `six_classes_partition`, `class_*` |
| 3 | The equation file has exactly the 165 triplets as block headings, and every block follows the grammar. The totals are 45 + 90 + 90 + 360 = **585** statements (FS-T05). The register's remark about "578" is out of date. | `source_inventory`, `sourceBlocks_follow_grammar` |
| 4 | Deleting any k sectors leaves all 3-subsets of the rest, C(11−k, 3) triplets: 120/84/56 for k = 1/2/3 (FS-T06). | `ablate_eq`, `ablate_card` |
| 5 | Of the 13,530 pairs of distinct triplets, 1,980/6,930/4,620 share 2/1/0 sectors, and none share 3 (FS-T07). | `overlap_spectrum` |
| 6 | The three-way term vanishes when one of its two fields is zero (null slice). Two triplets sharing a pair glue **iff** their base terms and pair coefficients agree (FS-T08/T09). | `trilinear_null_slice`, `shared_pair_overlap_iff` |
| 7 | **FS-C02:** a three-scalar triplet comes from one potential **iff** `λ_xy = λ_yx` (for every pair) and `λ_xyz = λ_yxz = λ_zxy`. The source names these as separate symbols, so it does not impose this. | `exists_potential_iff_reciprocal` |
| 8 | **FS-C04:** under reciprocity, the scalar coupling symbols drop from 224 to 84. | `scalar_parameter_economy` |
| 9 | **FS-C03 (problem in the source):** take the gauge equation `∂_μF^{μν} = κ φ∂^νφ + J^ν` with the other currents conserved. With `κ ≠ 0` it forces the extra equation `(∂φ)² = m²φ² + φ s`. The source does not list this equation, so as written the system is overdetermined. Concretely, `φ = xᵢ` is ruled out. | `scalar_current_extra_equation`, `linear_profile_obstruction` |
| 10 | **FS-C01:** local equations on the k-sector charts satisfy the gluing law **iff** they are the restrictions of a global theory with at most k-sector interactions. That global theory is **unique**. For the 165 triplets, k = 3. | `atlas_gluing`, `atlas_gluing_unique`, `fieldSpace_atlas_gluing` |

Limits: the theorems do not check that the coefficients written in the source satisfy the gluing
law. FS-C03 covers flat space with a constant diagonal metric only, and it assumes the source's
undefined currents (`J_E`, `Ξ`) are conserved.

---

## Complete list

★ marks the main result for a register item. The other entries are supporting lemmas.

### `RequestProject/FieldSpace/Basic.lean`: the triplet atlas (FS-T01–T04, T06, T07)

| Theorem | Statement |
|---|---|
| `card_sector` | `Fintype.card Sector = 11` |
| `mem_atlas` | `t ∈ tripletAtlas ↔ t.card = 3` |
| ★ `atlas_card` | `tripletAtlas.card = 165` |
| ★ `sector_incidence` | `(tripletAtlas.filter (s ∈ ·)).card = 45` for every sector `s` |
| ★ `pair_incidence` | `a ≠ b → (tripletAtlas.filter (fun t => a ∈ t ∧ b ∈ t)).card = 9` |
| `class_three_scalars` | `(tripletClass 0 0).card = 56` |
| `class_one_gauge_two_scalars` | `(tripletClass 0 1).card = 56` |
| `class_gravity_two_scalars` | `(tripletClass 1 0).card = 28` |
| `class_gravity_gauge_scalar` | `(tripletClass 1 1).card = 16` |
| `class_two_gauges_scalar` | `(tripletClass 0 2).card = 8` |
| `class_gravity_two_gauges` | `(tripletClass 1 2).card = 1` |
| `class_gravity_two_gauges_eq` | `tripletClass 1 2 = {{E, M, S}}` |
| ★ `six_classes_partition` | every triplet lies in exactly one of the six classes `(0,0),(0,1),(1,0),(1,1),(0,2),(1,2)` |
| ★ `ablate_eq` | `ablate X = Xᶜ.powersetCard 3` (deleting any set of sectors leaves exactly all 3-subsets of the rest) |
| ★ `ablate_card` | `(ablate X).card = Nat.choose (11 - X.card) 3` |
| `ablate_card_one` | deleting 1 sector: 120 remain, 45 lost |
| `ablate_card_two` | deleting 2 sectors: 84 remain, 81 lost |
| `ablate_card_three` | deleting 3 sectors: 56 remain, 109 lost |
| `distinctPairs_card` | `distinctPairs.card = Nat.choose 165 2` |
| `overlapPairs_two` | 1980 pairs share 2 sectors |
| `overlapPairs_one` | 6930 pairs share 1 sector |
| `overlapPairs_zero` | 4620 pairs share no sector |
| `overlap_le_two` | distinct triplets share at most 2 sectors |
| ★ `overlap_spectrum` | `1980 + 6930 + 4620 = distinctPairs.card = 13530` |

### `RequestProject/FieldSpace/Inventory.lean`: the source equation file (FS-T05)

| Theorem | Statement |
|---|---|
| `sourceBlocks_heading_nodup` | every block heading names 3 distinct sectors |
| `sourceBlocks_triplets_nodup` | no triplet is repeated |
| `sourceBlocks_triplets_eq_atlas` | the set of block headings is exactly `tripletAtlas` |
| `sourceBlocks_follow_grammar` | each block contains exactly the statements the grammar prescribes for its triplet (as a multiset) |
| ★ `source_inventory` | 45 Einstein, 90 gauge dynamics, 90 Bianchi, 360 scalar; 585 statements in total |
| `expected_inventory` | the grammar alone predicts 585 statements over the atlas |
| `source_sector_incidence` | each sector appears in 45 block headings of the file |

### `RequestProject/FieldSpace/Coupling.lean`: null slices and shared-pair gluing (FS-T08, T09)

All of these hold over any commutative ring `R`.

| Theorem | Statement |
|---|---|
| ★ `trilinear_null_slice` | if `φ_j = 0 ∨ φ_k = 0`, the three-way term contributes nothing (any `λ_ijk` gives the same residual) |
| `restrict_third_zero` | residual at `φ_k = 0` is `base + λ_ij φ_j` |
| `restrict_second_zero` | residual at `φ_j = 0` is `base + λ_ik φ_k` |
| ★ `shared_pair_overlap_consistency` | two triplets sharing the pair (i,j) give the same equation once their third field is zero |
| ★ `shared_pair_overlap_iff` | they agree for every `φ_j` **iff** `base = base' ∧ λ_ij = λ_ij'` |
| `triple_ablation_difference` | removing the three-way coupling changes the residual by exactly `λ_ijk φ_j φ_k` |

### `RequestProject/FieldSpace/Reciprocity.lean`: master-action reciprocity, parameter economy (FS-C02, C04)

| Theorem | Statement |
|---|---|
| `hasDerivAt_quadratic` | derivative of `a t² + b t + d` is `2 a s + b` |
| `eq_of_hasDerivAt_affine` | if `f' (s) = a s + b` everywhere, then `f s = f 0 + a/2 s² + b s` |
| `potential_eq_x` | a potential is determined in its `x`-dependence by the `x` residual |
| `potential_eq_y` | likewise for `y` |
| `reciprocal_of_potential` | if a potential exists, the couplings are reciprocal |
| `masterPotential_isPotential` | if the couplings are reciprocal, the explicit `masterPotential` is a potential |
| ★ `exists_potential_iff_reciprocal` | a potential exists **iff** the couplings are reciprocal (`λ_xy = λ_yx`, `λ_xz = λ_zx`, `λ_yz = λ_zy`, `λ_xyz = λ_yxz = λ_zxy`) |
| ★ `scalar_parameter_economy` | 56 directional pair symbols become 28 pairs, and 168 directional triple symbols become 56 triplets |

### `RequestProject/FieldSpace/Conservation.lean`: conservation closure (FS-C03)

This file works on flat `ℝⁿ` with a constant diagonal metric `η`; `pd μ` is `∂_μ`.

| Theorem | Statement |
|---|---|
| `contDiff_pd` | a partial derivative of a `C^{k+1}` function is `C^k` |
| `differentiable_pd` | a partial derivative of a `C²` function is differentiable |
| `pd_comm` | partial derivatives of a `C²` function commute |
| `pd_neg` | `∂_μ(−f) = −∂_μ f` |
| `pd_sum` | `∂_μ` of a finite sum of differentiable functions is the sum of the derivatives |
| ★ `div_div_antisymm` | `∂_ν ∂_μ F^{μν} = 0` for any antisymmetric `C²` `F` |
| `pd_scalar_current` | `∂_ν(κ c φ ∂_νφ + J) = κ c ((∂_νφ)² + φ ∂_ν∂_νφ) + ∂_νJ` |
| ★ `scalar_current_constraint` | gauge equation + conserved `J` ⇒ `κ (φ □φ + (∂φ)²) = 0`, i.e. `κ □(φ²) = 0` up to a factor 2 |
| ★ `scalar_current_extra_equation` | adding the scalar equation `□φ + m²φ + s = 0`, with `κ ≠ 0`, forces `(∂φ)² = m²φ² + φ s` |
| `pd_coord` | `∂_ν xᵢ = δ_νi` |
| ★ `linear_profile_obstruction` | if `η_i ≠ 0` and `κ ≠ 0`, then `φ = xᵢ` satisfies `□φ = 0`, yet no antisymmetric `C²` `F` and conserved `J` satisfy the gauge equation with it |

### `RequestProject/FieldSpace/Gluing.lean`: atlas gluing law (FS-C01)

These results hold for any finite sector type `ι`, field values in any type with a zero, and
equations valued in any additive commutative group `M`.

| Theorem | Statement |
|---|---|
| `restrict_restrict` | `restrict U (restrict V φ) = restrict (U ∩ V) φ` |
| `restrict_of_subset` | `U ⊆ V → restrict U (restrict V φ) = restrict U φ` |
| `restrict_of_superset` | `U ⊆ V → restrict V (restrict U φ) = restrict U φ` |
| `mobius_congr` | the Möbius transform at `S` depends only on values on subsets of `S` |
| `mobius_insert` | recursion formula for the Möbius transform |
| `sum_mobius_powerset` | Möbius inversion: `∑_{S ⊆ T} mobius a S = a T` |
| `mobius_eq_zero_of_not_subset` | if `a` only depends on `U ∩ T`, then `mobius a S = 0` for `S ⊄ T` |
| `sum_mobius_le` | summing over all `S` with `|S| ≤ k` recovers `a T` when `|T| ≤ k` |
| `mobius_sum` | the Möbius transform is additive |
| `IsKBody.eq_sum_mobius` | a k-body theory equals the sum of the Möbius transforms of its restrictions |
| `gluingCompatible_of_restrictsTo` | restrictions of one global theory always satisfy the gluing law |
| `exists_kBody_of_gluingCompatible` | a gluing-compatible family comes from some k-body global theory (`k ≤ |ι|`) |
| ★ `atlas_gluing` | `GluingCompatible k f ↔ ∃ F, IsKBody k F ∧ RestrictsTo k F f` |
| ★ `atlas_gluing_unique` | two k-body theories with equal restrictions to all k-sector charts are equal |
| ★ `fieldSpace_atlas_gluing` | for the 11 sectors and 165 triplets: `GluingCompatible 3 f ↔ ∃! F, IsKBody 3 F ∧ RestrictsTo 3 F f` |

---

## Suggested corrections to the source

1. `THEOREM_REGISTER.md`, FS-T05, still says that the source contains 578 statements. The
   checked count shows the restored file has all 585 (`source_inventory`).
2. In the gauge equations, the term `κ φ ∇^ν φ` built from a real scalar is `½ κ ∇^ν(φ²)`, which
   is not a conserved current. Unless `J_E`/`Ξ` cancel it, setting `κ ≠ 0` overdetermines the
   system (`scalar_current_extra_equation`). Possible fixes:
   - set those couplings to zero;
   - use a complex (charged) scalar current;
   - state a conservation condition that `J_E` and `Ξ` must satisfy.
