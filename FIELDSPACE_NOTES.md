# FieldSpace: Lean formalization of the theorem register

Source: https://github.com/enuminous/FieldSpace (commit `a07c0b7`). The equation file is
copied verbatim to `source/EFMW_165_field_equations.txt`.

The original repository's Lean files mostly prove numeric identities such as
`Nat.choose 11 3 = 165`, `2 * 8 = 16`, `8 = 8` or `56 + 56 + 28 + 16 + 8 + 1 = 165`.
Those identities do not mention the sectors or the triplets. Here every structural claim is
stated about an actual type `Sector` with 11 constructors and the actual family
`tripletAtlas` of its 3-element subsets. Finite checks are done by the Lean kernel
(`decide +kernel`), not by `native_decide`. Every theorem uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

| Register item | Lean (namespace `FieldSpace`) | File |
|---|---|---|
| FS-T01 165 triplets | `atlas_card` | `RequestProject/FieldSpace/Basic.lean` |
| FS-T02 45 triplets per sector | `sector_incidence` | same |
| FS-T03 9 triplets per pair | `pair_incidence` | same |
| FS-T04 six classes 56/56/28/16/8/1 and they partition the atlas | `class_*`, `class_gravity_two_gauges_eq`, `six_classes_partition` | same |
| FS-T06 ablation closure | `ablate_eq` (any deletion leaves the complete 3-uniform hypergraph on what remains), `ablate_card` (`C(11-k,3)`), `ablate_card_one/two/three` | same |
| FS-T07 overlap spectrum 1980/6930/4620 | `overlapPairs_two/one/zero`, `overlap_le_two`, `overlap_spectrum` | same |
| FS-T05 585 statements | `source_inventory` (counted in the source file), `expected_inventory` (from the grammar alone) | `RequestProject/FieldSpace/Inventory.lean` |
| source integrity | `sourceBlocks_heading_nodup`, `sourceBlocks_triplets_nodup`, `sourceBlocks_triplets_eq_atlas`, `sourceBlocks_follow_grammar`, `source_sector_incidence` | same |
| FS-T08 null-slice law | `trilinear_null_slice` | `RequestProject/FieldSpace/Coupling.lean` |
| FS-T09 shared-pair gluing | `shared_pair_overlap_consistency`, plus the converse `shared_pair_overlap_iff` | same |

## How the source data was obtained

`RequestProject/FieldSpace/SourceData.lean` records, for each block, its heading and the kinds
of statement it contains (Einstein, gauge dynamics, Bianchi identity, scalar). A short script
extracted this mechanically from the text file, and that extraction step is not itself
verified. Everything after it is checked in Lean: the headings are exactly the 165 triplets,
with no duplicates and none missing, and every block contains exactly the statements the
grammar prescribes for its triplet.

## Observation

`THEOREM_REGISTER.md` (FS-T05) still says "The current source contains 578 because the S-P-A
body is absent and H-P-A is missing." For the restored file at commit `a07c0b7` that
sentence is out of date: `source_inventory` shows that the file has all 585 statements.

## Candidate laws FS-C02 to FS-C04 (second pass)

No new law of nature is established here, and the register itself says none is claimed.
What the second pass adds is a test of the candidate consistency laws against the source's
equation forms:

| Register item | Lean (namespace `FieldSpace`) | File | Outcome |
|---|---|---|---|
| FS-C02 master-action reciprocity | `ScalarTripletCouplings.exists_potential_iff_reciprocal` | `RequestProject/FieldSpace/Reciprocity.lean` | Proved, for a three-scalar triplet: the non-derivative parts of the three scalar equations are the partial derivatives of one potential **iff** `λ_xy = λ_yx`, `λ_xz = λ_zx`, `λ_yz = λ_zy` and `λ_xyz = λ_yxz = λ_zxy`. The potential is given explicitly (`masterPotential`). The source names these as separate symbols, so as written it does not impose reciprocity. |
| FS-C04 parameter economy | `scalar_parameter_economy` | same | Counted: among the eight scalar sectors, 56 directional pair symbols and 168 three-way symbols (224 in all) reduce to 28 + 56 = 84 under reciprocity. |
| FS-C03 Noether/conservation closure | `div_div_antisymm`, `scalar_current_constraint`, `scalar_current_extra_equation`, `linear_profile_obstruction` | `RequestProject/FieldSpace/Conservation.lean` | In flat coordinates with any constant diagonal metric: `∂_ν ∂_μ F^{μν} = 0` for antisymmetric `C²` `F`. So the source's gauge equation `∂_μ F^{μν} = κ φ ∂^ν φ + J^ν` (with the other currents `J` conserved) forces `κ □(φ²) = 0`. Together with the scalar equation `□φ + m²φ + s = 0`, for `κ ≠ 0` every solution must also satisfy `(∂φ)² = m²φ² + φ s`, an equation the source does not list. Concrete case: the profile `φ = xᵢ` solves `□φ = 0` but is incompatible with the gauge equation whenever `κ ≠ 0`. |

Scope of FS-C03: the term `κ φ ∂^ν φ` built from a real scalar is the gradient `½ κ ∂^ν(φ²)`, not a
Noether current. The theorem assumes that the remaining currents (`J_E`, `Ξ`, …) are conserved;
in the source they are not defined, so they could in principle compensate. Curved space is not
covered.

## Candidate law FS-C01 (third pass)

| Register item | Lean (namespace `FieldSpace`) | File | Outcome |
|---|---|---|---|
| FS-C01 atlas gluing | `atlas_gluing`, `atlas_gluing_unique`, `fieldSpace_atlas_gluing` | `RequestProject/FieldSpace/Gluing.lean` | Proved in general. Take local equations on the `k`-sector charts: arbitrary functions of the fields, valued in any additive group. Assume `k` is at most the number of sectors. The family satisfies the gluing law (any two charts agree whenever every field outside their shared sectors is zero) **iff** it is the family of chart restrictions of a global theory built from interaction terms that each involve at most `k` sectors. That global theory is unique. For the 11 sectors and the 165 triplets (`k = 3`), this is `fieldSpace_atlas_gluing`. |

The proof uses Möbius inversion on the lattice of sector subsets (`mobius`, `sum_mobius_powerset`).
The register asks whether the catalog can be read as projections of one global theory. Under the
gluing law it can, and the global theory has at most three-sector interactions. The theorem is
about the logical structure only. It does not check that the source's displayed coefficients
satisfy the gluing law, and it says nothing about FS-C03's dynamical consistency.
