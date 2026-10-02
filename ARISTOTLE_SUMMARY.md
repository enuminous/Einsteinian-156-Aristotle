# Summary of changes for run 0cb5ae24-92e1-4b47-b019-7f21b498d7cb
I wrote up the findings in a new file, `THEOREMS.md`, which lists all 71 theorems and lemmas in the project. Each entry gives the theorem's name, file and a one-line statement, and the main result for each register item is marked. I didn't change any proofs. Before writing the file I rebuilt the whole project: it compiles with no errors and contains no `sorry`. I also ran `#print axioms` on all 71 theorems; they rely only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and none use `native_decide`.

The file has three parts:
- **Findings at a glance:** a table of ten results that covers every item in the register (FS-T01 to FS-T09 and FS-C01 to FS-C04):
  - 165 triplets; each sector is in 45 of them and each pair of sectors is in 9.
  - The six classes have sizes 56/56/28/16/8/1, and every triplet falls in exactly one.
  - The equation file has 585 statements (45 + 90 + 90 + 360), and every block contains exactly the statements the source's rules require.
  - Deleting k sectors leaves C(11−k, 3) triplets.
  - Of the 13,530 pairs of triplets, 1,980/6,930/4,620 share 2/1/0 sectors.
  - The null-slice law, and shared-pair gluing as an "if and only if".
  - FS-C02: the three equations of a three-scalar triplet come from a single potential exactly when the couplings are symmetric (`λ_xy = λ_yx` for each pair, and `λ_xyz = λ_yxz = λ_zxy`).
  - FS-C04: with symmetric couplings, the scalar coupling symbols drop from 224 to 84.
  - FS-C03: as written, the gauge equations with a scalar coupling (`κ ≠ 0`) force an extra equation that the source doesn't list.
  - FS-C01: the triplet equations satisfy the gluing law exactly when there is a single global theory, with at most three-sector interactions, that reproduces all of them.
- **Complete list:** every theorem, grouped by file in `RequestProject/FieldSpace/` (`Basic`, `Inventory`, `Coupling`, `Reciprocity`, `Conservation`, `Gluing`).
- **Suggested corrections to the source:**
  - `THEOREM_REGISTER.md` still says the file has 578 statements; it has 585.
  - The term `κ φ ∇^ν φ` built from a real scalar is not a conserved current, so as written the system is overdetermined.

The file also states the limits:
- A script copied each block's heading and statement types from the equation file into Lean, and that copying step is not checked by Lean. Every check on the copied data is.
- FS-C03 covers flat space only, and it assumes the currents the source leaves undefined (`J_E`, `Ξ`) are conserved.
- The gluing results don't check the specific coefficients written in the source file.

The Properties table already matched these results, so I didn't change it. The new file is committed.

# Summary of changes for run 12c5a1c1-aff2-4ab0-9509-c11a1e8e11e3
Yes. This session proved the one candidate law in the register that was still open, **FS-C01 (Atlas Gluing Law)**. The full project builds with no `sorry`, and the new theorems use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). With this, every item in the register (FS-T01 to FS-T09 and FS-C01 to FS-C04) is now covered.

**What FS-C01 says.** The register states that triplet equations sharing some sectors should agree when every field outside the shared sectors is zero. If that fails, the catalog "cannot be interpreted as projections of one global theory." I made both halves of that statement precise and proved that they are equivalent.

**What I proved** (all in the new file `RequestProject/FieldSpace/Gluing.lean`):
- **`atlas_gluing`**: take any finite set of sectors and charts of `k` sectors each, where `k` is at most the number of sectors. Each chart's equation can be any function of the fields, with values in any additive group; nothing about its shape is assumed. The family satisfies the gluing law **if and only if** some global theory restricts to each chart's equation, where the global theory is a sum of terms that each involve at most `k` sectors.
- **`atlas_gluing_unique`**: that global theory is unique. A theory of this kind is fully determined by its restrictions to the `k`-sector charts.
- **`fieldSpace_atlas_gluing`**: the case of the source's 11 sectors and 165 triplets. The triplet equations satisfy the gluing law exactly when there is **exactly one** global theory with at most three-sector interactions that reproduces every triplet.

The global theory is built explicitly, using inclusion–exclusion (Möbius inversion) over sets of sectors.

**Limits:** these theorems are about the logical structure of the catalog. They do not check that the coefficients actually written in `EFMW_165_field_equations.txt` satisfy the gluing law. They also do not affect the earlier FS-C03 finding that, as written, the gauge equations with a scalar coupling impose an extra equation the source does not list.

I added a FS-C01 section to `FIELDSPACE_NOTES.md`, the Properties table has the new result marked as proved, and the work is committed.

# Summary of changes for run 7fc74883-729e-4649-b4a5-cf7afcc120bd
**No new law of nature.** The repository's own `THEOREM_REGISTER.md` says the same: "This pass does not establish a new law of nature." What I did this session was test the register's candidate laws (FS-C02, FS-C03, FS-C04) against the equation forms in the source file. All of these results are proved in Lean, build cleanly with no `sorry`, and use only the standard axioms.

**FS-C02, couplings that can come from a single action** (`RequestProject/FieldSpace/Reciprocity.lean`, `exists_potential_iff_reciprocal`). Take any three-scalar triplet and its residuals `m_x φ_x + λ_xy φ_y + λ_xz φ_z + λ_xyz φ_y φ_z` (and the same pattern for y and z). These are the partial derivatives of one potential exactly when:
- each pair coupling matches its reverse: `λ_xy = λ_yx`, `λ_xz = λ_zx`, `λ_yz = λ_zy`;
- the three-way couplings are all equal: `λ_xyz = λ_yxz = λ_zxy`.

In that case the potential is written out explicitly. The source gives `λ_FW` and `λ_WF` (and the others) separate names, so as written it does not require this.

**FS-C04, fewer free parameters** (`scalar_parameter_economy`). If the couplings match as above, the scalar-only coupling symbols drop from 224 independent ones to 84:
- 56 one-way pair symbols become 28;
- 168 three-way symbols become 56.

**FS-C03, conservation check — this is where the source has a problem** (`RequestProject/FieldSpace/Conservation.lean`). In flat space with any constant diagonal metric:
- For any antisymmetric, twice-differentiable `F`, the divergence of `∂_μ F^{μν}` is identically zero (`div_div_antisymm`).
- Apply this to the source's gauge equation `∂_μ F^{μν} = κ φ ∂^ν φ + J^ν`. If the other currents `J` are conserved, it forces `κ □(φ²) = 0` (`scalar_current_constraint`).
- Add the source's scalar equation `□φ + m²φ + s = 0`. If `κ ≠ 0`, every solution must also satisfy `(∂φ)² = m²φ² + φ s`. The source does not list this extra equation (`scalar_current_extra_equation`).
- A concrete case (`linear_profile_obstruction`): `φ = xᵢ` solves `□φ = 0`, but no field `F` with conserved `J` can satisfy the gauge equation alongside it when `κ ≠ 0`.

The reason is that `φ ∂^ν φ` built from a real scalar equals `½ ∂^ν(φ²)`. That is not a conserved current, so as written the source's gauge equations with a scalar coupling impose this extra condition (the system is overdetermined). There are three ways around it:
- set those couplings to zero;
- use a complex (charged) scalar;
- let the currents `J_E` and `Ξ` cancel the term. The source does not define those currents, which is why the theorem assumes they are conserved.

Curved spacetime is not covered.

**Not done:** FS-C01, general atlas gluing, is still not formalized beyond FS-T09.

`FIELDSPACE_NOTES.md` now maps each candidate law to its Lean theorem. The Properties table has been updated, and the work is committed.

## Suggested follow-up

The source has two problems I can help fix. First, its gauge equations use `κ_MF φ_F ∇^ν φ_F` (and the same pattern for the other scalars). For a real scalar this term is not a conserved current, so with `κ ≠ 0` the equations are overdetermined. Second, the note in `THEOREM_REGISTER.md` about 578 statements is out of date; the file has all 585. I can draft corrected wording for both, for example a complex-scalar current or a stated conservation condition on `J_E` and `Ξ`.

# Summary of changes for run af59d620-659c-442e-9843-d4ab188bee08
You sent only the repository link, so I took the task to be checking the structural and algebraic claims marked as proved in its `THEOREM_REGISTER.md`. I used the repository at commit `a07c0b7`. Everything builds with no `sorry`, and every theorem relies only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The finite checks are run by Lean's kernel itself (`decide +kernel`); I didn't use `native_decide`.

**Why I restated the theorems:** most of the repository's own Lean proofs are bare number facts, such as `Nat.choose 11 3 = 165`, `2 * 8 = 16`, `8 = 8` and `56+56+28+16+8+1 = 165`. They never mention the sectors or the triplets. My version defines an actual type with the 11 sectors and the set of all their 3-element subsets, and states each claim about those objects.

**Results (all in `RequestProject/FieldSpace/`):**
- **FS-T01 to FS-T03** (`Basic.lean`): there are 165 triplets, every sector is in 45 of them, and every pair of distinct sectors is in 9.
- **FS-T04** (`Basic.lean`): the six classes have sizes 56/56/28/16/8/1, the single gravity + two gauges triplet is {E, M, S}, and every triplet falls in exactly one class.
- **FS-T06** (`Basic.lean`): deleting any set of sectors leaves exactly all the 3-subsets of the remaining sectors. That gives C(11−k, 3) triplets, so 120, 84 and 56 remain after deleting 1, 2 and 3 sectors.
- **FS-T07** (`Basic.lean`): of the 13,530 unordered pairs of distinct triplets, 1,980 share two sectors, 6,930 share one and 4,620 share none. Two distinct triplets never share more than two.
- **FS-T05** (`Inventory.lean`), checked against the equation file itself:
  - its block headings are exactly the 165 triplets, with no duplicates and none missing;
  - every block contains exactly the statements the source's rules require for its triplet (one Einstein equation if E is present, a dynamical equation and a Bianchi identity for each gauge sector, one equation per scalar sector);
  - the totals are 45 + 90 + 90 + 360 = 585.
- **FS-T08 and FS-T09** (`Coupling.lean`), proved for any commutative ring rather than only the reals:
  - the three-way term vanishes whenever either of its two fields is zero;
  - two triplets that share a pair give the same equation once their third field is set to zero.
  - I also proved the converse: they agree for every value of the shared field **only if** their base terms and pair coefficients are equal.

**One unverified step:** a short script copied the heading and statement types of each block from the equation file into `SourceData.lean`. That copying step is not checked by Lean; every check on the copied data is.

**Not covered:** FS-C01 to FS-C04, which the register itself labels as candidate laws.

`FIELDSPACE_NOTES.md` maps each register item to its Lean theorem. The equation file is copied unchanged into `source/`.

## Suggested follow-up

One sentence in the repository is out of date. Under FS-T05, `THEOREM_REGISTER.md` still says "The current source contains 578 because the S-P-A body is absent and H-P-A is missing." The checked count shows the restored equation file has all 585 statements. I can draft the corrected wording if that would help.