# FieldSpace reconstruction

<!-- ENUMINOUS-LIFECYCLE:START -->
**Lifecycle review — 2026-10-16: superseded source-closure claim; historical derivation retained.**

The claim that shared-component overlap checks plus two support rules establish the original full-vector `fieldSpace_atlas_gluing` premise is superseded. The [later closure audit](https://github.com/enuminous/EFMW_Post156_Zoo_Audit/blob/6fbd8beddf442e7adb752ec30ae054a25857602b/docs/FIELDSPACE_CLOSURE_AUDIT.md) gives an explicit counterexample to that implication. The [projected gluing repair](https://github.com/enuminous/EFMW_Post156_Zoo_Audit/blob/6fbd8beddf442e7adb752ec30ae054a25857602b/docs/PROJECTED_GLUING_REPAIR.md) replaces the contract by restricting both inputs and equation outputs, with uniqueness in the explicit class `|S ∪ {s}| ≤ k`. The generic conditional Lean theorem remains valid; applying it to the old zero-padded source encoding is the unsupported step. The original reports below do not establish full source gluing or unique physical dynamics. Mixed current/stress, vacuum and conservation obligations remain open.

[Portfolio review and evidence](https://github.com/enuminous/EFMW_Post156_Zoo_Audit/blob/main/portfolio/REPOSITORY_LIFECYCLE_2026-10-16.md).
<!-- ENUMINOUS-LIFECYCLE:END -->

Using the proved gluing theorem, define for each subset S of at most three sectors:

h_S(phi) = sum over U subset S of (-1)^(|S|-|U|) times f_tau(S)(phi restricted to U).

Then define F(phi) as the sum of h_S(phi) over all subsets S with |S| <= 3.

For 11 sectors this gives 1 + 11 + 55 + 165 = 232 components.

Under the two support conditions in GLUING_AUDIT.md, every one of the 165 triplet restrictions is recovered exactly from F. This is the explicit Mobius-inversion reconstruction of the atlas. It is a mathematical residual-system reconstruction, not an empirical validation claim.
