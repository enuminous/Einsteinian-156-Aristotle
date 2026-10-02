# FieldSpace Master Interaction Inventory

This inventory is derived directly from the 165 source triplets in `source/EFMW_165_field_equations.txt`.

## Global decomposition

The unique <=3-sector reconstruction has the expected support structure:

- 11 one-sector components
- 55 two-sector components
- 165 three-sector components

All 55 unordered sector pairs occur explicitly somewhere in the source. No pair is missing.

## Three-sector irreducibility audit

Every one of the 165 triplets contains at least one explicit coefficient whose index spans all three sectors of that chart.

Therefore:

- explicit three-sector charts with no triple coefficient: 0
- explicit three-sector charts with at least one triple coefficient: 165

Breakdown:

- 45 triplets containing E have 2 explicit three-sector coefficient symbols in the written scalar/gauge equations;
- 120 triplets not containing E have 3 explicit three-sector coefficient symbols.

Thus none of the 165 charts is reducible, as written, to purely one- and two-sector couplings unless its three-sector coefficients are set to zero by an additional parameter choice.

For gravity-containing charts, `T_mu_nu^(int)` may also contain an additional irreducible three-sector stress contribution, but its detailed decomposition is not specified in the source.

## Interpretation

This establishes a source-level interaction inventory, not empirical nonzero values. A named coefficient appearing in the equations is a permitted independent interaction term; the source does not provide measured values showing that every coefficient is physically nonzero.

The strongest justified statement is:

> The written FieldSpace model contains an explicit three-sector interaction channel in every one of its 165 triplet charts, and contains all 55 possible pairwise sector channels.

Combined with the gluing reconstruction, the source therefore has the full combinatorial support of a <=3-sector global interaction model.

