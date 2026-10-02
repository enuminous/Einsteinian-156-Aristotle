# Explicit Global FieldSpace Reconstruction

This file makes the constructive content of `fieldSpace_atlas_gluing` explicit for the 11-sector
FieldSpace atlas.

## Conditional premise

The reconstruction is valid for the actual 165-chart source provided the two support conditions
identified in `GLUING_AUDIT.md` hold:

1. each genuine three-sector mixed current `Ξ^ν_{ijk}` vanishes when any required sector is
   removed;
2. each `T^(int)_{ijk}` restricts on a two-sector slice to a chart-independent
   `T^(int)_{ij}`, with any genuine three-sector remainder vanishing when the third sector is zero.

Under those conditions the source passed all 1,980 shared-pair overlap obligations.

## Explicit reconstruction

Let `f_T(φ)` denote the residual vector of the local equations on triplet chart `T`.
For every sector subset `S` with `|S| ≤ 3`, choose any triplet `τ(S)` containing `S`.
Gluing compatibility makes the answer independent of this carrier choice.

Define the Möbius component

```
h_S(φ) = Σ_{U ⊆ S} (-1)^(|S|-|U|) f_{τ(S)}(φ|_U).
```

Here `φ|_U` means that every sector outside `U` is set to zero.

The reconstructed global theory is

```
F_global(φ) = Σ_{S ⊆ V, |S|≤3} h_S(φ).
```

For the 11-sector set `V={E,M,S,F,W,T,I,R,H,P,A}`, this contains exactly

- 1 zero-body component;
- 11 one-sector components;
- 55 two-sector components;
- 165 three-sector components;

for **232 Möbius components total**.

### Components by order

For a single sector `i`:

```
h_i = f(φ_i) - f(0).
```

For a pair `{i,j}`:

```
h_ij = f(φ_i,φ_j) - f(φ_i,0) - f(0,φ_j) + f(0,0).
```

For a triplet `{i,j,k}`:

```
h_ijk =
  f(φ_i,φ_j,φ_k)
- f(φ_i,φ_j,0)
- f(φ_i,0,φ_k)
- f(0,φ_j,φ_k)
+ f(φ_i,0,0)
+ f(0,φ_j,0)
+ f(0,0,φ_k)
- f(0,0,0).
```

The carrier chart used for lower-order terms is irrelevant if the gluing law holds.

## Reconstruction identity

For every one of the 165 triplets `T`,

```
F_global(φ|_T) = f_T(φ|_T).
```

This is Möbius inversion. It is exactly the restriction property proved in
`RequestProject/FieldSpace/Gluing.lean`.

Therefore, conditional on the two support rules above, the 165-chart atlas determines **one and
only one** global theory containing no interactions of order greater than three.

## What has actually been reconstructed

This is an explicit mathematical reconstruction of the global residual/equation object. It is
not yet a master Lagrangian and it does not resolve the independent FS-C03 conservation
obstruction. A global action requires the separate reciprocity/integrability conditions proved in
`Reciprocity.lean`.

The accompanying `GLOBAL_RECONSTRUCTION_MAP.csv` lists all 232 components and a deterministic
carrier triplet for each lower-order subset.
