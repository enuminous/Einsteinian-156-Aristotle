module

public import RequestProject.FieldSpace.Basic

/-!
# The FieldSpace source file, as data

`sourceBlocks` records, for each `=== Triplet (...) ===` heading of
`source/EFMW_165_field_equations.txt` (in file order), the three sectors of the heading and
the kinds of displayed statements in that block:

* `GR (Einstein): ...`              ↦ `.einstein`
* `X-gauge:` then `∇_μ ... = ...`   ↦ `.gaugeDynamics X`
* `X-gauge:` then `∇_[μ ... = 0`    ↦ `.bianchi X`
* `Scalar X: ...`                   ↦ `.scalar X`

The data was transcribed mechanically from the source file; the equations' contents are not
modelled, only the statement kinds.
-/

@[expose] public section

namespace FieldSpace

/-- The kinds of displayed statement in the source grammar. -/
inductive Stmt
  | einstein
  | gaugeDynamics (g : Sector)
  | bianchi (g : Sector)
  | scalar (s : Sector)
  deriving DecidableEq, Repr

/-- One `=== Triplet ===` block of the source file. -/
structure Block where
  heading : List Sector
  stmts : List Stmt
  deriving DecidableEq, Repr

open Sector in
/-- All 165 blocks of `source/EFMW_165_field_equations.txt`, in file order. -/
def sourceBlocks : List Block := [
  ⟨[.E, .F, .M], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .F)]⟩,
  ⟨[.E, .F, .W], [(.einstein), (.scalar .F), (.scalar .W)]⟩,
  ⟨[.E, .F, .T], [(.einstein), (.scalar .F), (.scalar .T)]⟩,
  ⟨[.E, .F, .I], [(.einstein), (.scalar .F), (.scalar .I)]⟩,
  ⟨[.E, .F, .R], [(.einstein), (.scalar .F), (.scalar .R)]⟩,
  ⟨[.E, .F, .S], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .F)]⟩,
  ⟨[.E, .F, .H], [(.einstein), (.scalar .F), (.scalar .H)]⟩,
  ⟨[.E, .F, .P], [(.einstein), (.scalar .F), (.scalar .P)]⟩,
  ⟨[.E, .F, .A], [(.einstein), (.scalar .F), (.scalar .A)]⟩,
  ⟨[.E, .M, .W], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .W)]⟩,
  ⟨[.E, .M, .T], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .T)]⟩,
  ⟨[.E, .M, .I], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .I)]⟩,
  ⟨[.E, .M, .R], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .R)]⟩,
  ⟨[.E, .M, .S], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S)]⟩,
  ⟨[.E, .M, .H], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .H)]⟩,
  ⟨[.E, .M, .P], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .P)]⟩,
  ⟨[.E, .M, .A], [(.einstein), (.gaugeDynamics .M), (.bianchi .M), (.scalar .A)]⟩,
  ⟨[.E, .W, .T], [(.einstein), (.scalar .W), (.scalar .T)]⟩,
  ⟨[.E, .W, .I], [(.einstein), (.scalar .W), (.scalar .I)]⟩,
  ⟨[.E, .W, .R], [(.einstein), (.scalar .W), (.scalar .R)]⟩,
  ⟨[.E, .W, .S], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .W)]⟩,
  ⟨[.E, .W, .H], [(.einstein), (.scalar .W), (.scalar .H)]⟩,
  ⟨[.E, .W, .P], [(.einstein), (.scalar .W), (.scalar .P)]⟩,
  ⟨[.E, .W, .A], [(.einstein), (.scalar .W), (.scalar .A)]⟩,
  ⟨[.E, .T, .I], [(.einstein), (.scalar .T), (.scalar .I)]⟩,
  ⟨[.E, .T, .R], [(.einstein), (.scalar .T), (.scalar .R)]⟩,
  ⟨[.E, .T, .S], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .T)]⟩,
  ⟨[.E, .T, .H], [(.einstein), (.scalar .T), (.scalar .H)]⟩,
  ⟨[.E, .T, .P], [(.einstein), (.scalar .T), (.scalar .P)]⟩,
  ⟨[.E, .T, .A], [(.einstein), (.scalar .T), (.scalar .A)]⟩,
  ⟨[.E, .I, .R], [(.einstein), (.scalar .I), (.scalar .R)]⟩,
  ⟨[.E, .I, .S], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .I)]⟩,
  ⟨[.E, .I, .H], [(.einstein), (.scalar .I), (.scalar .H)]⟩,
  ⟨[.E, .I, .P], [(.einstein), (.scalar .I), (.scalar .P)]⟩,
  ⟨[.E, .I, .A], [(.einstein), (.scalar .I), (.scalar .A)]⟩,
  ⟨[.E, .R, .S], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .R)]⟩,
  ⟨[.E, .R, .H], [(.einstein), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.E, .R, .P], [(.einstein), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.E, .R, .A], [(.einstein), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.E, .S, .H], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .H)]⟩,
  ⟨[.E, .S, .P], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .P)]⟩,
  ⟨[.E, .S, .A], [(.einstein), (.gaugeDynamics .S), (.bianchi .S), (.scalar .A)]⟩,
  ⟨[.E, .H, .P], [(.einstein), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.E, .H, .A], [(.einstein), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.E, .P, .A], [(.einstein), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.F, .M, .W], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .W)]⟩,
  ⟨[.F, .M, .T], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .T)]⟩,
  ⟨[.F, .M, .I], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .I)]⟩,
  ⟨[.F, .M, .R], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .R)]⟩,
  ⟨[.F, .M, .S], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .F)]⟩,
  ⟨[.F, .M, .H], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .H)]⟩,
  ⟨[.F, .M, .P], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .P)]⟩,
  ⟨[.F, .M, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .F), (.scalar .A)]⟩,
  ⟨[.F, .W, .T], [(.scalar .F), (.scalar .W), (.scalar .T)]⟩,
  ⟨[.F, .W, .I], [(.scalar .F), (.scalar .W), (.scalar .I)]⟩,
  ⟨[.F, .W, .R], [(.scalar .F), (.scalar .W), (.scalar .R)]⟩,
  ⟨[.F, .W, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .W)]⟩,
  ⟨[.F, .W, .H], [(.scalar .F), (.scalar .W), (.scalar .H)]⟩,
  ⟨[.F, .W, .P], [(.scalar .F), (.scalar .W), (.scalar .P)]⟩,
  ⟨[.F, .W, .A], [(.scalar .F), (.scalar .W), (.scalar .A)]⟩,
  ⟨[.F, .T, .I], [(.scalar .F), (.scalar .T), (.scalar .I)]⟩,
  ⟨[.F, .T, .R], [(.scalar .F), (.scalar .T), (.scalar .R)]⟩,
  ⟨[.F, .T, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .T)]⟩,
  ⟨[.F, .T, .H], [(.scalar .F), (.scalar .T), (.scalar .H)]⟩,
  ⟨[.F, .T, .P], [(.scalar .F), (.scalar .T), (.scalar .P)]⟩,
  ⟨[.F, .T, .A], [(.scalar .F), (.scalar .T), (.scalar .A)]⟩,
  ⟨[.F, .I, .R], [(.scalar .F), (.scalar .I), (.scalar .R)]⟩,
  ⟨[.F, .I, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .I)]⟩,
  ⟨[.F, .I, .H], [(.scalar .F), (.scalar .I), (.scalar .H)]⟩,
  ⟨[.F, .I, .P], [(.scalar .F), (.scalar .I), (.scalar .P)]⟩,
  ⟨[.F, .I, .A], [(.scalar .F), (.scalar .I), (.scalar .A)]⟩,
  ⟨[.F, .R, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .R)]⟩,
  ⟨[.F, .R, .H], [(.scalar .F), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.F, .R, .P], [(.scalar .F), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.F, .R, .A], [(.scalar .F), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.F, .S, .H], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .H)]⟩,
  ⟨[.F, .S, .P], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .P)]⟩,
  ⟨[.F, .S, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .F), (.scalar .A)]⟩,
  ⟨[.F, .H, .P], [(.scalar .F), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.F, .H, .A], [(.scalar .F), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.F, .P, .A], [(.scalar .F), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.M, .W, .T], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .W), (.scalar .T)]⟩,
  ⟨[.M, .W, .I], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .W), (.scalar .I)]⟩,
  ⟨[.M, .W, .R], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .W), (.scalar .R)]⟩,
  ⟨[.M, .W, .S], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .W)]⟩,
  ⟨[.M, .W, .H], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .W), (.scalar .H)]⟩,
  ⟨[.M, .W, .P], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .W), (.scalar .P)]⟩,
  ⟨[.M, .W, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .W), (.scalar .A)]⟩,
  ⟨[.M, .T, .I], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .T), (.scalar .I)]⟩,
  ⟨[.M, .T, .R], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .T), (.scalar .R)]⟩,
  ⟨[.M, .T, .S], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .T)]⟩,
  ⟨[.M, .T, .H], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .T), (.scalar .H)]⟩,
  ⟨[.M, .T, .P], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .T), (.scalar .P)]⟩,
  ⟨[.M, .T, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .T), (.scalar .A)]⟩,
  ⟨[.M, .I, .R], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .I), (.scalar .R)]⟩,
  ⟨[.M, .I, .S], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .I)]⟩,
  ⟨[.M, .I, .H], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .I), (.scalar .H)]⟩,
  ⟨[.M, .I, .P], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .I), (.scalar .P)]⟩,
  ⟨[.M, .I, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .I), (.scalar .A)]⟩,
  ⟨[.M, .R, .S], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .R)]⟩,
  ⟨[.M, .R, .H], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.M, .R, .P], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.M, .R, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.M, .S, .H], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .H)]⟩,
  ⟨[.M, .S, .P], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .P)]⟩,
  ⟨[.M, .S, .A], [(.gaugeDynamics .M), (.bianchi .M), (.gaugeDynamics .S), (.bianchi .S), (.scalar .A)]⟩,
  ⟨[.M, .H, .P], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.M, .H, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.M, .P, .A], [(.gaugeDynamics .M), (.bianchi .M), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.W, .T, .I], [(.scalar .W), (.scalar .T), (.scalar .I)]⟩,
  ⟨[.W, .T, .R], [(.scalar .W), (.scalar .T), (.scalar .R)]⟩,
  ⟨[.W, .T, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .W), (.scalar .T)]⟩,
  ⟨[.W, .T, .H], [(.scalar .W), (.scalar .T), (.scalar .H)]⟩,
  ⟨[.W, .T, .P], [(.scalar .W), (.scalar .T), (.scalar .P)]⟩,
  ⟨[.W, .T, .A], [(.scalar .W), (.scalar .T), (.scalar .A)]⟩,
  ⟨[.W, .I, .R], [(.scalar .W), (.scalar .I), (.scalar .R)]⟩,
  ⟨[.W, .I, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .W), (.scalar .I)]⟩,
  ⟨[.W, .I, .H], [(.scalar .W), (.scalar .I), (.scalar .H)]⟩,
  ⟨[.W, .I, .P], [(.scalar .W), (.scalar .I), (.scalar .P)]⟩,
  ⟨[.W, .I, .A], [(.scalar .W), (.scalar .I), (.scalar .A)]⟩,
  ⟨[.W, .R, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .W), (.scalar .R)]⟩,
  ⟨[.W, .R, .H], [(.scalar .W), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.W, .R, .P], [(.scalar .W), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.W, .R, .A], [(.scalar .W), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.W, .S, .H], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .W), (.scalar .H)]⟩,
  ⟨[.W, .S, .P], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .W), (.scalar .P)]⟩,
  ⟨[.W, .S, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .W), (.scalar .A)]⟩,
  ⟨[.W, .H, .P], [(.scalar .W), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.W, .H, .A], [(.scalar .W), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.W, .P, .A], [(.scalar .W), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.T, .I, .R], [(.scalar .T), (.scalar .I), (.scalar .R)]⟩,
  ⟨[.T, .I, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .T), (.scalar .I)]⟩,
  ⟨[.T, .I, .H], [(.scalar .T), (.scalar .I), (.scalar .H)]⟩,
  ⟨[.T, .I, .P], [(.scalar .T), (.scalar .I), (.scalar .P)]⟩,
  ⟨[.T, .I, .A], [(.scalar .T), (.scalar .I), (.scalar .A)]⟩,
  ⟨[.T, .R, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .T), (.scalar .R)]⟩,
  ⟨[.T, .R, .H], [(.scalar .T), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.T, .R, .P], [(.scalar .T), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.T, .R, .A], [(.scalar .T), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.T, .S, .H], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .T), (.scalar .H)]⟩,
  ⟨[.T, .S, .P], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .T), (.scalar .P)]⟩,
  ⟨[.T, .S, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .T), (.scalar .A)]⟩,
  ⟨[.T, .H, .P], [(.scalar .T), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.T, .H, .A], [(.scalar .T), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.T, .P, .A], [(.scalar .T), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.I, .R, .S], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .I), (.scalar .R)]⟩,
  ⟨[.I, .R, .H], [(.scalar .I), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.I, .R, .P], [(.scalar .I), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.I, .R, .A], [(.scalar .I), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.I, .S, .H], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .I), (.scalar .H)]⟩,
  ⟨[.I, .S, .P], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .I), (.scalar .P)]⟩,
  ⟨[.I, .S, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .I), (.scalar .A)]⟩,
  ⟨[.I, .H, .P], [(.scalar .I), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.I, .H, .A], [(.scalar .I), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.I, .P, .A], [(.scalar .I), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.R, .S, .H], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .R), (.scalar .H)]⟩,
  ⟨[.R, .S, .P], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .R), (.scalar .P)]⟩,
  ⟨[.R, .S, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .R), (.scalar .A)]⟩,
  ⟨[.R, .H, .P], [(.scalar .R), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.R, .H, .A], [(.scalar .R), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.R, .P, .A], [(.scalar .R), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.S, .H, .P], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .H), (.scalar .P)]⟩,
  ⟨[.S, .H, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .H), (.scalar .A)]⟩,
  ⟨[.S, .P, .A], [(.gaugeDynamics .S), (.bianchi .S), (.scalar .P), (.scalar .A)]⟩,
  ⟨[.H, .P, .A], [(.scalar .H), (.scalar .P), (.scalar .A)]⟩
]

end FieldSpace
