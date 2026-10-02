module

public import RequestProject.FieldSpace.SourceData

/-!
# FS-T05: statement inventory, checked against the source file

We define the statement grammar a block *should* have, given its triplet, and check that
every block of the source file follows it, that the headings are exactly the 165 triplets of
the atlas (no duplicates, none missing), and that the resulting inventory is
`45 + 90 + 90 + 360 = 585`.
-/

@[expose] public section

namespace FieldSpace

open Sector

/-- The statements the source grammar prescribes for a triplet `t`: one Einstein equation if
`E ∈ t`; a dynamical equation and a Bianchi identity for each gauge sector in `t`; and one
scalar equation for each scalar sector in `t`. Returned as a multiset (order is irrelevant). -/
def expectedStmts (t : Finset Sector) : Multiset Stmt :=
  (if E ∈ t then {Stmt.einstein} else 0) +
  ((t.filter (fun s => s.kind = .gauge)).val.bind fun g => {Stmt.gaugeDynamics g, Stmt.bianchi g}) +
  (t.filter (fun s => s.kind = .scalar)).val.map Stmt.scalar

/-- The heading of a block, as a set of sectors. -/
def Block.triplet (b : Block) : Finset Sector := b.heading.toFinset

/-- Every block heading names three distinct sectors. -/
theorem sourceBlocks_heading_nodup : ∀ b ∈ sourceBlocks, b.heading.Nodup ∧ b.heading.length = 3 := by
  decide +kernel

/-- The source headings are pairwise distinct triplets. -/
theorem sourceBlocks_triplets_nodup : (sourceBlocks.map Block.triplet).Nodup := by
  decide +kernel

/-- The source headings are exactly the 165 triplets of the complete atlas. -/
theorem sourceBlocks_triplets_eq_atlas : (sourceBlocks.map Block.triplet).toFinset = tripletAtlas := by
  decide +kernel

/-- Every block of the source contains exactly the statements prescribed by the grammar. -/
theorem sourceBlocks_follow_grammar :
    ∀ b ∈ sourceBlocks, (b.stmts : Multiset Stmt) = expectedStmts b.triplet := by
  decide +kernel

/-- All displayed statements of the source file. -/
def allStmts : List Stmt := sourceBlocks.flatMap Block.stmts

def countEinstein : ℕ := allStmts.countP (· matches .einstein)
def countGaugeDynamics : ℕ := allStmts.countP (· matches .gaugeDynamics _)
def countBianchi : ℕ := allStmts.countP (· matches .bianchi _)
def countScalar : ℕ := allStmts.countP (· matches .scalar _)

/-- **FS-T05** (statement inventory) for the restored source file:
45 Einstein, 90 gauge-dynamical, 90 Bianchi and 360 scalar statements, 585 in total. -/
theorem source_inventory :
    countEinstein = 45 ∧ countGaugeDynamics = 90 ∧ countBianchi = 90 ∧ countScalar = 360 ∧
      allStmts.length = 585 := by
  decide +kernel

/-- **FS-T05**, grammar-level version: summing the prescribed statement counts over the
complete atlas gives 585, independently of the source file. -/
theorem expected_inventory :
    (tripletAtlas.val.map fun t => Multiset.card (expectedStmts t)).sum = 585 := by
  decide +kernel

/-- Every sector heads exactly 45 blocks in the source file. -/
theorem source_sector_incidence (s : Sector) :
    (sourceBlocks.filter fun b => s ∈ b.heading).length = 45 := by
  revert s; decide +kernel

end FieldSpace
