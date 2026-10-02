module

public import Mathlib

/-!
# FieldSpace: the 11-sector rank-3 atlas

This file formalizes the *structural* claims of the FieldSpace theorem register
(FS-T01 … FS-T04, FS-T06, FS-T07) as statements about an actual finite type of
sectors and the actual family of its three-element subsets, rather than as bare
arithmetic identities.
-/

@[expose] public section

namespace FieldSpace

/-- The eleven named sectors `E, M, S, F, W, T, I, R, H, P, A`. -/
inductive Sector
  | E | M | S | F | W | T | I | R | H | P | A
  deriving DecidableEq, Fintype, Repr

/-- The three kinds of sector: gravity (`E`), gauge (`M`, `S`), scalar (the rest). -/
inductive Kind
  | gravity | gauge | scalar
  deriving DecidableEq, Fintype, Repr

namespace Sector

/-- The kind of each sector, as declared in the source file header. -/
def kind : Sector → Kind
  | E => .gravity
  | M | S => .gauge
  | _ => .scalar

end Sector

open Sector

/-- The complete rank-3 atlas: all three-element sets of sectors. -/
def tripletAtlas : Finset (Finset Sector) := (Finset.univ : Finset Sector).powersetCard 3

theorem card_sector : Fintype.card Sector = 11 := rfl

theorem mem_atlas {t : Finset Sector} : t ∈ tripletAtlas ↔ t.card = 3 := by
  simp [tripletAtlas, Finset.mem_powersetCard]

/-- **FS-T01** (rank-3 projection count): the tripletAtlas has `C(11,3) = 165` triplets. -/
theorem atlas_card : tripletAtlas.card = 165 := by
  simp [tripletAtlas, Finset.card_powersetCard, card_sector]
  rfl

/-- **FS-T02** (uniform sector incidence): every sector lies in exactly
`C(10,2) = 45` triplets. -/
theorem sector_incidence (s : Sector) : (tripletAtlas.filter (s ∈ ·)).card = 45 := by
  revert s; decide

/-- **FS-T03** (uniform pair incidence): every unordered pair of distinct sectors
lies in exactly 9 triplets. -/
theorem pair_incidence (a b : Sector) (hab : a ≠ b) :
    (tripletAtlas.filter (fun t => a ∈ t ∧ b ∈ t)).card = 9 := by
  revert a b; decide

/-- Number of sectors of a given kind in a triplet. -/
def kindCount (k : Kind) (t : Finset Sector) : ℕ := (t.filter (fun s => s.kind = k)).card

/-- Triplets with exactly `g` gravity sectors and `m` gauge sectors
(the remaining `3 - g - m` being scalar). -/
def tripletClass (g m : ℕ) : Finset (Finset Sector) :=
  tripletAtlas.filter (fun t => kindCount .gravity t = g ∧ kindCount .gauge t = m)

/-- **FS-T04** (six-class decomposition), class sizes. -/
theorem class_three_scalars : (tripletClass 0 0).card = 56 := by decide
theorem class_one_gauge_two_scalars : (tripletClass 0 1).card = 56 := by decide
theorem class_gravity_two_scalars : (tripletClass 1 0).card = 28 := by decide
theorem class_gravity_gauge_scalar : (tripletClass 1 1).card = 16 := by decide
theorem class_two_gauges_scalar : (tripletClass 0 2).card = 8 := by decide
theorem class_gravity_two_gauges : (tripletClass 1 2).card = 1 := by decide

/-- The unique gravity + two gauges triplet is `{E, M, S}`. -/
theorem class_gravity_two_gauges_eq : tripletClass 1 2 = {{E, M, S}} := by decide

/-- **FS-T04** (exhaustiveness): every triplet lies in exactly one of the six classes,
so the six classes partition the tripletAtlas. -/
theorem six_classes_partition (t : Finset Sector) (ht : t ∈ tripletAtlas) :
    ∃! gm : ℕ × ℕ, gm ∈ ({(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2)} : Finset (ℕ × ℕ)) ∧
      t ∈ tripletClass gm.1 gm.2 := by
  refine ⟨(kindCount .gravity t, kindCount .gauge t), ?_, ?_⟩
  · refine ⟨?_, Finset.mem_filter.2 ⟨ht, rfl, rfl⟩⟩
    have hg : kindCount .gravity t ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ t))).trans
        (by decide)
    have hm : kindCount .gauge t ≤ 2 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ t))).trans
        (by decide)
    interval_cases (kindCount .gravity t) <;> interval_cases (kindCount .gauge t) <;> decide
  · rintro ⟨g, m⟩ ⟨-, h⟩
    obtain ⟨-, rfl, rfl⟩ := Finset.mem_filter.1 h
    rfl

/-! ## FS-T06: sector-ablation closure -/

/-- The triplets surviving deletion of a set `X` of sectors. -/
def ablate (X : Finset Sector) : Finset (Finset Sector) :=
  tripletAtlas.filter (fun t => Disjoint t X)

/-- Deleting sectors leaves exactly the complete 3-uniform hypergraph on the
remaining sectors. -/
theorem ablate_eq (X : Finset Sector) : ablate X = Xᶜ.powersetCard 3 := by
  ext t
  simp only [ablate, mem_atlas, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨h3, hd⟩
    exact ⟨fun x hx => Finset.mem_compl.2 (Finset.disjoint_left.1 hd hx), h3⟩
  · rintro ⟨hsub, h3⟩
    exact ⟨h3, Finset.disjoint_left.2 fun x hx => Finset.mem_compl.1 (hsub hx)⟩

/-- **FS-T06**: removing any `k` sectors leaves `C(11-k, 3)` triplets. -/
theorem ablate_card (X : Finset Sector) : (ablate X).card = Nat.choose (11 - X.card) 3 := by
  rw [ablate_eq, Finset.card_powersetCard, Finset.card_compl, card_sector]

theorem ablate_card_one (X : Finset Sector) (h : X.card = 1) :
    (ablate X).card = 120 ∧ tripletAtlas.card - (ablate X).card = 45 := by
  rw [ablate_card, h, atlas_card]; decide

theorem ablate_card_two (X : Finset Sector) (h : X.card = 2) :
    (ablate X).card = 84 ∧ tripletAtlas.card - (ablate X).card = 81 := by
  rw [ablate_card, h, atlas_card]; decide

theorem ablate_card_three (X : Finset Sector) (h : X.card = 3) :
    (ablate X).card = 56 ∧ tripletAtlas.card - (ablate X).card = 109 := by
  rw [ablate_card, h, atlas_card]; decide

/-! ## FS-T07: projection-overlap spectrum -/

/-- Number of sectors shared by the two triplets of an unordered pair. -/
def overlap : Sym2 (Finset Sector) → ℕ :=
  Sym2.lift ⟨fun s t => (s ∩ t).card, fun s t => by simp only [Finset.inter_comm]⟩

/-- Unordered pairs of distinct triplets. -/
def distinctPairs : Finset (Sym2 (Finset Sector)) :=
  tripletAtlas.sym2.filter (fun p => ¬ p.IsDiag)

/-- Unordered pairs of distinct triplets sharing exactly `j` sectors. -/
def overlapPairs (j : ℕ) : Finset (Sym2 (Finset Sector)) :=
  distinctPairs.filter (fun p => overlap p = j)

theorem distinctPairs_card : distinctPairs.card = Nat.choose 165 2 := by decide +kernel

theorem overlapPairs_two : (overlapPairs 2).card = 1980 := by decide +kernel
theorem overlapPairs_one : (overlapPairs 1).card = 6930 := by decide +kernel
theorem overlapPairs_zero : (overlapPairs 0).card = 4620 := by decide +kernel

/-- Two distinct triplets share at most two sectors, so overlaps 0, 1, 2 are exhaustive. -/
theorem overlap_le_two : ∀ p ∈ distinctPairs, overlap p ≤ 2 := by
  rintro ⟨s, t⟩ hp
  simp only [distinctPairs, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
    mem_atlas] at hp
  obtain ⟨⟨hs, ht⟩, hst⟩ := hp
  change (s ∩ t).card ≤ 2
  by_contra h
  have h3 : s.card ≤ (s ∩ t).card := by omega
  have h3' : t.card ≤ (s ∩ t).card := by omega
  exact hst ((Finset.eq_of_subset_of_card_le Finset.inter_subset_left h3).symm.trans
    (Finset.eq_of_subset_of_card_le Finset.inter_subset_right h3'))

/-- **FS-T07**: the overlap classes 2, 1, 0 exhaust all `C(165,2) = 13530` unordered pairs
of distinct triplets. -/
theorem overlap_spectrum :
    (overlapPairs 2).card + (overlapPairs 1).card + (overlapPairs 0).card =
      distinctPairs.card ∧ distinctPairs.card = 13530 := by
  rw [overlapPairs_two, overlapPairs_one, overlapPairs_zero, distinctPairs_card]
  norm_num [Nat.choose_two_right]

end FieldSpace
