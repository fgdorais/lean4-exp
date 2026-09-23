/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.BitSet.Basic
public import Extra.BitSet.Lemmas
public import Extra.Fin.Sum

/-!
# Cardinality of bit sets

`Extra.BitSet.card x` is the number of elements of `x`, counted by summing its
bits. Note this is unrelated to the width `w`, which bounds it.
-/

public section

namespace Extra.BitSet

@[simp, grind =]
theorem card_empty : (∅ : BitSet w).card = 0 := by
  simp only [card, toBitVec_empty]
  have : (fun i : Fin w => (0#w)[i].toNat) = fun _ => 0 := by funext i; simp
  rw [this, Fin.sum_const]; lia

@[simp, grind =]
theorem card_univ : (univ : BitSet w).card = w := by
  simp only [card, toBitVec_univ]
  have : (fun i : Fin w => (BitVec.allOnes w)[i].toNat) = fun _ => 1 := by funext i; simp
  rw [this, Fin.sum_const]; lia

@[simp, grind =]
theorem card_singleton (i : Fin w) : (singleton i).card = 1 := by
  simp only [card, toBitVec_singleton]
  have h : (fun j : Fin w => (BitVec.twoPow w i)[j].toNat)
         = fun j => if j = i then 1 else 0 := by
    funext j
    by_cases hji : j = i
    · simp [BitVec.getElem_twoPow, hji]
    · simp [BitVec.getElem_twoPow, hji]
      exact fun h => hji (Fin.ext h)
  rw [h, Fin.sum_ite_eq]

theorem card_le_card_of_subset {x y : BitSet w} : x ⊆ y → x.card ≤ y.card := by
  intro h
  simp only [card]
  apply Fin.sum_le_sum
  intro i
  cases hx : x.toBitVec[i.val] with
  | false => simp
  | true =>
    have hmem : i ∈ y := subset_def.mp h (mem_def.mpr (by simp [hx]))
    rw [mem_def] at hmem
    simp [hmem]

theorem card_le (x : BitSet w) : x.card ≤ w := by
  lia [card_le_card_of_subset (subset_univ x), card_univ (w := w)]

theorem card_inter_le_left (x y : BitSet w) : (x ∩ y).card ≤ x.card :=
  card_le_card_of_subset (inter_subset_left x y)

theorem card_inter_le_right (x y : BitSet w) : (x ∩ y).card ≤ y.card :=
  card_le_card_of_subset (inter_subset_right x y)

theorem card_le_card_union_left (x y : BitSet w) : x.card ≤ (x ∪ y).card :=
  card_le_card_of_subset (subset_union_left x y)

theorem card_le_card_union_right (x y : BitSet w) : y.card ≤ (x ∪ y).card :=
  card_le_card_of_subset (subset_union_right x y)

theorem card_sub_le (x y : BitSet w) : (x - y).card ≤ x.card :=
  card_le_card_of_subset (sub_subset x y)

theorem card_eq_zero_iff {x : BitSet w} : x.card = 0 ↔ x = ∅ := by
  constructor
  · intro h
    rw [eq_empty_iff_forall_not_mem]
    intro i hi
    lia [card_le_card_of_subset (singleton_subset_iff_mem.mpr hi), card_singleton i]
  · rintro rfl
    exact card_empty

/-- Inclusion-exclusion. -/
theorem card_union_add_card_inter (x y : BitSet w) :
    (x ∪ y).card + (x ∩ y).card = x.card + y.card := by
  simp only [card]
  rw [← Fin.sum_add_sum, ← Fin.sum_add_sum]
  congr 1
  funext i
  simp only [toBitVec_union, toBitVec_inter]
  cases hx : x.toBitVec[i.val] <;> cases hy : y.toBitVec[i.val] <;> simp [hx, hy]

theorem card_union (x y : BitSet w) :
    (x ∪ y).card = x.card + y.card - (x ∩ y).card := by
  grind [card_union_add_card_inter]

theorem card_union_le_card_add_card (x y : BitSet w) : (x ∪ y).card ≤ x.card + y.card := by
  lia [card_union x y]

theorem card_union_eq_card_add_card_iff_disjoint {x y : BitSet w} :
    (x ∪ y).card = x.card + y.card ↔ x ∩ y = ∅ := by
  constructor
  · intro h
    exact card_eq_zero_iff.mp (by lia [card_union_add_card_inter x y])
  · intro hd
    lia [card_union_add_card_inter x y, card_empty (w := w)]

theorem card_inter (x y : BitSet w) :
  (x ∩ y).card = x.card + y.card - (x ∪ y).card := by
  grind [card_union_add_card_inter]

theorem card_neg (x : BitSet w) : (-x).card = w - x.card := by
  lia [card_union_add_card_inter x (-x), union_neg_self x, inter_neg_self x,
       card_univ (w := w), card_empty (w := w)]

theorem card_sub (x y : BitSet w) : (x - y).card = x.card - (x ∩ y).card := by
  lia [card_union_add_card_inter (x - y) (x ∩ y), sub_union_inter x y, sub_inter_inter x y,
       card_empty (w := w)]
