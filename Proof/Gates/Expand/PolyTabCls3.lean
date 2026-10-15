import Proof.Gates.Expand.PolyTabCls2

/-! # PolyTab cost classes: the head's output and sum atoms -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine

variable (E : ExpandMachine)

theorem flatMap_frame_len (W : ℕ) (L : List ℕ) : ((L.map (binary W)).flatMap frame).length = L.length * (2 * W + 1) := by
  rw [List.flatMap_map, flatMap_len_const _ _ (2 * W + 1) (fun x _ => by rw [frame_length, binary_length])]

theorem codeRecs_len (r : TabReq) : (codeRecs (tsK E r)).length ≤ (E.expand ⟨r.V, r.F⟩).length * (1 + r.V * (r.k + r.s + 2)) := by
  unfold codeRecs
  rw [List.length_flatMap]
  have h := sum_le_len_mul (tsK E r) (fun t => (blkRecs t).length) (1 + r.V * (r.k + r.s + 2)) (fun t ht => by
    rw [tsK_eq] at ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
    simp only [blkRecs, List.length_cons, List.length_flatMap, List.length_reverse, List.length_map]
    have h1 : ((((mvars u).map (occ (tabT E r))).reverse.map fun o => (occRecs o).length)).sum =
        (mvars u).length * (r.k + r.s + 2) := by
      rw [List.map_reverse, List.sum_reverse, List.map_map]
      rw [show ((fun o => (occRecs o).length) ∘ occ (tabT E r)) = fun _ => r.k + r.s + 2 from funext fun v => by
        simp only [Function.comp, occRecs_length, occLen, occ_inW_length, occ_outW_length]; try ring]
      simp
    have h2 : (mvars u).length ≤ r.V := by have := mvars_len u; simpa using this
    rw [h1]
    have := Nat.mul_le_mul_right (r.k + r.s + 2) h2
    omega)
  have e : (tsK E r).length = (E.expand ⟨r.V, r.F⟩).length := by rw [tsK_eq]; simp
  rw [e] at h; simpa using h

theorem lc_O46 : LCls 1 (fun r => ((ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r))).length) := by
  refine lc_mono (f := fun r => (E.expand ⟨r.V, r.F⟩).length * (1 + r.V * (r.k + r.s + 2)) * (2 * (Wk E r + 1) + 1))
    ?_ (fun r => ?_)
  · have := lc_P E; have := lc_V; have := lc_k; have := lc_s; have := lc_Wk E; lcs_to
  rw [blk46_eq, flatMap_frame_len]
  exact Nat.mul_le_mul_right _ (codeRecs_len E r)

theorem lc_O56 : LCls 1 (fun r => ((ts9 E r).flatMap (blk56 (Wdk E r + 1))).length) := by
  refine lc_mono (f := fun r => (E.expand ⟨r.V, r.F⟩).length * (2 * (Wdk E r + 1) + 1)) ?_ (fun r => ?_)
  · have := lc_P E; have := lc_Wdk E; lcs_to
  rw [blk56_eq, coefRecs, List.flatMap_map, flatMap_len_const _ _ (2 * (Wdk E r + 1) + 1) (fun x _ => by
    simp only [Function.comp_apply, frame_length, binary_length, ← Wdk_succ])]
  simp [tsK_eq]

theorem lc_vtRecs : LCls 0 (fun r => (vtRecs (Wk E r + 1) E r r.V).length) := by
  refine lc_mono (f := fun r => r.V * ((r.k + r.s + 2) * (2 * (Wk E r + 1) + 1))) ?_
    (fun r => by rw [vtRecs_length _ E r r.V le_rfl])
  have := lc_V; have := lc_k; have := lc_s; have := lc_Wk E; lcs_to

/-- A polynomial bound of one monomial's copy cost. -/
def cmB (r : TabReq) : ℕ :=
  (r.V + 3) * (40 * (2 * r.V + 2) + 40) + 1 + ((r.V + 11) * (100 * r.V + 200) + 1 + (r.V * (60 * (2 * r.V + 3) + 64) +
    1)) + 1 + (60 * (2 * r.F.weight + 9) + 121)

theorem cpMono_le (r : TabReq) (t : Finset (Fin r.V) × ℤ) (ht : t ∈ E.expand ⟨r.V, r.F⟩) : cpMonoCost t ≤ cmB r := by
  unfold cpMonoCost Codec.copyListCost cmB
  set m := ((t.1.sort (· ≤ ·)).map Fin.val).length with hm
  have hmV : m ≤ r.V := mvars_len t
  have h1 : natBitLength m ≤ r.V + 1 := (natBitLength_le' m).trans (by omega)
  have h2 : 2 ^ natBitLength m ≤ 2 * r.V + 2 := (two_pow_nbl m).trans (by omega)
  have h3 : (((((t.1.sort (· ≤ ·)).map Fin.val).map fun x => 60 * (natWord x).length + 60).map fun c => c + 4)).sum ≤
      r.V * (60 * (2 * r.V + 3) + 64) := by
    rw [List.map_map]
    refine (sum_le_len_mul _ _ (60 * (2 * r.V + 3) + 64) (fun x hx => ?_)).trans ?_
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      simp only [Function.comp, natWord_len]
      have := (natBitLength_le' v.val).trans (show v.val + 1 ≤ r.V + 1 by have := v.isLt; omega)
      omega
    · exact Nat.mul_le_mul_right _ hmV
  have h4 : (Interfaces.intWord t.2).length ≤ 2 * r.F.weight + 9 := by
    have := coef_nbl E r t ht
    have n1 : natBitLength 1 = 1 := by simp [natBitLength]
    have n0 : natBitLength 0 = 1 := by simp [natBitLength]
    by_cases hc : t.2 < 0 <;> simp only [Interfaces.intWord, List.length_append, natWord_len, hc, if_true, if_false, n1, n0] <;>
      omega
  have h5 : (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) ≤ (r.V + 3) * (40 * (2 * r.V + 2) + 40) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h6 : (natBitLength m + 10) * (100 * m + 200) ≤ (r.V + 11) * (100 * r.V + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega
where natBitLength_le' (x : ℕ) : natBitLength x ≤ x + 1 := nbl_le x

theorem lc_cpSum : LCls 1 (fun r => (((E.expand ⟨r.V, r.F⟩).map cpMonoCost).map fun c => c + 4).sum) := by
  refine lc_mono (f := fun r => (E.expand ⟨r.V, r.F⟩).length * (cmB r + 4)) ?_ (fun r => ?_)
  · have := lc_P E; have := lc_V; have := lc_w; unfold cmB; lcs_to
  rw [List.map_map]
  exact sum_le_len_mul _ _ _ (fun t ht => by simp only [Function.comp]; have := cpMono_le E r t ht; omega)

end NearCubicGates.Close.Expand.PolyTab
