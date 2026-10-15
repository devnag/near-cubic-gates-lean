import Proof.CaseAnalysis.RowsPreparationBounds

/-! One concrete preparation capacity covers every degree of every
polynomial whose monomial count fits the shared digit width. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationFits
open CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scale_fields (n p F w N Q : ℕ) :
    1 ≤ scale n p F w N Q ∧ n ≤ scale n p F w N Q ∧ p ≤ scale n p F w N Q ∧
      F ≤ scale n p F w N Q ∧ w ≤ scale n p F w N Q ∧ N ≤ scale n p F w N Q ∧
      Q+1 ≤ scale n p F w N Q := by unfold scale; omega

theorem selected_length (w M k : ℕ) : (RowTupleSubsets.selected w M k).length ≤ 2^(w*k) := by
  have h := List.length_filter_le (RowTupleSubsets.valid M) (RowTupleDigits.candidates w k)
  simpa only [RowTupleSubsets.selected,RowTupleDigits.candidates,List.length_map,List.length_range] using h

theorem list_budget {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w k S : ℕ) (rows : List (List Bool))
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w)
    (hn : n ≤ S) (hN : gs.length ≤ S) (hp : p ≤ S) (hF : F ≤ S)
    (hw : w ≤ S) (hk : k ≤ S) (hS : 1 ≤ S) :
    RowTupleCutList.budget gs p F w rows.length rows (RowTupleSubsets.selected w rows.length k) ≤
      2^(w*k)*(1024*2^w*S^3)+1 := by
  have hb : ∀ ds∈RowTupleSubsets.selected w rows.length k,
      RowTupleCutBody.budget gs p F w rows.length rows ds+2 ≤ 1024*2^w*S^3 := by
    intro ds hd
    obtain ⟨hlen,hvalid⟩ := RowTupleSelectedList.selected_fields w rows.length k ds hd
    have h := tuple_budget gs p F w rows.length rows ds hl hvalid
    rw [hlen] at h
    exact h.trans (tuple_envelope_le n gs.length p F w rows.length k (2^w) S
      hn hN hp hF hw hk hM Nat.one_le_two_pow hS)
  have hs := RowBinLift.sum_le_length_mul
    ((RowTupleSubsets.selected w rows.length k).map (fun ds=>RowTupleCutBody.budget gs p F w rows.length rows ds+2))
    (1024*2^w*S^3) (by
      intro x hx
      obtain ⟨ds,hd,rfl⟩ := List.mem_map.mp hx
      exact hb ds hd)
  rw [List.length_map] at hs
  unfold RowTupleCutList.budget
  exact Nat.add_le_add_right (hs.trans (Nat.mul_le_mul_right _ (selected_length w rows.length k))) 1

theorem computed_fits {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool))
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j<Q) :
    CloseoutRowsComputedCuts.budget gs p F w j rows+1 ≤ capacity n p F w gs.length Q := by
  let S := scale n p F w gs.length Q
  obtain ⟨hS,hn,hp,hF,hw,hN,hQ⟩ := scale_fields n p F w gs.length Q
  have hk : j+1 ≤ S := by dsimp only [S]; omega
  have hE : 1 ≤ 2^(w*Q) := Nat.one_le_two_pow
  have hU : 1 ≤ 2^w := Nat.one_le_two_pow
  have he := enumeration_le w (j+1) Q S hw hk (by omega) hS
  have hlb := list_budget gs p F w (j+1) S rows hl hM hn hN hp hF hw hk hS
  have hpow : 2^(w*(j+1)) ≤ 2^(w*Q) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w (by omega))
  have hlist := hlb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hpow) 1)
  have h24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h34 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h14 : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 4 by decide)
  have hp1 : S ≤ 2^(w*Q)*2^w*S^4 := by
    calc
      S ≤ S^4 := h14
      _ ≤ 2^(w*Q)*2^w*S^4 := by nlinarith [Nat.mul_le_mul_right (S^4) (Nat.mul_le_mul hE hU)]
  have hp2 : 2^(w*Q)*S^2 ≤ 2^(w*Q)*2^w*S^4 := by
    calc
      _ ≤ 2^(w*Q)*S^4 := Nat.mul_le_mul_left _ h24
      _ ≤ 2^(w*Q)*2^w*S^4 := by nlinarith [Nat.mul_le_mul_left (2^(w*Q)*S^4) hU]
  have hp3 : 2^(w*Q)*2^w*S^3 ≤ 2^(w*Q)*2^w*S^4 := Nat.mul_le_mul_left _ h34
  have hcap : capacity n p F w gs.length Q=4096*(2^(w*Q)*2^w*S^4) := by
    unfold capacity
    rw [Nat.mul_add,Nat.mul_one,pow_add]
    dsimp only [S]
    ring
  rw [hcap]
  change (6*j+8*p+43)+1+(RowTupleEnumerationReady.budget w (j+1)+1+
    RowTupleCutList.budget gs p F w rows.length rows (RowTupleSubsets.selected w rows.length (j+1)))+1 ≤ _
  change p ≤ S at hp
  change 1 ≤ S at hS
  nlinarith

theorem cursor_fits (n p F w N Q M k : ℕ)
    (hM : M ≤ 2^w) (hk : k ≤ Q+1) :
    RowTupleCursorReady.capacity N w M k ≤ capacity n p F w N Q := by
  let S := scale n p F w N Q
  obtain ⟨hS,hn,hp,hF,hw,hN,hQ⟩ := scale_fields n p F w N Q
  have h := tuple_envelope_le n N p F w M k (2^w) S hn hN hp hF hw
    (hk.trans hQ) hM Nat.one_le_two_pow hS
  have hbase : RowTupleCursorReady.capacity N w M k ≤ tupleEnvelope n N p F w M k := by unfold tupleEnvelope; omega
  have h34 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have he : 2^w ≤ 2^(w*(Q+1)) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  calc
    _ ≤ 1024*2^w*S^3 := hbase.trans h
    _ ≤ 4096*2^(w*(Q+1))*S^4 := by gcongr; omega
    _ = capacity n p F w N Q := by unfold capacity; dsimp only [S]; ring

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationFits
