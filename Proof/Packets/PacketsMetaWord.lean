import Proof.Packets.PacketsMetaCount
import Proof.CaseAnalysis.RowsRawAtomMeaning

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-- **The field-scan run, word output** (`field_runE` with `replicate v true` generalized to any word `w`). -/
theorem field_runW {e s : ℕ} (M : Machine (2 + e) s) (j : Fin 5) (a : DecompositionAlgorithm) (r : Request)
    (w : List Bool) (n : ℕ) (H1 : Fin (2 + e) → ℕ) (A1 : Fin (2 + e) → List Bool)
    (hM : Step M n (fun _ => 0) (scanIn e (frame (fields a r j))) H1 A1)
    (hv : A1 ⟨1, by omega⟩ = w) :
    ∃ (H' : Fin (2 + (13 + e + 1)) → ℕ) (A' : Fin (2 + (13 + e + 1)) → List Bool),
      Step (fieldMachineE M j) (6*(r.input a).length+17 + 1 + (2*n+2)) (fun _ => 0)
        (inBank (2 + (13 + e + 1)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = w ∧ H' ⟨1, by omega⟩ = 0 := by
  have hA := RequestInputFields.request_run a r
  have d1 := hA.dock (rfE e) (rfE_injective e) (fun _ => 0) (inBank (2 + (13 + e + 1)) (Request.input a r))
    (fun _ => rfl)
    (by
      intro i
      by_cases h : i = 0
      · subst h
        rfl
      · have hv : (rfE e i).val ≠ 0 := by
          unfold rfE
          rw [if_neg (show ¬ (i.val = 0) by intro h'; exact h (Fin.ext h'))]
          simp
        simp only [inBank, hv, if_false, h])
  obtain ⟨k, hm⟩ := step_mask0 hM (fun _ => true) (by intro i _; rfl)
  set ws := RequestInputFields.values a r with hws
  set H1' := dockH (rfE e) (fun _ => 0) (RequestInputFields.heads ws 5) with hH1'
  set A1' := install (rfE e) (inBank (2 + (13 + e + 1)) (Request.input a r))
    (RequestInputFields.bank ws 5) with hA1'
  have hHd : ∀ i : Fin (2 + e + 1), H1' (scE e j i) = Fin.addCases (fun _ : Fin (2 + e) => 0) (fun _ : Fin 1 => 0) i := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · rw [Fin.addCases_left]
      rcases Nat.lt_or_ge i'.val 2 with hi | hi
      · rcases (show i'.val = 0 ∨ i'.val = 1 by omega) with h0 | h1
        · have hc : (Fin.castAdd 1 i' : Fin (2 + e + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp [h0])
          rw [hc, scE_zero, hH1', dockH_slot _ (rfE_injective e), heads_field]
        · have hc : (Fin.castAdd 1 i' : Fin (2 + e + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp [h1])
          rw [hc, scE_one, hH1', dockH_other _ _ _ _ (rfE_ne_one e)]
      · rw [hH1', dockH_other _ _ _ _ (fun i => rfE_ne_big e j _ (by simpa using hi) i)]
    · rw [Fin.addCases_right, hH1', dockH_other _ _ _ _ (fun i => rfE_ne_big e j _ (by simp) i)]
  have hAd : ∀ i : Fin (2 + e + 1), A1' (scE e j i) =
      Fin.addCases (scanIn e (frame (fields a r j))) (fun _ : Fin 1 => ([] : List Bool)) i := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · rw [Fin.addCases_left]
      rcases Nat.lt_or_ge i'.val 2 with hi | hi
      · rcases (show i'.val = 0 ∨ i'.val = 1 by omega) with h0 | h1
        · have hc : (Fin.castAdd 1 i' : Fin (2 + e + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp [h0])
          rw [hc, scE_zero, hA1', install_slot _ (rfE_injective e), bank_field]
          simp [scanIn, h0, hws, fields]
        · have hc : (Fin.castAdd 1 i' : Fin (2 + e + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp [h1])
          rw [hc, scE_one, hA1', install_other _ _ _ _ (rfE_ne_one e)]
          simp [scanIn, inBank, h1]
      · rw [hA1', install_other _ _ _ _ (fun i => rfE_ne_big e j _ (by simpa using hi) i)]
        have : ¬ i'.val = 0 := by omega
        simp only [scanIn, inBank, this, if_false]
        split_ifs with hz
        · exact absurd hz (scE_val_ne_zero e j _)
        · rfl
    · rw [Fin.addCases_right, hA1', install_other _ _ _ _ (fun i => rfE_ne_big e j _ (by simp) i)]
      simp only [inBank]
      split_ifs with hz
      · exact absurd hz (scE_val_ne_zero e j _)
      · rfl
  have d2 := hm.dock (scE e j) (scE_injective e j) H1' A1' hHd hAd
  have hall := d1.seq d2
  have h0 : (⟨0, by omega⟩ : Fin (2 + (13 + e + 1))) = rfE e 0 := rfl
  have h1 : (⟨1, by omega⟩ : Fin (2 + (13 + e + 1))) = scE e j ⟨1, by omega⟩ := (scE_one e j _).symm
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_⟩
  · rw [h0, install_other _ _ _ _ (scE_ne_zero e j), hA1', install_slot _ (rfE_injective e)]
    change RepairOrdinary.frame (RequestInputFields.word ws) = _
    rw [hws, RequestInputFields.word_values]
  · rw [h0, dockH_other _ _ _ _ (scE_ne_zero e j), hH1', dockH_slot _ (rfE_injective e)]
    rfl
  · rw [h1, install_slot _ (scE_injective e j)]
    have hc : (⟨1, by omega⟩ : Fin (2 + e + 1)) = Fin.castAdd 1 (⟨1, by omega⟩ : Fin (2 + e)) := rfl
    rw [hc, Fin.addCases_left, hv]
  · rw [h1, dockH_slot _ (scE_injective e j)]
    have hc : (⟨1, by omega⟩ : Fin (2 + e + 1)) = Fin.castAdd 1 (⟨1, by omega⟩ : Fin (2 + e)) := rfl
    rw [hc, Fin.addCases_left]
    rfl

/-! ## The count word -/

def countWordOf (a : DecompositionAlgorithm) (r : Request) : List Bool :=
  CloseoutRowsRawAtomMeaning.countWord a (RepairSource.CloseoutRowsUniversal.pool (live a r) (occ a r))

theorem natWord_split (n : ℕ) : ∃ l bits, bits.length = l ∧
    RepairRepresentation.natWord n = List.replicate l true ++ false :: bits := by
  refine ⟨_, _, ?_, rfl⟩
  exact List.length_ofFn

/-- Field 3 (`natListWord childCounts`) is the header `natWord |childCounts|` followed by the count word. -/
theorem count_eq (a : DecompositionAlgorithm) (r : Request) : ∃ l bits, bits.length = l ∧
    fields a r 3 = StripH.word l bits (countWordOf a r) := by
  obtain ⟨l, bits, hb, hw⟩ := natWord_split (childCounts a r).length
  refine ⟨l, bits, hb, ?_⟩
  have e : fields a r 3 = natListWord (childCounts a r) := rfl
  rw [e]
  unfold natListWord
  rw [hw]
  simp only [StripH.word, List.append_assoc, List.cons_append]
  rfl

theorem heads0_3 : (![0, 0, 0] : Fin 3 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

/-- **The count-word stage.** -/
def countStage (a : DecompositionAlgorithm) : WordStage a (countWordOf a) where
  extra := 13 + 1 + 1
  states := _
  machine := fieldMachineE StripH.machine 3
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (2 * (2 * (r.input a).length + 3) + 2)
  coefficient := 36
  degree := 1
  cost_le := by
    intro r
    have h := input_le_small a r
    rw [pow_one]
    omega
  run := by
    intro r
    obtain ⟨l, bits, hb, hf⟩ := count_eq a r
    obtain ⟨H, hs⟩ := StripH.run l bits (countWordOf a r) hb
    have hlen : 2 * (2 * l + 1 + (countWordOf a r).length) + 3 ≤ 2 * (r.input a).length + 3 := by
      have h1 := field_le_input a r 3
      rw [hf, frame_length, StripH.word_length l bits _ hb] at h1
      omega
    have hs' : Step StripH.machine (2 * (r.input a).length + 3) (fun _ => 0)
        (scanIn 1 (frame (fields a r 3))) H
        ![RepairOrdinary.frame (StripH.word l bits (countWordOf a r)), countWordOf a r, NatSum.sent l 0] := by
      have e : scanIn 1 (frame (fields a r 3)) =
          ![RepairOrdinary.frame (StripH.word l bits (countWordOf a r)), [], []] := by
        rw [hf]; funext i; fin_cases i <;> rfl
      rw [e, ← heads0_3]
      exact hs.enlarge hlen
    exact field_runW (e := 1) StripH.machine 3 a r (countWordOf a r) _ H _ hs' rfl

/-! ## Unary templates -/

def UnaryStage.tplP {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v) :
    WordStage a (fun r => UnaryTemplate.tape (v r)) :=
  s.thenWord tplMap (2 * (s.coefficient + 7) + 2) (s.degree + 1) (by
    intro r
    have hb := s.value_bound r
    have hs := one_le_small a r
    have p0 : 1 ≤ (r.smallSize a) ^ (s.degree + 1) := Nat.one_le_pow _ _ hs
    change 2 * v r + 8 ≤ _
    have e : (2 * (s.coefficient + 7) + 2) * (r.smallSize a) ^ (s.degree + 1) =
        2 * ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) + 2 * (r.smallSize a) ^ (s.degree + 1) := by
      ring
    rw [e]
    omega)

end
end NearCubicWires.PacketsGlue.RequestMeta

