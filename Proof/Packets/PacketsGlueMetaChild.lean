import Proof.Packets.PacketsMetaField
import Proof.Packets.PacketsNatSum

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## The general field-scan stage -/

/-- The splitter inside a stage with `e` further private scanner tapes. -/
def rfE (e : ℕ) : Fin 13 → Fin (2 + (13 + e + 1)) :=
  fun i => if i.val = 0 then ⟨0, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- The masked scanner: tape 0 on field `j`, tape 1 on the output, the rest past the splitter. -/
def scE (e : ℕ) (j : Fin 5) : Fin (2 + e + 1) → Fin (2 + (13 + e + 1)) :=
  fun k => if k.val = 0 then ⟨j.val + 4, by omega⟩ else if k.val = 1 then ⟨1, by omega⟩
    else ⟨k.val + 13, by omega⟩

theorem rfE_injective (e : ℕ) : Function.Injective (rfE e) := by
  intro a b h
  have hv := congrArg Fin.val h
  unfold rfE at hv
  apply Fin.ext
  split_ifs at hv <;> simp at hv <;> omega

theorem scE_injective (e : ℕ) (j : Fin 5) : Function.Injective (scE e j) := by
  intro a b h
  have hv := congrArg Fin.val h
  unfold scE at hv
  apply Fin.ext
  have := j.isLt
  split_ifs at hv <;> simp at hv <;> omega

theorem scE_zero (e : ℕ) (j : Fin 5) (h : 0 < 2 + e + 1) :
    scE e j ⟨0, h⟩ = rfE e ⟨j.val + 3, by omega⟩ := by
  apply Fin.ext
  simp [scE, rfE]

theorem scE_one (e : ℕ) (j : Fin 5) (h : 1 < 2 + e + 1) : scE e j ⟨1, h⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  simp [scE]

theorem rfE_ne_one (e : ℕ) (i : Fin 13) : rfE e i ≠ ⟨1, by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  unfold rfE at hv
  split_ifs at hv <;> simp at hv <;> omega

theorem rfE_ne_big (e : ℕ) (j : Fin 5) (k : Fin (2 + e + 1)) (hk : 2 ≤ k.val) (i : Fin 13) :
    rfE e i ≠ scE e j k := by
  intro h
  have hv := congrArg Fin.val h
  unfold rfE scE at hv
  have := i.isLt
  split_ifs at hv <;> simp at hv <;> omega

theorem scE_val_ne_zero (e : ℕ) (j : Fin 5) (k : Fin (2 + e + 1)) : (scE e j k).val ≠ 0 := by
  unfold scE
  split_ifs <;> simp

theorem scE_ne_zero (e : ℕ) (j : Fin 5) (k : Fin (2 + e + 1)) : scE e j k ≠ rfE e 0 := by
  intro h
  have hv := congrArg Fin.val h
  unfold rfE scE at hv
  split_ifs at hv <;> simp at hv <;> omega

/-- One fixed machine per `(scanner, field)`. -/
def fieldMachineE {e s : ℕ} (M : Machine (2 + e) s) (j : Fin 5) :=
  Composition.machine (RecoveryFocus.machine (rfE e) RequestInputFields.machine)
    (RecoveryFocus.machine (scE e j) (MaskedReset.machine M (fun _ => true)))

/-- The field-scan entry of a `2+e`-tape scanner. -/
def scanIn (e : ℕ) (f : List Bool) : Fin (2 + e) → List Bool := fun k => if k.val = 0 then f else []

/-- **The general field-scan run.** -/
theorem field_runE {e s : ℕ} (M : Machine (2 + e) s) (j : Fin 5) (a : DecompositionAlgorithm) (r : Request)
    (v n : ℕ) (H1 : Fin (2 + e) → ℕ) (A1 : Fin (2 + e) → List Bool)
    (hM : Step M n (fun _ => 0) (scanIn e (frame (fields a r j))) H1 A1)
    (hv : A1 ⟨1, by omega⟩ = List.replicate v true) :
    ∃ (H' : Fin (2 + (13 + e + 1)) → ℕ) (A' : Fin (2 + (13 + e + 1)) → List Bool),
      Step (fieldMachineE M j) (6*(r.input a).length+17 + 1 + (2*n+2)) (fun _ => 0)
        (inBank (2 + (13 + e + 1)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate v true ∧ H' ⟨1, by omega⟩ = 0 := by
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

/-! ## `N` and `alphabet` -/

theorem alphabet_eq (a : DecompositionAlgorithm) (r : Request) : alphabet a r = childTotal a r + 2 := by
  unfold alphabet childTotal childCounts Packets.alphabet
  rw [← ExtDecompositionBatch.B_eq_sum]
  rfl

theorem alphabet_le_small (a : DecompositionAlgorithm) (r : Request) : alphabet a r ≤ r.smallSize a := by
  have hpos : 1 ≤ alphabet a r := by rw [alphabet_eq]; omega
  have h1 : alphabet a r ≤ (alphabet a r) ^ (Request.degree a r + 1) :=
    Nat.le_self_pow (by omega) _
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x3 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  have h2 : (alphabet a r) ^ (Request.degree a r + 1) ≤ r.smallSize a := by
    unfold Request.smallSize
    exact key _ _ _ _ _ _ _ _
  exact h1.trans h2

theorem child_le_small (a : DecompositionAlgorithm) (r : Request) : childTotal a r + 2 ≤ r.smallSize a := by
  rw [← alphabet_eq]
  exact alphabet_le_small a r

theorem index_le_input (a : DecompositionAlgorithm) (r : Request) :
    (natListWord (childCounts a r)).length ≤ (r.input a).length := by
  have h := field_le_input a r 3
  have h2 : fields a r 3 = natListWord (childCounts a r) := rfl
  rw [h2, frame_length] at h
  omega

/-- **`childTotal` (N) stage.** -/
def childStage (a : DecompositionAlgorithm) : UnaryStage a (childTotal a) where
  extra := 13 + 3 + 1
  states := _
  machine := fieldMachineE PacketsGlue.NatSum.machine 3
  cost := fun r => 6*(r.input a).length+17 + 1 +
    (2*(16 * childTotal a r + 40 * (natListWord (childCounts a r)).length + 12) + 2)
  coefficient := 200
  degree := 1
  cost_le := by
    intro r
    have h1 := index_le_input a r
    have h2 := input_le_small a r
    have h3 := child_le_small a r
    rw [pow_one]
    omega
  run := by
    intro r
    obtain ⟨n, H1, A1, hs, hv, hn⟩ := PacketsGlue.NatSum.run (childCounts a r)
    have hs' : Step PacketsGlue.NatSum.machine n (fun _ => 0) (scanIn 3 (frame (fields a r 3))) H1 A1 := by
      have e : scanIn 3 (frame (fields a r 3)) =
          (fun k : Fin 5 => if k.val = 0 then frame (natListWord (childCounts a r)) else []) := rfl
      rw [e]
      exact hs
    obtain ⟨H', A', hrun, h0, hh0, h1, hh1⟩ := field_runE (e := 3) PacketsGlue.NatSum.machine 3 a r
      (childCounts a r).sum n H1 A1 hs' (by exact hv)
    have hN : childTotal a r = (childCounts a r).sum := rfl
    refine ⟨H', A', hrun.enlarge (by omega), h0, hh0, h1, hh1⟩

end
end NearCubicWires.PacketsGlue.RequestMeta

