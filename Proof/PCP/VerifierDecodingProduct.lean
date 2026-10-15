import Proof.PCP.VerifierDecodingProductKernel

/-! Complete ordinary capped multiplication, including every overflowing input.
The controller tests capacity before growth and runs in quadratic unary time. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.ProductMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejected (cap operand total pos value : ℕ) : Configuration 4 6 :=
  controlConfig addCode (TapeEmbedding.config (fun _ : Fin 1 => pos+2)
    (fun _ => CapMachine.counter cap total)
    (CapMachine.cfg 2 cap operand cap (cap-value)))

theorem rejected_cells (cap operand total pos value : ℕ)
    (ha : operand ≤ cap) (ht : total ≤ cap) :
    (rejected cap operand total pos value).tapeCells = 4*(cap+2) := by
  simp [rejected, controlConfig, TapeEmbedding.config, CapMachine.cfg,
    Configuration.tapeCells, Fin.sum_univ_succ, Fin.addCases,
    CapMachine.counter_length _ _ ha, CapMachine.counter_length _ _ ht,
    CapMachine.counter_length cap cap (Nat.le_refl _)]
  omega

theorem reject_iteration (cap operand total pos value : ℕ)
    (ha : operand ≤ cap) (ht : total ≤ cap) (hp : pos < total)
    (hv : value ≤ cap) (hover : cap < value+operand) :
    Prefix machine (4*(cap+2)) (cap-value+2)
      (boundary cap operand total pos value) (rejected cap operand total pos value) := by
  obtain ⟨r,hr,hf,hs,hpeak⟩ := CapMachine.capped_add_run cap value operand hv ha
  have hmin : min operand (cap-value) = cap-value := Nat.min_eq_right (by omega)
  simp only [hmin, if_neg (by omega : ¬value+operand ≤ cap), min_eq_left (by omega : cap ≤ value+operand)] at hr hf hs
  have hrun := TapeEmbedding.run_embed CapMachine.machine (fun _ : Fin 1 => pos+2)
    (fun _ => CapMachine.counter cap total) _ _ r hr
  have hbody := add_prefix (prefix_of_run _ _ _ _ hrun).1
  simp only [TapeEmbedding.receipt, TapeEmbedding.extraCells, Fin.sum_univ_one,
    CapMachine.counter_length _ _ ht, hs, hf] at hbody
  have hbody' := hbody.enlarge (large := 4*(cap+2)) (by omega)
  exact Prefix.step (by rw [boundary_cells _ _ _ _ _ ha ht hv]) (by rfl)
    (enter_step cap operand total pos value hp) hbody'

/-- The endpoint describes the complete remaining driver loop. On success it
restores the operand head and leaves the exact product at its unary end; on
failure the target is capped and the rejecting state is terminal. -/
def Result (cap operand total sum : ℕ) (receipt : ExecutionReceipt 4 6) : Prop :=
  if sum ≤ cap then
    receipt.final = { boundary cap operand total total sum with control := 4 }
  else receipt.final.control = 5 ∧ receipt.final.tapes 1 = CapMachine.counter cap cap

theorem driver_run (n cap operand total pos value : ℕ)
    (ha : operand ≤ cap) (ht : total ≤ cap) (hpos : pos+n=total) (hv : value ≤ cap) :
    ∃ receipt : ExecutionReceipt 4 6,
      runFrom machine (n*(2*operand+4)+1) (boundary cap operand total pos value) = some receipt ∧
      Result cap operand total (value+n*operand) receipt ∧
      receipt.steps ≤ n*(2*operand+4)+1 ∧ receipt.peakTapeCells ≤ 4*(cap+2) := by
  induction n generalizing pos value with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    have tail : Prefix machine (4*(cap+2)) 1 (boundary cap operand total total value)
        { boundary cap operand total total value with control := 4 } :=
      Prefix.step (by rw [boundary_cells _ _ _ _ _ ha ht hv]) (by rfl)
        (stop_step cap operand total value)
        (Prefix.refl _ (by simpa only [Configuration.tapeCells] using
          (boundary_cells cap operand total total value ha ht hv).le))
    obtain ⟨r,hr,hf,hs,hpeak⟩ := tail.run (by rfl)
      (by simpa only [Configuration.tapeCells] using
        (boundary_cells cap operand total total value ha ht hv).le)
    exact ⟨r, by simpa using hr, by simpa [Result, hv] using hf, by simpa using hs.le, hpeak⟩
  | succ n ih =>
    have hp : pos < total := by omega
    by_cases hfit : value+operand ≤ cap
    · obtain ⟨r,hr,hf,hs,hpeak⟩ := ih (pos+1) (value+operand) (by omega) hfit
      have pref := success_iteration cap operand total pos value ha ht hp hfit
      obtain ⟨joined,hj,hjf,hjs,hjp⟩ := pref.followedBy r hr
      have hclock : 2*operand+4+(n*(2*operand+4)+1) = (n+1)*(2*operand+4)+1 := by ring
      have hsum : value+operand+n*operand = value+(n+1)*operand := by ring
      refine ⟨joined, by rwa [hclock] at hj, ?_, ?_, ?_⟩
      · simpa only [Result, hjf, hsum] using hf
      · rw [hjs]
        nlinarith
      · exact hjp.trans (max_le (Nat.le_refl _) hpeak)
    · have pref := reject_iteration cap operand total pos value ha ht hp hv (by omega)
      obtain ⟨r,hr,hf,hs,hpeak⟩ := pref.run (by rfl)
        (by rw [rejected_cells _ _ _ _ _ ha ht])
      have hclock : cap-value+2 ≤ (n+1)*(2*operand+4)+1 := by
        have hn : 2*operand+4 ≤ (n+1)*(2*operand+4) := by nlinarith
        omega
      have hmore := runFrom_moreFuel machine (cap-value+2)
        ((n+1)*(2*operand+4)+1-(cap-value+2)) _ r hr
      have hover : ¬ value+(n+1)*operand ≤ cap := by nlinarith
      refine ⟨r, ?_, ?_, by omega, hpeak⟩
      · rw [Nat.add_sub_of_le hclock] at hmore
        exact hmore
      · simp only [Result, if_neg hover, hf]
        exact ⟨rfl,rfl⟩

/-- A real four-tape capped multiplication. The input marks are retained and
explicit; false backing may subsequently be removed by run_unpad. -/
theorem capped_product_run (cap a b : ℕ) (ha : a ≤ cap) (hb : b ≤ cap) :
    ∃ receipt : ExecutionReceipt 4 6,
      runFrom machine (b*(2*a+4)+1) (boundary cap a b 0 0) = some receipt ∧
      Result cap a b (a*b) receipt ∧
      receipt.steps ≤ b*(2*a+4)+1 ∧ receipt.peakTapeCells ≤ 4*(cap+2) := by
  simpa only [Nat.zero_add, Nat.mul_comm b a] using
    driver_run b cap a b 0 0 ha hb (by omega) (by omega)

end NearCubicWires.RepairSource.VerifierDecoding.ProductMachine
