import Proof.PCP.VerifierDecodingPowerStep

/-! The complete capped 2^t loop used before transition-table expansion. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.PowerMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejected (cap total pos value : ℕ) : Configuration 4 11 :=
  controlConfig addCode (TapeEmbedding.config (fun _ : Fin 1 => pos+2)
    (fun _ => CapMachine.counter cap total)
    (CapMachine.cfg 2 cap value cap (cap-value)))

theorem rejected_cells (cap total pos value : ℕ) (ht : total ≤ cap) (hv : value ≤ cap) :
    (rejected cap total pos value).tapeCells = 4*(cap+2) := by
  simp [rejected, controlConfig, TapeEmbedding.config, CapMachine.cfg,
    Configuration.tapeCells, Fin.sum_univ_succ, Fin.addCases,
    CapMachine.counter_length _ _ ht, CapMachine.counter_length _ _ hv,
    CapMachine.counter_length cap cap (Nat.le_refl _)]
  omega

theorem reject_iteration (cap total pos value : ℕ)
    (ht : total ≤ cap) (hp : pos < total) (hv : value ≤ cap) (hover : cap < value+value) :
    Prefix machine (4*(cap+2)) (cap-value+2)
      (boundary cap total pos value) (rejected cap total pos value) := by
  obtain ⟨r,hr,hf,hs,hpeak⟩ := CapMachine.capped_add_run cap value value hv hv
  have hmin : min value (cap-value) = cap-value := Nat.min_eq_right (by omega)
  simp only [hmin, if_neg (by omega : ¬value+value ≤ cap), min_eq_left (by omega : cap ≤ value+value)] at hr hf hs
  have hbody := add_prefix (prefix_of_run _ _ _ _
    (TapeEmbedding.run_embed CapMachine.machine (fun _ : Fin 1 => pos+2)
      (fun _ => CapMachine.counter cap total) _ _ r hr)).1
  simp only [TapeEmbedding.receipt, TapeEmbedding.extraCells, Fin.sum_univ_one,
    CapMachine.counter_length _ _ ht, hs, hf] at hbody
  have hbody' := hbody.enlarge (large := 4*(cap+2)) (by omega)
  exact Prefix.step (by rw [boundary_cells _ _ _ _ ht hv]) (by rfl)
    (enter_step cap total pos value hp) hbody'

def Result (cap total value : ℕ) (receipt : ExecutionReceipt 4 11) : Prop :=
  if value ≤ cap then
    receipt.final = { boundary cap total total value with control := 9 }
  else receipt.final.control = 10 ∧ receipt.final.tapes 1 = CapMachine.counter cap cap

theorem driver_run (n cap total pos value : ℕ)
    (ht : total ≤ cap) (hpos : pos+n=total) (hv : value ≤ cap) :
    ∃ receipt : ExecutionReceipt 4 11,
      runFrom machine (n*(8*cap+9)+1) (boundary cap total pos value) = some receipt ∧
      Result cap total (value*2^n) receipt ∧
      receipt.steps ≤ n*(8*cap+9)+1 ∧ receipt.peakTapeCells ≤ 4*(cap+2) := by
  induction n generalizing pos value with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    have tail : Prefix machine (4*(cap+2)) 1 (boundary cap total total value)
        { boundary cap total total value with control := 9 } :=
      Prefix.step (by rw [boundary_cells _ _ _ _ ht hv]) (by rfl)
        (stop_step cap total value)
        (Prefix.refl _ (by simpa only [Configuration.tapeCells] using
          (boundary_cells cap total total value ht hv).le))
    obtain ⟨r,hr,hf,hs,hpeak⟩ := tail.run (by rfl)
      (by simpa only [Configuration.tapeCells] using
        (boundary_cells cap total total value ht hv).le)
    exact ⟨r, by simpa using hr, by simpa [Result, hv] using hf, by simpa using hs.le, hpeak⟩
  | succ n ih =>
    have hp : pos < total := by omega
    by_cases hfit : value+value ≤ cap
    · obtain ⟨r,hr,hf,hs,hpeak⟩ := ih (pos+1) (value+value) (by omega) hfit
      have pref := success_iteration cap total pos value ht hp hfit
      obtain ⟨joined,hj,hjf,hjs,hjp⟩ := pref.followedBy r hr
      have hclock : 8*value+9+(n*(8*cap+9)+1) ≤ (n+1)*(8*cap+9)+1 := by nlinarith
      have hsum : (value+value)*2^n = value*2^(n+1) := by rw [pow_succ]; ring
      have hmore := runFrom_moreFuel machine (8*value+9+(n*(8*cap+9)+1))
        ((n+1)*(8*cap+9)+1-(8*value+9+(n*(8*cap+9)+1))) _ joined hj
      rw [Nat.add_sub_of_le hclock] at hmore
      refine ⟨joined, hmore, ?_, ?_, ?_⟩
      · simpa only [Result, hjf, hsum] using hf
      · rw [hjs]
        nlinarith
      · exact hjp.trans (max_le (Nat.le_refl _) hpeak)
    · have pref := reject_iteration cap total pos value ht hp hv (by omega)
      obtain ⟨r,hr,hf,hs,hpeak⟩ := pref.run (by rfl)
        (by rw [rejected_cells _ _ _ _ ht hv])
      have hclock : cap-value+2 ≤ (n+1)*(8*cap+9)+1 := by
        have hn : 8*cap+9 ≤ (n+1)*(8*cap+9) := by nlinarith
        omega
      have hmore := runFrom_moreFuel machine (cap-value+2)
        ((n+1)*(8*cap+9)+1-(cap-value+2)) _ r hr
      rw [Nat.add_sub_of_le hclock] at hmore
      have hover : ¬ value*2^(n+1) ≤ cap := by
        have hpow : 0 < (2:ℕ)^n := pow_pos (by omega) _
        rw [pow_succ]
        nlinarith
      refine ⟨r, hmore, ?_, by omega, hpeak⟩
      simp only [Result, if_neg hover, hf]
      exact ⟨rfl,rfl⟩

/-- The power is materialized only when it fits in the literal input cap.
Overflow halts with a rejecting control and never writes beyond that cap. -/
theorem capped_power_run (cap exponent : ℕ) (hc : 1 ≤ cap) (ht : exponent ≤ cap) :
    ∃ receipt : ExecutionReceipt 4 11,
      runFrom machine (exponent*(8*cap+9)+1) (boundary cap exponent 0 1) = some receipt ∧
      Result cap exponent (2^exponent) receipt ∧
      receipt.steps ≤ exponent*(8*cap+9)+1 ∧ receipt.peakTapeCells ≤ 4*(cap+2) := by
  simpa only [Nat.one_mul] using driver_run exponent cap exponent 0 1 ht (by omega) hc

end NearCubicWires.RepairSource.VerifierDecoding.PowerMachine
