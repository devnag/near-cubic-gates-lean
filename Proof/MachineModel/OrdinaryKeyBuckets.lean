import Proof.MachineModel.OrdinaryKeyBucketLoop

/-! Complete interpreter receipt for the actual per-gate bucket traversal. -/
namespace NearCubicWires.RepairOrdinary.KeyBucketLoop
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem buckets_run (S K I keyCap resetCap b : ℕ) (records : List KeyLoop.Record) (mask : Bool)
    (hrecords : ∀ r ∈ records, r.2.2 < 2 ^ (K+S+1)) (hci : 2*I ≤ keyCap) (hck : 2*K ≤ keyCap)
    (hreset : records.length * (68*(K+S+1)+4*(I+K)+63)+1 ≤ resetCap)
    (count inner a initialRank : ℕ) (upper recordBack cloneBack out : List Bool)
    (hinner : inner+count < 2^I) (hfit : a+count*b < 2^(K+S+1))
    (hu : upper.length ≤ 2*(K+S+1)+1) (hr : recordBack.length ≤ 4*(K+S+1)+1) (hc : cloneBack.length ≤ 4*(K+S+1)+1) :
    let W := K+S+1
    let F := records.length * (68*W+4*(I+K)+63)+1
    let budget := count*(2*F+12*W+4*I+21)+1
    ∃ finalPhase finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2*W+1 ∧ finalRecord.length ≤ 4*W+1 ∧ finalClone.length ≤ 4*W+1 ∧
      ∃ r : ExecutionReceipt 23 154,
        runFrom machine budget
          (config machine.start W a b initialRank upper recordBack cloneBack mask (KeyLoop.stream S K records) out
            K I inner keyCap resetCap 1 count) = some r ∧
        r.final = config (UnaryController.stop (s := 75) finalPhase) W (a+count*b) b finalRank finalUpper finalRecord finalClone mask
          (KeyLoop.stream S K records) (out ++ output K I inner a b mask records count) K I (inner+count) keyCap resetCap (count+1) count ∧
        r.steps ≤ budget ∧
        r.peakTapeCells ≤ (KeyLoop.stream S K records).length + out.length + count*(records.length*(2*(I+K)+3)) +
          108*W+8*I+6*K+keyCap+resetCap+F+count+69 := by
  dsimp only
  obtain ⟨phase, rank, upper', record', clone', hu', hr', hc', steps, hsteps, hp⟩ :=
    loop_prefix S K I keyCap resetCap b records mask hrecords hci hck hreset count count 0 inner a initialRank false
      upper recordBack cloneBack out (by omega) hinner hfit hu hr hc
  obtain ⟨r, hrun, hf, hs, hb⟩ := hp.run (UnaryController.stop_halted family phase) (SortMatrix.final_cells hp)
  let budget := count*(2*(records.length*(68*(K+S+1)+4*(I+K)+63)+1)+12*(K+S+1)+4*I+21)+1
  have hmore := runFrom_moreFuel machine steps (budget-steps) _ r hrun
  rw [Nat.add_sub_of_le hsteps] at hmore
  exact ⟨phase, rank, upper', record', clone', hu', hr', hc', r, hmore, hf, hs.le.trans hsteps, hb⟩

end NearCubicWires.RepairOrdinary.KeyBucketLoop
