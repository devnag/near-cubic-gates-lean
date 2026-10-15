import Proof.PCP.PCPTraversalDescend

/-! The return node reads and changes its physical continuation stack. The
actual halted controls select the fixed left/right/empty successor paths. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem continuation_timed_path (q : Fin 8) (target : Fin 39) (fuel beforePos afterPos : ℕ)
    (before after : List Bool) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hr : Timed PCPContinuation.machine fuel (PCPContinuation.cfg 0 before beforePos)
      (PCPContinuation.cfg q after afterPos))
    (hq : PCPContinuation.machine.halted q=true)
    (hn : ∀ scanned,next 9 q scanned=some target)
    (ht : ambient 81=before) (hh : heads 81=beforePos) :
    Path 9 target (fuel+1) heads ambient
      (installedHeads ![81] heads (fun _ => afterPos)) (install ![81] ambient (fun _ => after)) := by
  obtain ⟨base,hbase,hfinal,_⟩ := hr.run hq
  obtain ⟨r,hrun,hrq,hrh,hrt,_⟩ := focused_run_at PCPContinuation.machine ![81] (by decide)
    heads ambient _ base hbase rfl (by intro i; fin_cases i; exact hh)
    (by intro i; fin_cases i; exact ht)
  rw [hfinal] at hrq hrh hrt
  change r.final.control=q at hrq
  obtain ⟨steps,hsteps,hpath⟩ := call_receipt sizes programs 37 next 9 target fuel
    (RecoveryCalls.restarted (programs 9) heads ambient) r hrun (by rw [hrq]; exact hn _)
  rw [hrh,hrt] at hpath
  exact ⟨steps,hsteps,hpath⟩

theorem return_left_path (pre : List Bool) (z : ℕ) (heads : Fin 128 → ℕ)
    (ambient : Fin 128 → List Bool)
    (ht : ambient 81=pre++false::true::List.replicate z false)
    (hh : heads 81=pre.length+2) :
    Path 9 10 5 heads ambient heads
      (install ![81] ambient (fun _ => pre++true::true::List.replicate z false)) := by
  have h := continuation_timed_path 5 10 4 (pre.length+2) (pre.length+2) _ _ heads ambient
    (PCPContinuation.left_return pre z) (by rfl) (by intro scanned; simp [next]) ht hh
  have he := installedHeads_existing ![81] heads (fun _ => pre.length+2)
    (by intro i; fin_cases i; exact hh)
  rw [he] at h
  exact h

theorem return_right_path (pre : List Bool) (z : ℕ) (heads : Fin 128 → ℕ)
    (ambient : Fin 128 → List Bool)
    (ht : ambient 81=pre++true::true::List.replicate z false)
    (hh : heads 81=pre.length+2) :
    Path 9 21 5 heads ambient (installedHeads ![81] heads (fun _ => pre.length))
      (install ![81] ambient (fun _ => pre++List.replicate (z+2) false)) :=
  continuation_timed_path 7 21 4 (pre.length+2) pre.length _ _ heads ambient
    (PCPContinuation.right_return pre z) (by rfl) (by intro scanned; simp [next]) ht hh

theorem return_empty_path (z : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (ht : ambient 81=List.replicate (z+1) false) (hh : heads 81=1) :
    Path 9 35 3 heads ambient heads ambient := by
  have h := continuation_timed_path 6 35 2 1 1 _ _ heads ambient
    (PCPContinuation.empty_return z) (by rfl) (by intro scanned; simp [next]) ht hh
  have he := installedHeads_existing ![81] heads (fun _ => 1) (by intro i; fin_cases i; exact hh)
  have htapes := install_existing ![81] ambient (fun _ => List.replicate (z+1) false)
    (by intro i; fin_cases i; exact ht)
  rw [he,htapes] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPTraversal
