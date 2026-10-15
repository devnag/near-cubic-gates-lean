import Proof.Hierarchy.HierarchyBinaryBounds
import Proof.Amplification.RecoveryReadyCalls
import Proof.MachineModel.OrdinaryBoundaryAdvance

/-! Reusable binary add and streaming focus boundary for the hierarchy-bound
multiplier. Every focus call executes the imported ordinary machine, retaining
the factor cursor while its local arithmetic heads return to zero. -/
namespace NearCubicWires.RepairOrdinary.HierarchyBinary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem add_ready (w a b cap : ℕ) (backing : List Bool) (hfit : a+b<2^w)
    (hb : backing.length≤2*w+1) :
    ReadyRun BoundaryAdvance.machine (4*w+4)
      ![frame (binary w a),frame (binary w b),backing,List.replicate cap false]
      ![frame (binary w a),frame (binary w b),frame (binary w (a+b)),
        List.replicate (max cap (2*w+1)) false] := by
  obtain ⟨base,hr,h0,h1,h2,_,_,_,hs,_⟩ := Add.add_run w a b backing hfit hb
  have hin : Add.config (Add.scanState false) (frame (binary w a)) (frame (binary w b)) 0 0 [] backing=
      initialConfiguration Add.machine ![frame (binary w a),frame (binary w b),backing] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · simp [Add.config,initialConfiguration,StablePartition.Workspace.overlay]
  have hr' : run Add.machine (2*w+1) ![frame (binary w a),frame (binary w b),backing]=some base := by
    rw [run,← hin]
    exact hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace Add.machine _ _ base hr' cap
  have he : 2*base.steps+2=4*w+4 := by omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · exact (ht 0).trans h0
    · exact (ht 1).trans h1
    · exact (ht 2).trans h2
    · simpa [hs] using hc

theorem focused_run {t u s time : ℕ} (slot : Fin t → Fin u)
    (hi : Function.Injective slot) (p : Machine t s)
    (input output : Fin t → List Bool) (h : ReadyRun p time input output)
    (heads : Fin u → ℕ) (ambient : Fin u → List Bool)
    (hh : ∀ j,heads (slot j)=0) (ht : ∀ j,ambient (slot j)=input j) :
    ∃ r : ExecutionReceipt u s,
      runFrom (RecoveryFocus.machine slot p) time
        (RecoveryCalls.restarted (RecoveryFocus.machine slot p) heads ambient)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=install slot ambient output ∧ r.steps=time := by
  obtain ⟨base,hr,hout,hheads,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot hi p heads ambient time
    (initialConfiguration p input) base hr
  have hin : RecoveryFocus.config slot heads ambient (initialConfiguration p input)=
      RecoveryCalls.restarted (RecoveryFocus.machine slot p) heads ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp,RecoveryCalls.restarted]
      | some j =>
        have he := RecoveryFocus.slot_of_pick slot hp
        simp only [RecoveryFocus.config,hp,initialConfiguration,RecoveryCalls.restarted]
        exact (hh j).symm.trans (congrArg heads he)
    · exact install_existing slot ambient input ht
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simp only [RecoveryFocus.config,hp]
      exact (hheads j).trans ((hh j).symm.trans (congrArg heads he))
  · rw [hf]
    change install slot ambient base.final.tapes=install slot ambient output
    rw [hout]

end NearCubicWires.RepairOrdinary.HierarchyBinary
