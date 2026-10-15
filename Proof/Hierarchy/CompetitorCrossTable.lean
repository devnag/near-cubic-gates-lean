import Proof.Hierarchy.CompetitorCrossTablePrepare
import Proof.Hierarchy.CompetitorCrossStateMeaning

/-! Complete ordinary native cross-table evaluation from four raw dimension
fields and the literal signed packet stream. All capacities, counters, zero
banks and padding are generated before the accepted complete table loop. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossTableCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 35) : Fin 120 := i.castAdd 85
theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 120 => k.val) h)
noncomputable def table := RecoveryFocus.machine native CompetitorPlaneTableCold.machine
noncomputable def machine := Composition.machine CompetitorCrossTablePrepare.machine table
def budget (b w n p : ℕ) := CompetitorCrossTablePrepare.budget b w n p+1+CompetitorPlaneTableCold.budget w n p
def heads (pos : ℕ) (i : Fin 120) : ℕ := if i.val=32 then pos else 0

theorem cold_run {n : ℕ} (b p : ℕ) (planes : List (Plane n))
    (hlen : planes.length ≤ p) (hv : ∀ a∈planes,a.Valid b p) :
    ∃ r out,run machine (budget b (CompetitorPlaneWidth.width b p) n planes.length)
      (CompetitorCrossTablePrepare.input b (CompetitorPlaneWidth.width b p) n planes.length (stream b planes))=some r ∧
      r.steps ≤ budget b (CompetitorPlaneWidth.width b p) n planes.length ∧
      r.final.heads=heads (stream b planes).length ∧
      (∀ i : Fin 35,r.final.tapes (native i)=CompetitorPlaneTableEntry.tapes out planes.length i) ∧
      TableContext b (CompetitorPlaneWidth.width b p) (evaluate planes (zero n)) out ∧
      r.final.tapes 32=stream b planes ∧ r.final.tapes 35=List.replicate n true ∧
      r.final.tapes 36=List.replicate planes.length true ∧
      Bounded b p (2*planes.length) (evaluate planes (zero n)) := by
  let w := CompetitorPlaneWidth.width b p
  obtain ⟨prepared,⟨first,hfirst,ht,hh,hs⟩,hf,h35,h36⟩ :=
    CompetitorCrossTablePrepare.prepare_run b w n planes.length (stream b planes)
  obtain ⟨child,out,hchild,hcs,hch,hct,hcontext,hsource,hbound⟩ :=
    CompetitorPlaneTableCold.cold_table_run b p planes hlen hv
  obtain ⟨last,hl,_,hls,hlh,hlt,hother⟩ := RecoveryFocus.dock native native_injective
    CompetitorPlaneTableCold.machine _ first.final.heads first.final.tapes
    (initialConfiguration CompetitorPlaneTableCold.machine (CompetitorPlaneTableCold.input b w n planes.length (stream b planes)))
    (by intro i;exact hh _) (by intro i;rw [ht];exact hf i) child hchild
  change runFrom table (CompetitorPlaneTableCold.budget w n planes.length)
    (Composition.restart first.final table.start)=some last at hl
  have hwhole := Composition.run_join CompetitorCrossTablePrepare.machine table _ _ _ first last hfirst hl
  have local_tapes : ∀ i : Fin 35,last.final.tapes (native i)=CompetitorPlaneTableEntry.tapes out planes.length i := by
    intro i
    rw [hlt,hct]
  have avoided (i : Fin 120) (hi : 35 ≤ i.val) : ∀ j,native j≠i := by
    intro j hj
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  refine ⟨Composition.joinedReceipt first last,out,hwhole,?_,?_,local_tapes,hcontext,?_,?_,?_,hbound⟩
  · change first.steps+1+last.steps ≤ budget b w n planes.length
    rw [hls]
    change child.steps ≤ CompetitorPlaneTableCold.budget w n planes.length at hcs
    unfold budget
    omega
  · change last.final.heads=heads (stream b planes).length
    funext i
    refine Fin.addCases (m := 35) (n := 85) ?_ ?_ i
    · intro j
      change last.final.heads (native j)=_
      rw [hlh,hch]
      fin_cases j <;> rfl
    · intro j
      rw [(hother _ (avoided _ (by simp))).1,hh]
      change 0=(if 35+j.val=32 then (stream b planes).length else 0)
      rw [if_neg (by omega)]
  · exact (local_tapes 32).trans hsource
  · exact (hother 35 (avoided _ (by decide))).2.trans (by rw [ht];exact h35)
  · exact (hother 36 (avoided _ (by decide))).2.trans (by rw [ht];exact h36)

end NearCubicWires.RepairOrdinary.CompetitorCrossTableCold
