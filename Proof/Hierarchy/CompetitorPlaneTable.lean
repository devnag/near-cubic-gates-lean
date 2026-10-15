import Proof.Hierarchy.CompetitorPlaneTableInitialize

/-! One ordinary table program begins with blank accumulator/reset tapes,
physically initializes them and executes the complete packet stream. Width,
capacity and count words remain named input fields pending their producer. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTableCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneTable CompetitorPlaneTableInitialize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 34) : Fin 35 := i.castAdd 1
def input (b w n count : ℕ) (source : List Bool) :=
  CompetitorPlaneTableEntry.tapes (CompetitorPlaneTableInitialize.input b w n source) count
noncomputable def clear := RecoveryFocus.machine native CompetitorPlaneTableInitialize.clear
noncomputable def machine := Composition.machine clear CompetitorPlaneTableEntry.machine
def budget (w n count : ℕ) := 2*capacity w n+5+CompetitorPlaneTableEntry.budget w n count

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 35 => x.val) h)

theorem cold_clear (b w n count : ℕ) (source : List Bool) :
    ClockJoin.ReadyRun clear (2*capacity w n+4) (input b w n count source)
      (CompetitorPlaneTableEntry.tapes (cleared b w n source) count) := by
  have hi : ∀ i,input b w n count source (native i)=CompetitorPlaneTableInitialize.input b w n source i := by
    intro i
    simp [input,CompetitorPlaneTableEntry.tapes,native]
  have ready := CompetitorRationalProducts.bounded_focus native native_injective _ _ _
    (clear_ready b w n source) (input b w n count source) hi
  have he : install native (input b w n count source) (cleared b w n source)=
      CompetitorPlaneTableEntry.tapes (cleared b w n source) count := by
    funext i
    refine Fin.addCases (m := 34) (n := 1) ?_ ?_ i
    · intro j
      simp only [CompetitorPlaneTableEntry.tapes,Fin.addCases_left]
      exact install_slot native native_injective (input b w n count source) (cleared b w n source) j
    · intro j
      fin_cases j
      apply install_other
      intro a ha
      have hv:=congrArg (fun x : Fin 35 => x.val) ha
      change a.val=34 at hv
      omega
  rw [he] at ready
  exact ready

theorem cold_table_run {n : ℕ} (b p : ℕ) (planes : List (Plane n))
    (hlength : planes.length≤p) (hvalid : ∀ a∈planes,a.Valid b p) :
    ∃ r out,run machine (budget (CompetitorPlaneWidth.width b p) n planes.length)
      (input b (CompetitorPlaneWidth.width b p) n planes.length (stream b planes))=some r ∧
      r.steps≤budget (CompetitorPlaneWidth.width b p) n planes.length ∧
      r.final.heads=CompetitorPlaneTableEntry.heads (stream b planes).length 0 ∧
      r.final.tapes=CompetitorPlaneTableEntry.tapes out planes.length ∧
      TableContext b (CompetitorPlaneWidth.width b p) (evaluate planes (zero n)) out ∧
      out 32=stream b planes ∧ Bounded b p (2*planes.length) (evaluate planes (zero n)) := by
  let w := CompetitorPlaneWidth.width b p
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := cold_clear b w n planes.length (stream b planes)
  have hsource : cleared b w n (stream b planes) 32=[]++stream b planes++[] := by
    have he := install_other slots (CompetitorPlaneTableInitialize.input b w n (stream b planes))
      (eraseOutput (capacity w n)) 32 (by intro i; fin_cases i <;> decide)
    simpa [cleared,CompetitorPlaneTableInitialize.input] using he
  obtain ⟨last,out,hl,hls,hlh,hlt,hcontext,hsrc,hbound⟩ := CompetitorPlaneTableEntry.table_run
    b p planes (zero n) [] [] (cleared b w n (stream b planes)) hlength hvalid
    (by intro i; simp [zero]) (cleared_context b w n (stream b planes) (by dsimp [w,CompetitorPlaneWidth.width]; omega)) hsource
  have he : Composition.restart first.final CompetitorPlaneTableEntry.machine.start=
      CompetitorPlaneTableEntry.cfg CompetitorPlaneTableEntry.machine.start 0 0
        (cleared b w n (stream b planes)) planes.length := by
    apply configuration_ext
    · rfl
    · funext i
      change first.final.heads i=CompetitorPlaneTableEntry.heads 0 0 i
      rw [hfh i]
      refine Fin.addCases (m := 34) (n := 1) ?_ ?_ i
      · intro j
        simp [CompetitorPlaneTableEntry.heads,CompetitorPlanePacketDock.heads]
      · intro j
        simp [CompetitorPlaneTableEntry.heads]
    · exact hft
  have hl' : runFrom CompetitorPlaneTableEntry.machine (CompetitorPlaneTableEntry.budget w n planes.length)
      (Composition.restart first.final CompetitorPlaneTableEntry.machine.start)=some last := by
    rw [he]
    exact hl
  have hall := Composition.run_join clear CompetitorPlaneTableEntry.machine _ _ _ first last hfirst hl'
  have hc : (2*capacity w n+4)+1+CompetitorPlaneTableEntry.budget w n planes.length=budget w n planes.length := by
    unfold budget
    omega
  rw [hc] at hall
  refine ⟨Composition.joinedReceipt first last,out,hall,?_,?_,hlt,hcontext,?_,hbound⟩
  · change first.steps+1+last.steps≤budget w n planes.length
    unfold budget
    change last.steps≤CompetitorPlaneTableEntry.budget w n planes.length at hls
    omega
  · change last.final.heads=_
    simpa using hlh
  · simpa using hsrc

end NearCubicWires.RepairOrdinary.CompetitorPlaneTableCold
