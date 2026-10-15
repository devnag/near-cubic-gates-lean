import Proof.MachineModel.ClockInputLength

/-! Input-length counting starts with blank scratch and restores the complete
input cursor. The apparent initial counter delimiter is discharged by the
actual zero-unpadding simulation. -/
namespace NearCubicWires.RepairOrdinary.ClockLengthReady
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) : Fin 3 → List Bool := ![[],[],frame bits]
def pad : Fin 3 → ℕ := ![1,0,0]

theorem scan_run (bits : List Bool) (hn : 0<bits.length) :
    ∃ cap, cap≤2*PCPResourceLedger.ell bits.length+3 ∧
      ∃ r : ExecutionReceipt 3 12,
        run ClockInputLength.machine (ClockInputLength.cost bits.length bits) (input bits) = some r ∧
        r.final.tapes 0 = frame (ClockBinary.word bits.length) ∧
        r.final.tapes 1 = List.replicate cap false ∧
        r.final.tapes 2 = frame bits ∧
        r.final.heads = ![0,0,2*bits.length] ∧
        r.steps≤ClockInputLength.cost bits.length bits := by
  obtain ⟨cap,hcap,base,hb,hf,hs⟩ := ClockInputLength.loop_run bits.length 0 0 [] bits []
    (by simp) (by omega)
  let c := initialConfiguration ClockInputLength.machine (input bits)
  have hi : ZeroPadding.config pad c =
      ClockInputLength.config (RecordController.test 10) (ClockBinary.word 0) 0 (frame bits) 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,pad,c,input,initialConfiguration,
        ClockInputLength.config,ClockBinary.word,ZeroPadding.pad,frame]
  have hb' : runFrom ClockInputLength.machine (ClockInputLength.cost bits.length bits)
      (ZeroPadding.config pad c) = some base := by
    rw [hi]
    simpa using hb
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad ClockInputLength.machine pad _ c base hb'
  have hfinal : ZeroPadding.config pad r.final =
      ClockInputLength.config (RecordController.stop 10) (ClockBinary.word bits.length) cap
        (frame bits) (2*bits.length) := by simpa [hf] using hrf
  have ht0 := congrArg (fun c : Configuration 3 12 => c.tapes 0) hfinal
  have ht1 := congrArg (fun c : Configuration 3 12 => c.tapes 1) hfinal
  have ht2 := congrArg (fun c : Configuration 3 12 => c.tapes 2) hfinal
  have hh := congrArg Configuration.heads hfinal
  change ZeroPadding.pad 1 (r.final.tapes 0) = frame (ClockBinary.word bits.length) at ht0
  have hword : ClockBinary.word bits.length ≠ [] := by
    intro he
    have hv := ClockBinary.word_value bits.length
    rw [he] at hv
    simp [RadixSemantics.value] at hv
    omega
  have htape : r.final.tapes 0 ≠ [] := by
    intro he
    rw [he] at ht0
    have hl := congrArg List.length ht0
    simp only [ZeroPadding.pad,List.length_append,List.length_nil,List.length_replicate,
      Nat.sub_zero,frame_length] at hl
    have hnil : ClockBinary.word bits.length = [] := List.length_eq_zero_iff.mp (by omega)
    exact hword hnil
  have hlen : 1≤(r.final.tapes 0).length := by
    cases he : r.final.tapes 0 <;> simp_all
  have hp : ZeroPadding.pad 1 (r.final.tapes 0) = r.final.tapes 0 := by
    simp [ZeroPadding.pad,Nat.sub_eq_zero_of_le hlen]
  rw [hp] at ht0
  simp [ZeroPadding.config,pad,ClockInputLength.config] at ht1 ht2
  exact ⟨cap,hcap,r,hr,ht0,ht1,ht2,hh,hrs.le.trans hs⟩

def machine : Machine 4 14 := Rewind.machine ClockInputLength.machine

def source (bits : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input bits) (fun _ : Fin 1 => [])

def budget (bits : List Bool) : ℕ := 2*ClockInputLength.cost bits.length bits+2

theorem count_run (bits : List Bool) (hn : 0<bits.length) :
    ∃ cap scratch, cap≤2*PCPResourceLedger.ell bits.length+3 ∧
      scratch≤ClockInputLength.cost bits.length bits ∧
      ∃ r : ExecutionReceipt 4 14,
        run machine (budget bits) (source bits) = some r ∧
        r.final.tapes 0 = frame (ClockBinary.word bits.length) ∧
        r.final.tapes 1 = List.replicate cap false ∧
        r.final.tapes 2 = frame bits ∧
        r.final.tapes 3 = List.replicate scratch false ∧
        (∀ i, r.final.heads i=0) ∧ r.steps≤budget bits := by
  obtain ⟨cap,hcap,base,hb,hbits,hcapbits,hinput,_,hs⟩ := scan_run bits hn
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace
    ClockInputLength.machine _ (input bits) base hb 0
  have hbound : 2*base.steps+2≤budget bits := by dsimp [budget]; omega
  have hmore := run_moreFuel machine (2*base.steps+2) (budget bits-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨cap,base.steps,hcap,hs,r,hmore,?_,?_,?_,?_,hh,by omega⟩
  · exact (ht 0).trans hbits
  · exact (ht 1).trans hcapbits
  · exact (ht 2).trans hinput
  · simpa using hcounter

end NearCubicWires.RepairOrdinary.ClockLengthReady
