import Proof.PCP.VerifierDecodingStartFlags

/-! Whole start-field and state-flag scan, including both early rejection
paths, all return steps, and the physical result. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.StartFlags
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def afterStart (pre bits bound : List Bool) := pre++Streaming.marks (bits.take bound.length)
def valid (bits bound : List Bool) (s : ℕ) : Bool :=
  decide (RecordMachine.rangeValid bits bound) && decide (2*s≤(bits.drop bound.length).length)
noncomputable def initial {a : ℕ} (base : Configuration 11 a) :=
  controlConfig (RecoveryCalls.code sizes 0) (StartLayout.input base)
noncomputable def endpoint {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool) (s : ℕ) :=
  let out := FlagsLayout.output (StartLayout.output base pre bits bound) (afterStart pre bits bound) s
  RecoveryCalls.stopped sizes out.heads out.tapes

theorem flags_entry {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool) (c s : ℕ)
    (h : StartLayout.Entry base pre bits bound)
    (hcountHead : base.heads 2=1) (hcountTape : base.tapes 2=CapMachine.counter c s)
    (hgood : RecordMachine.rangeValid bits bound) :
    FlagsLayout.Entry (StartLayout.output base pre bits bound) (afterStart pre bits bound)
      (bits.drop bound.length) c s := by
  have hlen : (bits.take bound.length).length=bound.length := by simp [Nat.min_eq_left hgood.1]
  constructor
  · simp [StartLayout.output,afterStart,Streaming.marks_length,hlen]
  · have he : pre++Streaming.marks (bits.take bound.length)++frame (bits.drop bound.length)=pre++frame bits := by
      rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    simpa [StartLayout.output,StartLayout.input,Fin.addCases,afterStart,h.codeTape] using he.symm
  · simpa [StartLayout.output,StartLayout.input,Fin.addCases] using hcountHead
  · simpa [StartLayout.output,StartLayout.input,Fin.addCases] using hcountTape

theorem start_flags_run {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool) (c s : ℕ)
    (h : StartLayout.Entry base pre bits bound)
    (hcountHead : base.heads 2=1) (hcountTape : base.tapes 2=CapMachine.counter c s) :
    ∃ r, runFrom machine (8*bound.length+8*s+20) (initial base)=some r ∧
      r.steps≤8*bound.length+8*s+20 ∧ r.final.scanned 12=valid bits bound s ∧
      (valid bits bound s=true → r.final=endpoint base pre bits bound s) := by
  obtain ⟨r,hr,hs,hbit,hresult⟩ := StartLayout.start_layout base pre bits bound h
  by_cases hgood : RecordMachine.rangeValid bits bound
  · have hp := call_prefix 0 1 (8*bound.length+10) _ r hr (by
      simp [next]
      exact hbit.trans (by simp [hgood]))
    have hfinal := hresult hgood
    rw [hfinal] at hp
    obtain ⟨n,final,hn,hflags,hh,hflagbit,hendpoint⟩ := flags_tail
      (StartLayout.output base pre bits bound) (afterStart pre bits bound)
      (bits.drop bound.length) c s (flags_entry base pre bits bound c s h hcountHead hcountTape hgood) (by rfl)
    have hall := hp.trans hflags
    obtain ⟨result,hrun,hf,hsteps⟩ := hall.run hh
    have htime : r.steps+1+n≤8*bound.length+8*s+20 := by omega
    have hm := runFrom_moreFuel machine (r.steps+1+n)
      (8*bound.length+8*s+20-(r.steps+1+n)) _ result hrun
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,hm,by omega,?_,?_⟩
    · rw [hf]
      simpa [valid,hgood] using hflagbit
    · intro hv
      have hlen : 2*s≤(bits.drop bound.length).length := by simpa [valid,hgood] using hv
      exact hf.trans (hendpoint hlen)
  · have hp := stop_prefix 0 (8*bound.length+10) _ r hr (by
      simp [next]
      exact hbit.trans (by simp [hgood]))
    obtain ⟨result,hrun,hf,hsteps⟩ := hp.run (by
      simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    have htime : r.steps+1≤8*bound.length+8*s+20 := by omega
    have hm := runFrom_moreFuel machine (r.steps+1)
      (8*bound.length+8*s+20-(r.steps+1)) _ result hrun
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,hm,by omega,?_,by simp [valid,hgood]⟩
    rw [hf]
    simpa [valid,hgood,RecoveryCalls.stopped,Configuration.scanned] using hbit

end NearCubicWires.RepairSource.VerifierDecoding.StartFlags
