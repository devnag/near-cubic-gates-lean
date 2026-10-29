import SourceAdapters.Machine.CappedLayoutSlots

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: actual capped execution followed by exact result serialization. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

theorem core_run (p : Program) (cap : ℕ) (word : List Bool) (data : Fin (tapes p) → List Bool)
    (hdata : ∀ i, data (preparedSlot p i)=preparedInput p cap word i)
    (hout0 : data (outputSlot p)=[]) (horigin0 : data (originSlot p)=[]) :
    ∃ receipt, run (core p) (14*cap+24) data=some receipt ∧
      receipt.final.tapes (outputSlot p)=frame (cappedResultWord p (cap,word)) := by
  obtain ⟨localRun,output,marker,hl,hlh,hlo,hlm,hm,hls,ha,hlc⟩ := prepared_run_clock p cap word
  obtain ⟨first,hfirst,_,_,hh,ht,ho⟩ := RecoveryFocus.dock (preparedSlot p)
    (preparedSlot_injective p) (preparedMachine p) (2*cap+4) (fun _ => 0) data
    (initialConfiguration (preparedMachine p) (preparedInput p cap word))
    (fun _ => rfl) hdata localRun hl
  have hlen : (run p.machine cap (p.inputTapes word)).isSome=true → output.length ≤ cap := by
    intro h
    cases hs : run p.machine cap (p.inputTapes word) with
    | none => simp [hs] at h
    | some source => rw [ha source hs]; exact OutputTracking.program_output_bound p word cap source hs
  obtain ⟨localResult,hlr,hlout⟩ := ResultWriter.result_run output marker cap
    (run p.machine cap (p.inputTapes word)).isSome hm hlen
  have hheads : ∀ i : Fin 6, first.final.heads (resultSlot p i)=0 := by
    intro i
    fin_cases i
    · exact (hh (preparedOutputSlot p)).trans (hlh _)
    · exact (ho (outputSlot p) (outputSlot_fresh p)).1
    · exact (ho (originSlot p) (originSlot_fresh p)).1
    · exact (hh (preparedMarkerSlot p)).trans (hlh _)
    · exact (hh (preparedClockSlot p)).trans (hlh _)
    · exact (hh (preparedStatusSlot p)).trans (hlh _)
  have htapes : ∀ i : Fin 6, first.final.tapes (resultSlot p i)=
      ResultWriter.input output marker cap (run p.machine cap (p.inputTapes word)).isSome i := by
    intro i
    fin_cases i
    · exact (ht (preparedOutputSlot p)).trans hlo
    · exact (ho (outputSlot p) (outputSlot_fresh p)).2.trans hout0
    · exact (ho (originSlot p) (originSlot_fresh p)).2.trans horigin0
    · exact (ht (preparedMarkerSlot p)).trans hlm
    · exact (ht (preparedClockSlot p)).trans hlc
    · exact (ht (preparedStatusSlot p)).trans hls
  obtain ⟨last,hlast,_,_,_,hlt,_⟩ := RecoveryFocus.dock (resultSlot p)
    (resultSlot_injective p) ResultWriter.machine (12*cap+19) first.final.heads first.final.tapes
    (initialConfiguration ResultWriter.machine
      (ResultWriter.input output marker cap (run p.machine cap (p.inputTapes word)).isSome))
    hheads htapes localResult hlr
  have hj := Composition.run_join (prepared p) (result p) (2*cap+4) (12*cap+19)
    _ first last hfirst hlast
  have hbudget : (2*cap+4)+1+(12*cap+19)=14*cap+24 := by omega
  rw [hbudget] at hj
  change run (core p) (14*cap+24) data=some _ at hj
  refine ⟨_,hj,?_⟩
  change last.final.tapes (outputSlot p)=frame (cappedResultWord p (cap,word))
  have he := hlt 1
  change last.final.tapes (outputSlot p)=localResult.final.tapes 1 at he
  rw [he,hlout]
  cases hs : run p.machine cap (p.inputTapes word) with
  | none => simp [cappedResultWord,hs]
  | some source => simp [cappedResultWord,hs,ha source hs]

end NearCubicGates.Adapters.Machine.Capped.Layout
