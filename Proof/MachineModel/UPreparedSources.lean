import Proof.MachineModel.UInitializedSources
import Proof.MachineModel.UPreparedRun

/-! Numeric and head-array preparation preserves all witness/event fields
needed by the actual transition walk, including both streaming cursors. -/
namespace NearCubicWires.RepairOrdinary.UPrepared
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_fields {s : ℕ} (raw witness : List Bool) (final : Configuration 139 s)
    (hp : Prepared raw witness final) :
    UInitialized.SourceFields raw witness (fun i => final.heads (i.castAdd 42))
      (fun i => final.tapes (i.castAdd 42)) := by
  obtain ⟨base,c,t,j,hbase,_,_,_,_,_,_,_,hkeep,_,_⟩ := hp
  obtain ⟨x,choices,hn,hB,hw,he⟩ := UInitialized.source_fields raw witness base hbase
  obtain ⟨word,bound,padding,m,suffix,hraw,hguards,hprefix,hm,hchoices,h1t,h1h,h74t,h74h⟩ := hw
  obtain ⟨hserial,hI,hout,h91h,h21h,h92h⟩ := he
  have h1 := hkeep 1 (by decide) (by decide) (by decide) (by decide)
  have h21 := hkeep 21 (by decide) (by decide) (by decide) (by decide)
  have h74 := hkeep 74 (by decide) (by decide) (by decide) (by decide)
  have h91 := hkeep 91 (by decide) (by decide) (by decide) (by decide)
  have h92 := hkeep 92 (by decide) (by decide) (by decide) (by decide)
  refine ⟨x,choices,hn,hB,⟨word,bound,padding,m,suffix,hraw,hguards,hprefix,hm,hchoices,
    h1.1.trans h1t,h1.2.trans h1h,h74.1.trans h74t,h74.2.trans h74h⟩,?_,
    h21.1.trans hI,h92.1.trans hout,h91.2.trans h91h,h21.2.trans h21h,?_⟩
  · exact (congrArg (ZeroPadding.pad (2*ClockDyadicLedger.width raw.length)) h91.1).trans hserial
  · exact h92.2.trans (h92h.trans (congrArg List.length h92.1).symm)

end NearCubicWires.RepairOrdinary.UPrepared
