import Proof.Amplification.RecoveryOuterRootTail

namespace NearCubicWires.RepairOrdinary.RecoveryOuterRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem continuation_run {s : Nat} (limit : Nat) (word bits innerBits : List Bool)
    (innerRows : List Row) (innerRest : List Bool) (x : State)
    (hx : x.Valid word bits innerBits) (first : Configuration 86 s)
    (hout : RecoveryRowTable.tableCheck x.data.outer.base.state.bits.length
      (RecoveryOuterLeaf.predicate innerRows) x.total [] bits=true →
      ∃ out : RecoveryOuterTable.Cursor,
        first=(⟨out.data,x.total,x.key⟩ : State).cfg first.control ∧
        RecoveryOuterTable.Inv x.data.outer.base.state.bits.length limit word bits innerBits innerRows innerRest out ∧
        out.data.outer.total=x.total) :
    RecoveryRowTable.tableCheck x.data.outer.base.state.bits.length
      (RecoveryOuterLeaf.predicate innerRows) x.total [] bits=true → ∃ last,
      runFrom rootMachine (rootBudget x.data.outer.base.state.bits.length x.total)
        (RecoveryCalls.restarted rootMachine first.heads first.tapes)=some last ∧
      last.final.heads 50=0 ∧ last.final.tapes 50=[wholeAnswer x innerRows bits] := by
  intro ha
  obtain ⟨out,hf,hi,hjout⟩ := hout ha
  obtain ⟨last,hl,hh,ht⟩ := root_tail_run limit word bits innerBits innerRows innerRest x out hx hi hjout ha
  have he : RecoveryCalls.restarted rootMachine first.heads first.tapes=
      (⟨out.data,x.total,x.key⟩ : State).cfg rootMachine.start := by rw [hf]; rfl
  rw [he]
  exact ⟨last,hl,hh,ht⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterRoot
