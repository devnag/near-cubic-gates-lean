import Proof.Amplification.RecoveryQueryCall

/-! Whole reusable prefix query and physical Boolean answer. This is an
actual ordinary oracle trace, with the one retained capacity driver explicit. -/
namespace NearCubicWires.RepairSource.RecoveryQueryStep
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose RecoveryQuery
open RecoveryQueryKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def answerSlot : Fin 357 := 356
def ports : Ports 357 := ⟨by decide,answerSlot,by decide,querySlot,by decide⟩
noncomputable abbrev piece (flat : Bool) := RecoveryQueryCall.piece (kernel flat) answerSlot
noncomputable abbrev program (flat : Bool) := ports.program (piece flat)
noncomputable def start (flat : Bool) (tapes : Fin 357→List Bool) :=
  RecoveryQueryCall.start (kernel flat) answerSlot tapes
noncomputable def stopped (flat : Bool) (tapes : Fin 357→List Bool) :=
  RecoveryQueryCall.stopped (kernel flat) answerSlot tapes

theorem step_trace (cap log : Nat) (flat : Bool) (payload committed count : Nat)
    (ambient : Fin 357→List Bool) (paddedPayload paddedCommitted paddedCount : List Bool)
    (hcap : capacity payload committed count ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1)
    (hp : ambient 0=frame payload.bits++paddedPayload)
    (ha : ambient 1=frame committed.bits++paddedCommitted)
    (hn : ambient 2=frame count.bits++paddedCount) :
    ∃ cost ≤ 18*cap,∃ out : Fin 357→List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program flat) cost
        (start flat ambient) (stopped flat out) ∧
      readTapeBit (out answerSlot) 0=RecoveryOracle.correctedSat (code flat payload committed count) ∧
      (∀ i : Fin 357,i.val<3 → out i=ambient i) ∧
      out 3=List.replicate cap true ∧ out 4=List.replicate (cap+1) false ∧ Bounded cap out := by
  classical
  obtain ⟨middle,hready,hquery,hkeep,hdriver,hlog,hbound⟩ := query_run cap log flat payload committed count
    ambient paddedPayload paddedCommitted paddedCount hcap hb hd hl hz hp ha hn
  obtain ⟨cost,hcost,htrace⟩ := RecoveryQueryCall.call_trace ports (kernel flat) answerSlot
    RecoveryOracle.correctedSat (16*cap) ambient middle (code flat payload committed count).bits
    (List.replicate (cap-(frame (code flat payload committed count).bits).length) false) hready hquery
  rw [CanonicalBinary.bitsValue_natBits] at htrace
  let out := RecoveryQueryAnswer.output answerSlot middle (RecoveryOracle.correctedSat (code flat payload committed count))
  have hwidth := (PCPSerializerMass.nat_bits_width (code flat payload committed count)).trans
    (code_width flat payload committed count)
  have hbase : bytes payload committed count+1 ≤ (bytes payload committed count+1)^2 := by nlinarith
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hcapone : 1 ≤ cap := by unfold capacity at hcap; omega
  have htotal : cost ≤ 18*cap := by
    rw [frame_length] at hcost
    unfold capacity at hcap
    omega
  refine ⟨cost,htotal,out,htrace,?_,?_,?_,?_,?_⟩
  · simp only [out,RecoveryQueryAnswer.output,Function.update_self]
    cases middle answerSlot <;> simp [readTapeBit,writeTapeBit]
  · intro i hi
    have hne : i≠answerSlot := by intro h; subst i; change (356 : Nat)<3 at hi; omega
    simpa [out,RecoveryQueryAnswer.output,hne] using hkeep i hi
  · simpa [out,RecoveryQueryAnswer.output,answerSlot] using hdriver
  · simpa [out,RecoveryQueryAnswer.output,answerSlot] using hlog
  · intro i hi
    by_cases he : i=answerSlot
    · subst i
      simp only [out,RecoveryQueryAnswer.output,Function.update_self,RecoveryTapeSupport.write_length]
      exact max_le (hbound answerSlot (by decide)) hcapone
    · simpa [out,RecoveryQueryAnswer.output,he] using hbound i hi

end NearCubicWires.RepairSource.RecoveryQueryStep
