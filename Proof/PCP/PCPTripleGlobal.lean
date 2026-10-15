import Proof.PCP.PCPTripleGlobalDock

/-! Whole clause serialization from its original M/stream and blank work. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleGlobal
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem global_run (pre : List Bool) (groups : List (List (List Bool))) (suffix : List Bool)
    (hthree : ∀ fields∈groups,fields.length=3) :
    ∃ r,runFrom machine (budget (PCPTripleLoop.stream groups).length groups.length)
      (entry groups.length (pre++PCPTripleLoop.stream groups++suffix) pre.length)=some r ∧
      r.final.tapes 0=CompareMachine.word groups.length ∧ r.final.heads 0=1 ∧
      r.final.tapes 5=pre++PCPTripleLoop.stream groups++suffix ∧
      r.final.heads 5=pre.length+(PCPTripleLoop.stream groups).length ∧
      r.final.tapes 177=PCPTripleLoop.encoded groups ∧
      r.final.heads 177=(PCPTripleLoop.encoded groups).length ∧
      r.final.tapes 37=List.replicate (envelope (PCPTripleLoop.stream groups).length) true ∧
      r.final.heads 37=0 ∧ r.steps ≤ budget (PCPTripleLoop.stream groups).length groups.length := by
  obtain ⟨p,hp,ph,p0,_p3,p5,_p6,p37,ps⟩ :=
    PCPTripleEnvelope.envelope_run pre groups.flatten suffix groups.length (flatten_length groups hthree)
  rw [flatten_stream] at hp p5 p37 ps
  obtain ⟨base,hb,bh,bt,bs⟩ := cold_data_run pre groups suffix hthree
  have h := dock_run PCPTripleEnvelope.machine PCPTripleCold.machine _ _ p hp
    (envelope (PCPTripleLoop.stream groups).length) groups.length pre.length
    (pre.length+(PCPTripleLoop.stream groups).length)
    (pre++PCPTripleLoop.stream groups++suffix) (PCPTripleLoop.encoded groups)
    ph p0 p5 p37 ps base hb bh bt bs
  exact h

end NearCubicWires.RepairOrdinary.PCPTripleGlobal
