import Proof.CaseAnalysis.RecoveryCountPacketCanonical

/-! The actual shared count increment and original row reload, with paid
scalar backing and the same retained reference-stack backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketCanonical
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedRowPacketAppend (values)
open RecoveryBoundedRowPrototype (fields)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def packet (C D F L R count Q clauses B : ℕ):=
  ZeroPadding.pad B (RecoveryBoundedRowReload.word (fields C D F L R count Q clauses))
def capacity (B P : ℕ) (i : Fin 88):=if i=74 then P else if 78 ≤ i.val then B else 0
def padded (B P : ℕ) (A : Fin 78→List Bool) (v : Fin 10→ℕ) : Fin 88→List Bool:=
  fun i=>ZeroPadding.pad (capacity B P i) (data A v i)

theorem run (C D F L R count Q clauses B node : ℕ) (current : Fin 78→List Bool)
    (out stack oldPacket source : List Bool)
    (hb : ∀ j,2*values C F R count Q clauses j+4≤B) (hn : 2*(count+1)+4≤B)
    (hfit : 6+F≤C) (hp : oldPacket.length≤B)
    (hc : ∀ j∈RecoveryBoundedRowReload.ports,(current j).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L R (count+1) Q clauses j).length≤B)
    (bp : (RecoveryBoundedRowReload.word (fields C D F L R (count+1) Q clauses)).length≤B) :
    ∃ r,runFrom RecoveryBoundedCountRowEntry.machine (RecoveryBoundedCountRowEntry.budget C D F L R count Q clauses B)
      ⟨RecoveryBoundedCountRowEntry.machine.start,heads out stack,
        data (RecoveryBoundedGrammarBank.ready current node B out stack oldPacket source) (values C F R count Q clauses)⟩=some r ∧
      r.steps≤RecoveryBoundedCountRowEntry.budget C D F L R count Q clauses B ∧
      r.final.heads=heads out stack ∧
      r.final.tapes=data (RecoveryBoundedGrammarBank.ready (fields C D F L R (count+1) Q clauses)
        node B out stack (packet C D F L R (count+1) Q clauses B) source) (values C F R (count+1) Q clauses) := by
  let A:=data (RecoveryBoundedGrammarBank.ready current node B out stack oldPacket source) (values C F R count Q clauses)
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedCountRowEntry.run C D F L R count Q clauses B out stack (heads out stack) A
    (loaded current node B out stack oldPacket source (values C F R count Q clauses) hb) hn hfit
    (by intro j;simp only [heads,RecoveryBoundedRowPacketLoad.slots,Fin.addCases_left])
    (by exact hp) rfl rfl (by
      intro i
      simp only [A,data,RecoveryBoundedRowPacketLoad.slots,Fin.addCases_left]
      rw [RecoveryBoundedGrammarBank.ready_work]
      split
      · rename_i hi
        simp only [ZeroPadding.pad_length]
        exact max_le (le_refl B) (hc _ hi)
      · simp only [List.length_replicate,le_refl]) hf bp
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt,result C D F L R count Q clauses B node current out stack oldPacket source hb hn]
  rfl

theorem padded_run (C D F L R count Q clauses B P node : ℕ) (current : Fin 78→List Bool)
    (out stack oldPacket source : List Bool)
    (hb : ∀ j,2*values C F R count Q clauses j+4≤B) (hn : 2*(count+1)+4≤B)
    (hfit : 6+F≤C) (hp : oldPacket.length≤B)
    (hc : ∀ j∈RecoveryBoundedRowReload.ports,(current j).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L R (count+1) Q clauses j).length≤B)
    (bp : (RecoveryBoundedRowReload.word (fields C D F L R (count+1) Q clauses)).length≤B) :
    ∃ r,runFrom RecoveryBoundedCountRowEntry.machine (RecoveryBoundedCountRowEntry.budget C D F L R count Q clauses B)
      ⟨RecoveryBoundedCountRowEntry.machine.start,heads out stack,
        padded B P (RecoveryBoundedGrammarBank.ready current node B out stack oldPacket source) (values C F R count Q clauses)⟩=some r ∧
      r.steps≤RecoveryBoundedCountRowEntry.budget C D F L R count Q clauses B ∧
      r.final.heads=heads out stack ∧
      r.final.tapes=padded B P (RecoveryBoundedGrammarBank.ready (fields C D F L R (count+1) Q clauses)
        node B out stack (packet C D F L R (count+1) Q clauses B) source) (values C F R (count+1) Q clauses) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=run C D F L R count Q clauses B node current out stack oldPacket source hb hn hfit hp hc hf bp
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config RecoveryBoundedCountRowEntry.machine (capacity B P) _ _ p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · rw [rf];exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (capacity B P i) (p.final.tapes i))=_
    rw [pt]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketCanonical
