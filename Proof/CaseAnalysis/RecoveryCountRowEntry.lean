import Proof.CaseAnalysis.RecoveryCountIncrement

/-! The complete original grammar-to-row entry: one shared candidate
increment followed by the exact paid original row metadata installation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountRowEntry
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (heads)
open RecoveryBoundedRowPacketInstall (fields printed)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine RecoveryBoundedCountIncrement.machine RecoveryBoundedRowPacketInstall.machine
def budget (C D F L R count Q clauses B : ℕ):=
  2*count+4+1+RecoveryBoundedRowPacketInstall.budget C D F L R (count+1) Q clauses B
noncomputable def result (C D F L R count Q clauses B : ℕ) (A : Fin 88→List Bool):=
  RecoveryBoundedRowPacketLoad.bank (fields C D F L R (count+1) Q clauses) B
    (printed C D F L R (count+1) Q clauses B (RecoveryBoundedCountIncrement.next A count))

theorem run (C D F L R count Q clauses B : ℕ) (out stack : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (h : RecoveryBoundedRowPacketAppend.Loaded (RecoveryBoundedRowPacketAppend.values C F R count Q clauses) B H A)
    (hn : 2*(count+1)+4≤B) (hfit : 6+F≤C)
    (hH : ∀ j,H (RecoveryBoundedRowPacketLoad.slots j)=heads out stack j)
    (hp : (A 75).length≤B) (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hA : ∀ i,(A (RecoveryBoundedRowPacketLoad.slots (RecoveryBoundedRowErase.work i))).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L R (count+1) Q clauses j).length≤B)
    (bp : (RecoveryBoundedRowReload.word (fields C D F L R (count+1) Q clauses)).length≤B) :
    ∃ r,runFrom machine (budget C D F L R count Q clauses B) ⟨machine.start,H,A⟩=some r ∧
      r.steps≤budget C D F L R count Q clauses B ∧ r.final.heads=H ∧
      r.final.tapes=result C D F L R count Q clauses B A := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedCountIncrement.loaded_run h
  let next:=RecoveryBoundedCountIncrement.next A count
  have keep (i : Fin 88) (hi : i≠81) : next i=A i:=Function.update_of_ne hi _ _
  have hb : ∀ i,(next (RecoveryBoundedRowPacketLoad.slots (RecoveryBoundedRowErase.work i))).length≤B:=by
    intro i
    rw [keep]
    · exact hA i
    · intro he
      have hv:=congrArg Fin.val he
      have hw:=(RecoveryBoundedRowErase.work_spec i).1
      change (RecoveryBoundedRowErase.work i).val=81 at hv
      omega
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedRowPacketInstall.run C D F L R (count+1) Q clauses B out stack H next
    (RecoveryBoundedCountIncrement.loaded_next h hn) hfit hH
    (by rw [keep 75 (by decide)];exact hp) (by rw [keep 76 (by decide)];exact hd)
    (by rw [keep 77 (by decide)];exact hl) hb hf bp
  have qr' : runFrom RecoveryBoundedRowPacketInstall.machine
      (RecoveryBoundedRowPacketInstall.budget C D F L R (count+1) Q clauses B)
      (restart p.final RecoveryBoundedRowPacketInstall.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have whole:=Composition.run_join RecoveryBoundedCountIncrement.machine RecoveryBoundedRowPacketInstall.machine _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,whole,?_,qh,qt⟩
  change p.steps+1+q.steps≤budget C D F L R count Q clauses B
  unfold budget
  omega

def capacities (B : ℕ) (i : Fin 88):=if 78 ≤ i.val then B else 0

theorem padded_run (C D F L R count Q clauses B : ℕ) (out stack : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (h : RecoveryBoundedRowPacketAppend.Loaded (RecoveryBoundedRowPacketAppend.values C F R count Q clauses) B H A)
    (hn : 2*(count+1)+4≤B) (hfit : 6+F≤C)
    (hH : ∀ j,H (RecoveryBoundedRowPacketLoad.slots j)=heads out stack j)
    (hp : (A 75).length≤B) (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hA : ∀ i,(A (RecoveryBoundedRowPacketLoad.slots (RecoveryBoundedRowErase.work i))).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L R (count+1) Q clauses j).length≤B)
    (bp : (RecoveryBoundedRowReload.word (fields C D F L R (count+1) Q clauses)).length≤B) :
    ∃ r,runFrom machine (budget C D F L R count Q clauses B)
      ⟨machine.start,H,fun i=>ZeroPadding.pad (capacities B i) (A i)⟩=some r ∧
      r.steps≤budget C D F L R count Q clauses B ∧ r.final.heads=H ∧
      r.final.tapes=(fun i=>ZeroPadding.pad (capacities B i) (result C D F L R count Q clauses B A i)) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=run C D F L R count Q clauses B out stack H A h hn hfit hH hp hd hl hA hf bp
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config machine (capacities B) _ _ p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · rw [rf];exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (capacities B i) (p.final.tapes i))=_
    rw [pt]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountRowEntry
