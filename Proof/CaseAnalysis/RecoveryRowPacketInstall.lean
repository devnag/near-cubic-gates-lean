import Proof.CaseAnalysis.RecoveryRowPacketLoad

/-! The whole grammar-to-row metadata handoff: refresh the exact original
prototype, clear the old work fields, reload, and preserve graph/count/refs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketInstall
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine RecoveryBoundedRowPacketAppend.refresh RecoveryBoundedRowPacketLoad.machine
def fields (C D F L R count Q clauses : ℕ):=RecoveryBoundedRowPrototype.fields C D F L R count Q clauses
def printed (C D F L R count Q clauses B : ℕ) (A : Fin 88→List Bool):=
  Function.update A 75 (ZeroPadding.pad B (RecoveryBoundedRowReload.word (fields C D F L R count Q clauses)))
def budget (C D F L R count Q clauses B : ℕ):=
  RecoveryBoundedRowPacketAppend.refreshBudget C F R count Q clauses B+1+
    RecoveryBoundedRowPacketLoad.budget (fields C D F L R count Q clauses) B

theorem run (C D F L R count Q clauses B : ℕ) (out stack : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (h : RecoveryBoundedRowPacketAppend.Loaded (RecoveryBoundedRowPacketAppend.values C F R count Q clauses) B H A)
    (hfit : 6+F≤C) (hH : ∀ j,H (RecoveryBoundedRowPacketLoad.slots j)=heads out stack j)
    (hp : (A 75).length≤B) (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hA : ∀ i,(A (RecoveryBoundedRowPacketLoad.slots (RecoveryBoundedRowErase.work i))).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L R count Q clauses j).length≤B)
    (bp : (RecoveryBoundedRowReload.word (fields C D F L R count Q clauses)).length≤B) :
    ∃ r,runFrom machine (budget C D F L R count Q clauses B) ⟨machine.start,H,A⟩=some r ∧
      r.steps≤budget C D F L R count Q clauses B ∧ r.final.heads=H ∧
      r.final.tapes=RecoveryBoundedRowPacketLoad.bank (fields C D F L R count Q clauses) B
        (printed C D F L R count Q clauses B A) := by
  have hz : ∀ j,H (RecoveryBoundedRowPacketAppend.eraseSlots j)=0:=by
    intro j;fin_cases j
    · exact hH 75
    · exact hH 76
    · exact hH 77
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedRowPacketAppend.refresh_run C D F L R count Q clauses B H A h hfit hz hp hd hl bp
  let next:=printed C D F L R count Q clauses B A
  have keep (i : Fin 88) (hi : i≠75) : next i=A i:=Function.update_of_ne hi _ _
  have hb : ∀ i,(next (RecoveryBoundedRowPacketLoad.slots (RecoveryBoundedRowErase.work i))).length≤B:=by
    intro i
    rw [keep]
    · exact hA i
    · intro he
      have hv:=congrArg Fin.val he
      have hw:=(RecoveryBoundedRowErase.work_spec i).1
      change (RecoveryBoundedRowErase.work i).val=75 at hv
      omega
  let word:=RecoveryBoundedRowReload.word (fields C D F L R count Q clauses)
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedRowPacketLoad.load_run out stack
    (List.replicate (B-word.length) false) (fields C D F L R count Q clauses) B H next hH
    (by rw [keep 73 (by decide)];exact h.scratch_tape) rfl
    (by rw [keep 76 (by decide)];exact hd) (by rw [keep 77 (by decide)];exact hl) hb hf bp
  have qr' : runFrom RecoveryBoundedRowPacketLoad.machine
      (RecoveryBoundedRowPacketLoad.budget (fields C D F L R count Q clauses) B)
      (restart p.final RecoveryBoundedRowPacketLoad.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have whole:=Composition.run_join RecoveryBoundedRowPacketAppend.refresh RecoveryBoundedRowPacketLoad.machine _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,whole,?_,qh,qt⟩
  change p.steps+1+q.steps≤budget C D F L R count Q clauses B
  unfold budget
  omega

theorem budget_bound (C D F L R count Q clauses B : ℕ) {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : RecoveryBoundedRowPacketAppend.Loaded (RecoveryBoundedRowPacketAppend.values C F R count Q clauses) B H A)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L R count Q clauses j).length≤B) :
    budget C D F L R count Q clauses B≤1024*(B+1) := by
  have hr:=h.refresh_bound
  have hl:=RecoveryBoundedRowReload.budget_bound (fields C D F L R count Q clauses) B hf
  unfold budget RecoveryBoundedRowPacketLoad.budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketInstall
