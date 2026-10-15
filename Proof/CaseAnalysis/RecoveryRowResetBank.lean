import Proof.CaseAnalysis.RecoveryRowAfter

/-! The checked whole-row/reset worker runs beside the paid outer stack,
prototype packet and two coarse clearing drivers. Every extra tape survives. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReusable
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 74) : Fin 78:=i.castAdd 4
theorem slots_injective : Function.Injective slots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 78=>k.val) h)
noncomputable def first:=RecoveryFocus.machine slots RecoveryBoundedRowReuse.machine

theorem entry_heads (out stack : List Bool) (A : Fin 73→List Bool) (B : ℕ) :
    ∀ i,RecoveryBoundedRowAfter.heads out stack (slots i)=(RecoveryBoundedRowReuse.entry out A B).heads i := by
  intro i;fin_cases i <;> rfl
theorem entry_tapes (out stack packet : List Bool) (A : Fin 73→List Bool) (B : ℕ) :
    ∀ i,RecoveryBoundedRowAfter.data A B stack packet (slots i)=(RecoveryBoundedRowReuse.entry out A B).tapes i := by
  intro i;fin_cases i <;> first | rfl | exact (ZeroPadding.pad_zero _).symm
theorem slots_old (i : Fin 73) : slots (i.castAdd 1)=RecoveryBoundedRowAfter.old i := rfl
theorem slots_high (i : Fin 74) (j : Fin 78) (hj : 74≤j.val) : slots i≠j := by
  intro h;have hv:=congrArg (fun k : Fin 78=>k.val) h;have hi:=i.isLt;change i.val=j.val at hv;omega

theorem reset_bank_run (out result stack packet : List Bool) (A : Fin 73→List Bool) (u S B : ℕ)
    (r : ExecutionReceipt 73 _)
    (hr : runFrom RecoveryBoundedRow.machine u ⟨RecoveryBoundedRow.machine.start,RecoveryBoundedRow.heads out [] [],A⟩=some r)
    (hs : r.steps≤u) (hS : 1≤S) (ho : out.length≤S) (hA : ∀ i,(A i).length≤S)
    (hB : S+u+3≤B) (hresult : r.final.heads 20=result.length) :
    ∃ q,runFrom first (2*(u+2)+2)
      ⟨first.start,RecoveryBoundedRowAfter.heads out stack,
        RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B A) B stack packet⟩=some q ∧
      q.steps≤2*(u+2)+2 ∧ q.final.heads=RecoveryBoundedRowAfter.heads result stack ∧
      q.final.tapes=RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B r.final.tapes) B stack packet ∧
      (∀ i,(RecoveryBoundedRowReuse.paddedData B r.final.tapes i).length≤B) := by
  obtain ⟨p,pr,ps,ph,pt,pb⟩:=RecoveryBoundedRowReuse.padded_reset_run out A u S B r hr hs hS ho hA hB
  obtain ⟨q,qr,_,qs,qh,qt,qkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedRowReuse.machine _
    (RecoveryBoundedRowAfter.heads out stack)
    (RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B A) B stack packet)
    (RecoveryBoundedRowReuse.entry out (RecoveryBoundedRowReuse.paddedData B A) B)
    (entry_heads out stack _ B) (entry_tapes out stack packet _ B) p pr
  refine ⟨q,qr,qs.le.trans ps,?_,?_,pb⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [qh j,ph,hresult]
      fin_cases j <;> rfl
    · rw [(qkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      have h20 : i≠20:=fun he=>hi ⟨20,he.symm⟩
      simp only [RecoveryBoundedRowAfter.heads,if_neg h20]
  · funext i
    refine Fin.addCases (m:=73) (n:=5) ?_ ?_ i
    · intro j
      change q.final.tapes (slots (j.castAdd 1))=_
      rw [qt,pt]
      simp only [RecoveryBoundedRowReuse.resultData,RecoveryBoundedRowAfter.data,Fin.addCases_left]
    · intro j;fin_cases j
      · change q.final.tapes (slots 73)=_
        rw [qt,pt]
        rfl
      all_goals first
        | exact (qkeep 74 (fun i=>slots_high i 74 (by decide))).2
        | exact (qkeep 75 (fun i=>slots_high i 75 (by decide))).2
        | exact (qkeep 76 (fun i=>slots_high i 76 (by decide))).2
        | exact (qkeep 77 (fun i=>slots_high i 77 (by decide))).2

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReusable
