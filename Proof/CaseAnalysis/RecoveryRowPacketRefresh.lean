import Proof.CaseAnalysis.RecoveryRowPacketReady

/-! Refresh the grammar packet into the exact original row packet. The
old packet is physically erased using the same paid B driver and log. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 3→Fin 88:=![75,76,77]
noncomputable def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def refresh:=Composition.machine erase ready
def refreshBudget (C F R count Q clauses B : ℕ):=2*B+4+1+readyBudget C F R count Q clauses B

theorem erase_run (B : ℕ) (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (hH : ∀ j,H (eraseSlots j)=0) (hp : (A 75).length≤B)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false) :
    ∃ r,runFrom erase (2*B+4) ⟨erase.start,H,A⟩=some r ∧ r.steps≤2*B+4 ∧
      r.final.heads=H ∧ r.final.tapes=Function.update A 75 (List.replicate B false) := by
  have base:=RecoveryScratchErase.erase_ready B (B+1) (fun _ : Fin 1=>A 75) (fun _=>hp)
  obtain ⟨r,rr,rh,rt,rs⟩:=base.focus_at eraseSlots (by decide) H A
    (by intro j;fin_cases j;rfl;exact hd;exact hl) hH
  refine ⟨r,rr,rs.le,rh,?_⟩
  rw [rt]
  apply HierarchyWidth.install_eq eraseSlots (by decide)
  · intro j;fin_cases j
    · rfl
    · change A 76=List.replicate B true
      exact hd
    · change A 77=List.replicate (max (B+1) (B+1)) false
      rw [max_self]
      exact hl
  · intro i hi
    have h75 : i≠75:=fun he=>hi 0 he.symm
    exact Function.update_of_ne h75 _ _

theorem Loaded.update_packet {v : Fin 10→ℕ} {B : ℕ} {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : Loaded v B H A) (bits : List Bool) : Loaded v B H (Function.update A 75 bits) := by
  refine ⟨h.heads,?_,h.scratch_head,?_,h.bounds⟩
  · intro j
    rw [Function.update_of_ne (scalar_ne_output j)]
    exact h.tapes j
  · rw [Function.update_of_ne (by decide)]
    exact h.scratch_tape

theorem refresh_run (C D F L R count Q clauses B : ℕ) (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (h : Loaded (values C F R count Q clauses) B H A) (hfit : 6+F≤C)
    (hH : ∀ j,H (eraseSlots j)=0) (hp : (A 75).length≤B)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (bp : (RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses)).length≤B) :
    ∃ r,runFrom refresh (refreshBudget C F R count Q clauses B) ⟨refresh.start,H,A⟩=some r ∧
      r.steps≤refreshBudget C F R count Q clauses B ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A 75
        (ZeroPadding.pad B (RecoveryBoundedRowReload.word
          (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses))) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=erase_run B H A hH hp hd hl
  obtain ⟨q,qr,qs,qh,qt⟩:=ready_run C D F L R count Q clauses B H
    (Function.update A 75 (List.replicate B false)) (h.update_packet _) hfit (hH 0) (hH 1)
    (by rw [Function.update_of_ne (by decide)];exact hd) rfl bp
  have qr' : runFrom ready (readyBudget C F R count Q clauses B) (restart p.final ready.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have whole:=Composition.run_join erase ready _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,whole,?_,qh,?_⟩
  · change p.steps+1+q.steps≤refreshBudget C F R count Q clauses B
    unfold refreshBudget
    omega
  · change q.final.tapes=_
    rw [qt,Function.update_idem]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
