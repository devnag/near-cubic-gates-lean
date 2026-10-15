import Proof.CaseAnalysis.RecoveryTableIndexBank

/-! The original table advances every retained row index by exactly
rowWidth=2*fieldLimit+6. All three actual driver scans and rewinds are paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexAdvance
open LocalBitMultitape Composition RecoveryBoundedTableIndexBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pair:=Composition.machine (RecoveryBoundedTableIndexBank.machine false) (RecoveryBoundedTableIndexBank.machine false)
noncomputable def machine:=Composition.machine pair (RecoveryBoundedTableIndexBank.machine true)
def budget (F W : ℕ):=2*RecoveryBoundedTableIndexLoop.budget F W+RecoveryBoundedTableIndexLoop.budget 6 W+2

theorem advance_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (a b c F C W : ℕ)
    (hH : ∀ six j,H (slots six j)=heads j)
    (hF : ∀ j,A (slots false j)=input a b c C F j) (h6 : ∀ j,A (slots true j)=input a b c C 6 j)
    (ha : a+(2*F+6) ≤ W) (hb : b+(2*F+6) ≤ W) (hc : c+(2*F+6) ≤ W) (hC : W+1 ≤ C) :
    ∃ r,runFrom machine (budget F W) ⟨machine.start,H,A⟩=some r ∧ r.steps ≤ budget F W ∧
      r.final.heads=H ∧ r.final.tapes=output A a b c (2*F+6) := by
  let A1:=output A a b c F
  let A2:=output A1 (a+F) (b+F) (c+F) F
  obtain ⟨p,pr,ps,ph,pt⟩:=index_run false H A a b c F C W (hH false) hF (by omega) (by omega) (by omega) hC
  have hF1 : ∀ j,A1 (slots false j)=input (a+F) (b+F) (c+F) C F j:=output_slot false A a b c F C F hF
  obtain ⟨q,qr,qs,qh,qt⟩:=index_run false H A1 (a+F) (b+F) (c+F) F C W (hH false) hF1
    (by omega) (by omega) (by omega) hC
  have qr' : runFrom (RecoveryBoundedTableIndexBank.machine false) (RecoveryBoundedTableIndexLoop.budget F W)
      (restart p.final (RecoveryBoundedTableIndexBank.machine false).start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have pq:=Composition.run_join (RecoveryBoundedTableIndexBank.machine false) (RecoveryBoundedTableIndexBank.machine false)
    _ _ _ p q pr qr'
  have h61 : ∀ j,A1 (slots true j)=input (a+F) (b+F) (c+F) C 6 j:=output_slot true A a b c F C 6 h6
  have h62 : ∀ j,A2 (slots true j)=input (a+F+F) (b+F+F) (c+F+F) C 6 j:=
    output_slot true A1 (a+F) (b+F) (c+F) F C 6 h61
  obtain ⟨r,rr,rs,rh,rt⟩:=index_run true H A2 (a+F+F) (b+F+F) (c+F+F) 6 C W (hH true) h62
    (by omega) (by omega) (by omega) hC
  have rr' : runFrom (RecoveryBoundedTableIndexBank.machine true) (RecoveryBoundedTableIndexLoop.budget 6 W)
      (restart (joinedReceipt p q).final (RecoveryBoundedTableIndexBank.machine true).start)=some r := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some r
    rw [qh,qt]
    exact rr
  have full:=Composition.run_join pair (RecoveryBoundedTableIndexBank.machine true) _ _ _ (joinedReceipt p q) r pq rr'
  have he : ((RecoveryBoundedTableIndexLoop.budget F W+1+RecoveryBoundedTableIndexLoop.budget F W)+1+
      RecoveryBoundedTableIndexLoop.budget 6 W)=budget F W := by unfold budget;omega
  rw [he] at full
  refine ⟨joinedReceipt (joinedReceipt p q) r,full,?_,rh,?_⟩
  · change p.steps+1+q.steps+1+r.steps ≤ budget F W
    unfold budget
    omega
  · change r.final.tapes=_
    dsimp only [A2,A1] at rt
    rw [output_add,output_add] at rt
    have he : F+(F+6)=2*F+6:=by omega
    rw [he] at rt
    exact rt

theorem budget_quadratic (F W : ℕ) (hF : F ≤ W) (h6 : 6 ≤ W) :
    budget F W ≤ 128*(W+1)^2 := by
  have hf:=RecoveryBoundedTableIndexLoop.budget_quadratic F W hF
  have h6:=RecoveryBoundedTableIndexLoop.budget_quadratic 6 W h6
  unfold budget
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexAdvance
