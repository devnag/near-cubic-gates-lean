import Proof.CaseAnalysis.RecoveryClauseGate
import Proof.CaseAnalysis.RecoveryClauseReplace

/-! Complete original single-node append: emit the exact native node,
return its actual live reference and advance the retained graph count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralNode
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def second (kind : Fin 4):=decide (kind=1)
noncomputable def machine (kind : Fin 4):=Composition.machine (RecoveryBoundedClauseGate.machine kind)
  (RecoveryBoundedClauseReplace.machine (second kind))
def budget (kind : Fin 4) (left right node C : ℕ):=
  RecoveryBoundedClauseNative.budget (RecoveryBoundedClauseGate.nativeKind kind) left right C+1+
    RecoveryBoundedClauseReplace.budget node C
def output (A : Fin 61→List Bool) (kind : Fin 4) (node C : ℕ) (result : List Bool):=
  RecoveryBoundedClauseReplace.output (RecoveryBoundedClauseGate.output A result) (second kind) node C

theorem node_run (kind : Fin 4) (H : Fin 61→ℕ) (A : Fin 61→List Bool)
    (left right node W C : ℕ) (out : List Bool)
    (hH : ∀ j,H (RecoveryBoundedClauseGate.slots kind j)=PCPPNativeClauseBank.heads out j)
    (hA : ∀ j,A (RecoveryBoundedClauseGate.slots kind j)=RecoveryBoundedUniversalGates.data left right C out j)
    (hR : ∀ j,H (RecoveryBoundedClauseReplace.slots (second kind) j)=0)
    (aR : ∀ j,A (RecoveryBoundedClauseReplace.slots (second kind) j)=RecoveryBoundedClauseReplace.data node left C 0 j)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) (hn : node+1 ≤ C) :
    let result:=out++RecoveryBoundedClauseNative.emitted (RecoveryBoundedClauseGate.nativeKind kind) left right
    ∃ r,runFrom (machine kind) (budget kind left right node C) ⟨(machine kind).start,H,A⟩=some r ∧
      r.steps ≤ budget kind left right node C ∧ r.final.heads=RecoveryBoundedClauseGate.heads H result ∧
      r.final.tapes=output A kind node C result := by
  let result:=out++RecoveryBoundedClauseNative.emitted (RecoveryBoundedClauseGate.nativeKind kind) left right
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedClauseGate.gate_run kind H A left right W C out hH hA hl hr hC
  have hlC : left ≤ C := by nlinarith [Nat.zero_le (W^2)]
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedClauseReplace.replace_run (second kind)
    (RecoveryBoundedClauseGate.heads H result) (RecoveryBoundedClauseGate.output A result) node left C
    (by intro j;have hj:=hR j;fin_cases j <;> fin_cases kind <;> exact hj)
    (by intro j;have hj:=aR j;fin_cases j <;> fin_cases kind <;> exact hj) hlC hn
  have qr' : runFrom (RecoveryBoundedClauseReplace.machine (second kind)) (RecoveryBoundedClauseReplace.budget node C)
      (restart p.final (RecoveryBoundedClauseReplace.machine (second kind)).start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join (RecoveryBoundedClauseGate.machine kind)
    (RecoveryBoundedClauseReplace.machine (second kind)) _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps ≤ budget kind left right node C
  unfold budget
  omega

theorem budget_bound (kind : Fin 4) (left right node W C : ℕ)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    budget kind left right node C ≤ 10*C+4*node+34 := by
  have h:=RecoveryBoundedClauseNative.budget_bound (RecoveryBoundedClauseGate.nativeKind kind) left right W C hl hr hC
  unfold budget RecoveryBoundedClauseReplace.budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralNode
