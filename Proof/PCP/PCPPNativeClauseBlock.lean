import Proof.PCP.PCPPNativeClauseFields
import Proof.PCP.PCPPRequestNodeSchema

/-! Emit exactly the three native DAG nodes implementing one compact clause.
No duplicate NOT/constant node is inserted and no wire is expanded. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseBank
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def nodeMachine (tag : ℕ) (a b c d : Fin 7) :=
  Composition.machine (Composition.machine (literalMachine (natWord tag)) (sumMachine a b)) (sumMachine c d)
def nodeBits (tag : ℕ) (a b c d : Fin 7) (values : Fin 7→ℕ) :=
  natWord tag++natWord (values a+values b)++natWord (values c+values d)
def nodeBudget (tag : ℕ) (a b c d : Fin 7) (values : Fin 7→ℕ) (C : ℕ) :=
  (natWord tag).length+1+PCPPNativeSumReusable.budget (values a) (values b) C+1+
    PCPPNativeSumReusable.budget (values c) (values d) C

theorem node_run (tag : ℕ) (a b c d : Fin 7) (hab : a≠b) (hcd : c≠d)
    (values : Fin 7→ℕ) (C : ℕ) (out : List Bool)
    (hfirst : PCPPNativeSumAppend.budget (values a) (values b)+1 ≤ C)
    (hlast : PCPPNativeSumAppend.budget (values c) (values d)+1 ≤ C) :
    AppendRun (nodeMachine tag a b c d) (nodeBudget tag a b c d values C) values C out
      (nodeBits tag a b c d values) := by
  have hf:=literal_run (natWord tag) values C out
  have hm:=sum_run a b hab values C (out++natWord tag) hfirst
  have h1:=AppendRun.join _ _ _ _ _ _ _ _ _ hf hm
  have hl:=sum_run c d hcd values C (out++(natWord tag++natWord (values a+values b))) hlast
  exact AppendRun.join _ _ _ _ _ _ _ _ _ h1 hl

def values (base accumulator : ℕ) (refs : Fin 3→ℕ) : Fin 7→ℕ :=
  ![0,refs 0,refs 1,refs 2,base,accumulator,1]
noncomputable def machine := Composition.machine
  (Composition.machine (nodeMachine 4 0 1 0 2) (nodeMachine 4 0 4 0 3)) (nodeMachine 3 0 5 6 4)
def emitted (v : Fin 7→ℕ) := nodeBits 4 0 1 0 2 v++nodeBits 4 0 4 0 3 v++nodeBits 3 0 5 6 4 v
def budget (v : Fin 7→ℕ) (C : ℕ) :=
  nodeBudget 4 0 1 0 2 v C+1+nodeBudget 4 0 4 0 3 v C+1+nodeBudget 3 0 5 6 4 v C
def Capacity (v : Fin 7→ℕ) (C : ℕ) : Prop :=
  PCPPNativeSumAppend.budget (v 0) (v 1)+1 ≤ C ∧
  PCPPNativeSumAppend.budget (v 0) (v 2)+1 ≤ C ∧
  PCPPNativeSumAppend.budget (v 0) (v 4)+1 ≤ C ∧
  PCPPNativeSumAppend.budget (v 0) (v 3)+1 ≤ C ∧
  PCPPNativeSumAppend.budget (v 0) (v 5)+1 ≤ C ∧
  PCPPNativeSumAppend.budget (v 6) (v 4)+1 ≤ C

theorem block_run (v : Fin 7→ℕ) (C : ℕ) (out : List Bool) (hC : Capacity v C) :
    AppendRun machine (budget v C) v C out (emitted v) := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩:=hC
  have ha:=node_run 4 0 1 0 2 (by decide) (by decide) v C out h1 h2
  have hb:=node_run 4 0 4 0 3 (by decide) (by decide) v C (out++nodeBits 4 0 1 0 2 v) h3 h4
  have hab:=AppendRun.join _ _ _ _ _ _ _ _ _ ha hb
  have hc:=node_run 3 0 5 6 4 (by decide) (by decide) v C
    (out++(nodeBits 4 0 1 0 2 v++nodeBits 4 0 4 0 3 v)) h5 h6
  exact AppendRun.join _ _ _ _ _ _ _ _ _ hab hc

theorem emitted_nodes (r base accumulator : ℕ) (refs : Fin 3→ℕ) :
    emitted (values base accumulator refs)=
      (PCPPNative.clauseNodes (r:=r) base accumulator refs).flatMap PCPPRequestNodeSchema.native := by
  simp [emitted,nodeBits,values,PCPPNative.clauseNodes,PCPPRequestNodeSchema.native,
    PCPPRequestNodeSchema.fields,List.append_assoc,Nat.add_comm]

theorem budget_bound (v : Fin 7→ℕ) (C : ℕ) (hC : Capacity v C) :
    budget v C ≤ 24*C+57 := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩:=hC
  have h4len : (natWord 4).length=7 := by decide
  have h3len : (natWord 3).length=5 := by decide
  unfold budget nodeBudget PCPPNativeSumReusable.budget
  rw [h4len,h3len]
  omega

end NearCubicWires.RepairOrdinary.PCPPNativeClauseBank
