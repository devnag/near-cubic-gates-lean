import Proof.Amplification.RecoveryBoundedNativeFoldLayout

/-! Emit the original AND/OR node from the actually popped reference and
current accumulator. False-only address storage remains allocated and paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
open LocalBitMultitape RepairRepresentation PCPPNativeClauseBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def referencePadding (C : ℕ) (i : Fin 29) := if i=1 then C else 0
private theorem padded_old (ref acc C : ℕ) (out : List Bool) :
    (fun i=>ZeroPadding.pad (referencePadding C i) (PCPPNativeClauseBank.data (values ref acc) C out i))=
      oldData ref acc C out := by
  funext i
  by_cases hi : i=1
  · subst i; rfl
  · simp only [referencePadding,oldData,hi,ite_false,ZeroPadding.pad_zero]

def nodeBudget (conjunction : Bool) (ref acc C : ℕ) :=
  PCPPNativeClauseBank.nodeBudget (tag conjunction) 0 1 0 3 (values ref acc) C

theorem node_run (conjunction : Bool) (ref acc C live : ℕ) (flag : Bool) (out stack framed : List Bool)
    (hr : PCPPNativeSumAppend.budget 0 ref+1 ≤ C)
    (ha : PCPPNativeSumAppend.budget 0 acc+1 ≤ C) :
    ∃ r, runFrom (second conjunction) (nodeBudget conjunction ref acc C)
      ⟨(second conjunction).start,heads out live,data ref acc C flag out stack framed⟩=some r ∧
      r.steps ≤ nodeBudget conjunction ref acc C ∧
      r.final.heads=heads (out++emitted conjunction ref acc) live ∧
      r.final.tapes=data ref acc C flag (out++emitted conjunction ref acc) stack framed := by
  obtain ⟨a,har,as,ah,atapes⟩:=PCPPNativeClauseBank.node_run (tag conjunction) 0 1 0 3
    (by decide) (by decide) (values ref acc) C out hr ha
  have hb : nodeBits (tag conjunction) 0 1 0 3 (values ref acc)=emitted conjunction ref acc := by
    simp [nodeBits,emitted,values]
  rw [hb] at ah atapes
  obtain ⟨b,hbr,bf,bs,_⟩:=ZeroPadding.run_config
    (nodeMachine (tag conjunction) 0 1 0 3) (referencePadding C) _ _ a har
  have bin : ZeroPadding.config (referencePadding C)
      (PCPPNativeClauseBank.entry (nodeMachine (tag conjunction) 0 1 0 3) (values ref acc) C out)=
      (⟨(nodeMachine (tag conjunction) 0 1 0 3).start,PCPPNativeClauseBank.heads out,oldData ref acc C out⟩ : Configuration 29 _) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact padded_old ref acc C out
  rw [bin] at hbr
  have bh : b.final.heads=PCPPNativeClauseBank.heads (out++emitted conjunction ref acc) := by
    rw [bf]; exact ah
  have bt : b.final.tapes=oldData ref acc C (out++emitted conjunction ref acc) := by
    rw [bf]
    change (fun i=>ZeroPadding.pad (referencePadding C i) (a.final.tapes i))=_
    rw [atapes]
    exact padded_old _ _ _ _
  let extraH : Fin 5→ℕ:=![0,0,live,0,0]
  let extraT : Fin 5→List Bool:=![[flag],ZeroPadding.pad C framed,stack,List.replicate C false,List.replicate C false]
  have full:=TapeEmbedding.run_embed (nodeMachine (tag conjunction) 0 1 0 3) extraH extraT _ _ b hbr
  refine ⟨TapeEmbedding.receipt extraH extraT b,full,bs.le.trans as,?_,?_⟩
  · change (Fin.addCases (m:=29) (n:=5) (motive:=fun _=>ℕ) b.final.heads extraH)=_
    rw [bh]; rfl
  · change (Fin.addCases (m:=29) (n:=5) (motive:=fun _=>List Bool) b.final.tapes extraT)=_
    rw [bt]; rfl

theorem node_budget_bound (conjunction : Bool) (ref acc C : ℕ)
    (hr : PCPPNativeSumAppend.budget 0 ref+1 ≤ C)
    (ha : PCPPNativeSumAppend.budget 0 acc+1 ≤ C) : nodeBudget conjunction ref acc C ≤ 8*C+32 := by
  have htag : (natWord (tag conjunction)).length ≤ 9 := by cases conjunction <;> decide
  unfold nodeBudget PCPPNativeClauseBank.nodeBudget PCPPNativeSumReusable.budget
  simp only [values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
