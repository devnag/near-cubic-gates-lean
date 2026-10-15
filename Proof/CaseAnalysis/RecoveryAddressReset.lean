import Proof.CaseAnalysis.RecoveryAddressPaddedRun

/-! Pay to rewind the actual address source after the original expression.
The graph append cursor and all allocated workspaces remain reusable. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine RecoveryBoundedAddressFinish.machine selected
def resetBudget (count W : ℕ):=2*RecoveryBoundedAddressFinish.budget count W+2
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1)) (start limit W D L base count : ℕ)
    (out source : List Bool):=
  ZeroPadding.config (Rewind.Workspace.capacities 41 L)
    (Rewind.recording (ZeroPadding.config (caps (capacity W))
      (RecoveryBoundedAddressFinish.entry (n:=n) row start limit W D base count out [] source [])) 0)

theorem entry_heads {n bound : ℕ} (row : Fin (bound+1)) (start limit W D L base count : ℕ)
    (out source : List Bool) :
    (entry (n:=n) row start limit W D L base count out source).heads=finalHeads out := by
  rfl

theorem entry_tapes {n bound : ℕ} (row : Fin (bound+1)) (start limit W D L base count : ℕ)
    (out source : List Bool) :
    (entry (n:=n) row start limit W D L base count out source).tapes=
      finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base (capacity W) D 0 limit count L out source := by
  have hOld : (RecoveryBoundedAddressFinish.entry (n:=n) row start limit W D base count out [] source []).tapes=
      RecoveryBoundedAddressFinish.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        base (capacity W) D 0 limit count out source [] := by rfl
  change (fun i=>ZeroPadding.pad (Rewind.Workspace.capacities 41 L i)
    (Fin.addCases (m:=41) (n:=1) (motive:=fun _=>List Bool)
      (fun j=>ZeroPadding.pad (caps (capacity W) j)
        ((RecoveryBoundedAddressFinish.entry (n:=n) row start limit W D base count out [] source []).tapes j))
      (fun _=>[]) i))=_
  rw [hOld]
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Rewind.Workspace.capacities,Fin.addCases_left,finalData]
    exact ZeroPadding.pad_zero _
  · simp only [Rewind.Workspace.capacities,Fin.addCases_right,finalData]
    rfl

theorem reset_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D L : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (bits out tail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+bits.length*(3*limit+1)+3*limit ≤ W)
    (hg : (compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))).final.nodes.length ≤ W)
    (hc : bits.length ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let compiled:=compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (resetBudget bits.length W)
      (entry (n:=n) row start limit W D L b.nodes.length bits.length out (bits++tail))=some r ∧
      r.steps ≤ resetBudget bits.length W ∧ r.final.heads=finalHeads result ∧
      r.final.tapes=finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        compiled.output.val (capacity W) D bits.length limit bits.length L result (bits++tail) := by
  obtain ⟨p,hpRun,ps,ph,pt⟩:=padded_run b row start limit W D hblock bits out tail hi hp hg hc hD
  have hstart : ∀ i,selected i=true →
      (ZeroPadding.config (caps (capacity W)) (RecoveryBoundedAddressFinish.entry (n:=n)
        row start limit W D b.nodes.length bits.length out [] (bits++tail) [])).heads i=0 := by
    intro i hs
    have he : i=37 := by simpa only [selected,decide_eq_true_eq] using hs
    subst i
    rfl
  have hcap : p.steps ≤ L:=ps.trans ((RecoveryBoundedAddressFinish.budget_log bits.length W hc).trans hL)
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.workspace_run RecoveryBoundedAddressFinish.machine selected _ L _ p hpRun hstart hcap
  have hb : 2*p.steps+2 ≤ resetBudget bits.length W := by unfold resetBudget;omega
  have more:=runFrom_moreFuel machine _ (resetBudget bits.length W-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_⟩
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config]
    rw [ph,reset_heads]
    rfl
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config]
    rw [pt]
    rfl

theorem reset_budget_quartic (count W : ℕ) (hc : count ≤ W) :
    resetBudget count W ≤ 268435802*(W+1)^4:=
  RecoveryBoundedAddressFinish.reset_budget_quartic count W hc

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressReuse
