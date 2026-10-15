import Proof.CaseAnalysis.RecoverySelectorPaddedRun

/-! The whole original selector pays to rewind its actual input-reference
stream, using the separate quartic log. The output graph cursor is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine RecoveryBoundedSelectorFinish.machine selected
def resetBudget (count W : ℕ):=2*RecoveryBoundedSelectorFinish.budget count W+2
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1)) (start limit W D L base count : ℕ)
    (out source : List Bool) :=
  ZeroPadding.config (Rewind.Workspace.capacities 43 L)
    (Rewind.recording (ZeroPadding.config (caps (capacity W))
      (RecoveryBoundedSelectorFinish.entry (n:=n) row start limit W D base count out [] source [])) 0)

theorem entry_heads {n bound : ℕ} (row : Fin (bound+1)) (start limit W D L base count : ℕ)
    (out source : List Bool) :
    (entry (n:=n) row start limit W D L base count out source).heads=finalHeads out := by
  have hOld : (RecoveryBoundedSelectorFinish.entry (n:=n) row start limit W D base count out [] source []).heads=
      heads out [] 0 := forward_heads row start limit W D count (initial base out [] []) source
  change Fin.addCases (m:=43) (n:=1) (motive:=fun _=>ℕ)
    (RecoveryBoundedSelectorFinish.entry (n:=n) row start limit W D base count out [] source []).heads (fun _=>0)=_
  rw [hOld]
  rfl

theorem entry_tapes {n bound : ℕ} (row : Fin (bound+1)) (start limit W D L base count : ℕ)
    (out source : List Bool) :
    (entry (n:=n) row start limit W D L base count out source).tapes=
      finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base (capacity W) D 0 limit count L out source := by
  have hOld : (RecoveryBoundedSelectorFinish.entry (n:=n) row start limit W D base count out [] source []).tapes=
      data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base (capacity W) D 0 limit count out source [] :=
    forward_tapes row start limit W D count (initial base out [] []) source
  change (fun i=>ZeroPadding.pad (Rewind.Workspace.capacities 43 L i)
    (Fin.addCases (m:=43) (n:=1) (motive:=fun _=>List Bool)
      (fun j=>ZeroPadding.pad (caps (capacity W) j)
        ((RecoveryBoundedSelectorFinish.entry (n:=n) row start limit W D base count out [] source []).tapes j))
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
    (wires : List (LiveWire b)) (out tail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hf : b.nodes.length+RecoveryBoundedUniversal.prefixSize
      (fieldItems row start limit hblock 0 (wires.map (fun w=>w.output.val)))+wires.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) (hL : logCapacity W ≤ L) :
    let raw:=wires.map (fun w=>w.output.val)
    let source:=sourceWord raw++tail
    let a:=(initial b.nodes.length out [] []).iterate row start limit hblock raw
    let refs:=RecoveryBoundedUniversal.references b.nodes.length (fieldItems row start limit hblock 0 raw)
    let f:=folded a.position (a.out++falseBits) refs
    ∃ r,runFrom machine (resetBudget wires.length W)
      (entry (n:=n) row start limit W D L b.nodes.length wires.length out source)=some r ∧
      r.steps ≤ resetBudget wires.length W ∧
      r.final.heads=finalHeads f.out ∧
      r.final.tapes=finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        f.acc (capacity W) D wires.length limit wires.length L f.out source := by
  let raw:=wires.map (fun w=>w.output.val)
  let source:=sourceWord raw++tail
  obtain ⟨p,hpRun,ps,ph,pt⟩:=padded_run b row start limit W D hblock wires out tail hi hp hf hc hD
  have hstart : ∀ i,selected i=true →
      (ZeroPadding.config (caps (capacity W)) (RecoveryBoundedSelectorFinish.entry (n:=n)
        row start limit W D b.nodes.length wires.length out [] source [])).heads i=0 := by
    intro i hs
    have he : i=37 := by simpa only [selected,decide_eq_true_eq] using hs
    subst i
    rfl
  have hcap : p.steps ≤ L := ps.trans ((budget_quartic wires.length W hc).trans hL)
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.workspace_run RecoveryBoundedSelectorFinish.machine selected _ L _ p hpRun hstart hcap
  have hb : 2*p.steps+2 ≤ resetBudget wires.length W := by unfold resetBudget; omega
  have more:=runFrom_moreFuel machine _ (resetBudget wires.length W-(2*p.steps+2)) _ r hr
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

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
