import Proof.CaseAnalysis.RecoveryAddressNodePorts

/-! Execute the original address expression in the same enclosing bank that
retains both selected children and the actual constant output. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem address_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D total L : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (bits out tail source : List Bool) (secondIndex : ℕ) (savedFirst savedSecond savedConstant : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+bits.length*(3*limit+1)+3*limit ≤ W)
    (hg : (compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))).final.nodes.length ≤ W)
    (hc : bits.length ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
    let compiled:=compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom addressMachine (RecoveryBoundedAddressReuse.resetBudget bits.length W)
      ⟨addressMachine.start,heads out,data index b.nodes.length (capacity W) D 0 limit total L out source secondIndex
        savedFirst savedSecond savedConstant (bits++tail) bits.length⟩=some r ∧
      r.steps ≤ RecoveryBoundedAddressReuse.resetBudget bits.length W ∧ r.final.heads=heads result ∧
      r.final.tapes=data index compiled.output.val (capacity W) D bits.length limit total L result source secondIndex
        savedFirst savedSecond savedConstant (bits++tail) bits.length := by
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
  have hC : 1 ≤ capacity W := by
    unfold capacity
    have h : 0 < (W+1)^2 := by positivity
    omega
  obtain ⟨p,hpRun,ps,ph,pt⟩:=RecoveryBoundedAddressReuse.reset_run b row start limit W D L hblock bits out tail hi hp hg hc hD hL
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock addressSlots address_injective RecoveryBoundedAddressReuse.machine _
    (heads out) (data index b.nodes.length (capacity W) D 0 limit total L out source secondIndex
      savedFirst savedSecond savedConstant (bits++tail) bits.length)
    (RecoveryBoundedAddressReuse.entry (n:=n) row start limit W D L b.nodes.length bits.length out (bits++tail))
    (by intro j;rw [RecoveryBoundedAddressReuse.entry_heads];exact address_heads out j)
    (by intro j;rw [RecoveryBoundedAddressReuse.entry_tapes];exact address_tapes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC j) p hpRun
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hslot : ∃ j,addressSlots j=i
    · obtain ⟨j,rfl⟩:=hslot
      rw [rh j,ph]
      exact (address_heads _ j).symm
    · rw [(rkeep i (by intro j h;exact hslot ⟨j,h⟩)).1]
      have h20 : i≠20:=fun h=>hslot ⟨20,h.symm⟩
      simp only [heads_override,if_neg h20]
  · have he:=HierarchyWidth.install_eq addressSlots address_injective
      (data index b.nodes.length (capacity W) D 0 limit total L out source secondIndex
        savedFirst savedSecond savedConstant (bits++tail) bits.length) r.final.tapes _
      (by intro j;rw [rt j,pt]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    exact address_install _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
