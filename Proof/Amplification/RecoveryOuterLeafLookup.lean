import Proof.Amplification.RecoveryOuterLeafState

/-! Actual reused inner-table lookup while preserving the outer structural
workspace, prior-prefix bank and streaming source cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lookup_focus (x : State) (bank : RecoveryRowLookupStream.Data) (cost : Nat)
    (h : ReadyRun RecoveryRowLookupTable.rewindMachine cost x.extra
      (RecoveryRowLookupTable.readyTapes bank x.total x.capacity)) :
    ∃ r,runFrom lookupMachine cost (x.cfg lookupMachine.start)=some r ∧
      r.final=(setBank x bank).cfg r.final.control ∧ r.steps=cost := by
  obtain ⟨r,hr,hh,ht,hs⟩ := h.focus_at slots slots_injective x.heads x.tapes
    (by intro j; simp only [State.tapes,slots,Fin.addCases_right])
    (by intro j; simp only [State.heads,slots,Fin.addCases_right])
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht.trans (install_bank x bank)

theorem lookup_run (x : State) (word outerBits innerBits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hp : readMany (readRow x.inner.row.width) x.total innerBits=some (rows,rest)) :
    ∃ r,runFrom lookupMachine (time x) (x.cfg lookupMachine.start)=some r ∧
      r.final=(output x innerBits).cfg r.final.control ∧ r.steps ≤ time x ∧
      (output x innerBits).Valid word outerBits innerBits ∧
      (output x innerBits).inner.found=rows.any (fun row=>decide (value x.inner.key=row.code)) := by
  have ha : (readMany (readRow x.inner.row.width) x.total innerBits).isSome=true := by rw [hp]; rfl
  have hi : RecoveryRowLookupTable.Inv x.inner.row.width ⟨x.inner,innerBits⟩ :=
    ⟨hx.2.2.1.1,rfl,hx.2.2.1.2.2⟩
  obtain ⟨base,hrun,hbound,hheads,_,hout⟩ := RecoveryRowLookupTable.ready_run x.inner.row.width
    x.total x.capacity x.inner innerBits hi hx.2.2.2.1 hx.2.2.2.2.2.2
  have hready := ready_of_run RecoveryRowLookupTable.rewindMachine (time x) x.extra base hrun hheads
  rw [hout ha] at hready
  obtain ⟨r,hr,hf,hs⟩ := lookup_focus x (RecoveryRowLookupTable.output x.total x.inner innerBits) base.steps hready
  change base.steps ≤ time x at hbound
  have hm := runFrom_moreFuel lookupMachine base.steps (time x-base.steps) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨r,hm,hf,hs.le.trans hbound,output_valid x word outerBits innerBits hx ha,?_⟩
  exact (RecoveryRowLookupTable.output_lookup x.total x.inner innerBits rows rest hp).1

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
