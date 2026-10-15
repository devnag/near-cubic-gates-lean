import Proof.Amplification.RecoveryRowStructureChildrenState

/-! Complete prior-row lookup call inside the paired-row workspace. The
caller supplies a physically retained table source and checked prefix; the
lookup pays positioning, clearing, every comparison/copy and all rewinds. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankTime (x : Children) := 2*x.total*(RecoveryRowLookupStream.budget x.bank.row.width+3)+12
def bankOutput (x : Children) (bits : List Bool) : Children :=
  {x with bank:=RecoveryRowLookupTable.output x.total x.bank bits}

theorem bank_output_valid (x : Children) (word bits : List Bool) (hx : x.Valid word bits)
    (ha : (readMany (readRow x.bank.row.width) x.total bits).isSome=true) : (bankOutput x bits).Valid word bits := by
  obtain ⟨hv,hp,hw,_,hs⟩ := RecoveryRowLookupTable.output_valid x.base.state.bits.length x.total x.bank bits hx.2.1 ha
  have hsource : x.bank.row.source=frame bits := by
    obtain ⟨pre,ht,hpos⟩ := hx.2.1.2.2
    have he : pre=[] := List.length_eq_zero_iff.mp (hpos.symm.trans hx.2.2.1)
    simpa only [he,List.nil_append] using ht
  have hsaved := RecoveryRowLookupTable.output_saved_length x.total x.bank bits hx.2.2.2.1 ha
  refine ⟨hx.1,⟨hv,hw.trans hx.2.1.2.1,[],?_,hp⟩,hp,?_,hx.2.2.2.2.1,?_⟩
  · exact hs.trans hsource
  · exact hsaved.trans hw.symm
  · change x.total*(RecoveryRowLookupStream.budget (RecoveryRowLookupTable.output x.total x.bank bits).row.width+3)+5≤x.lookupCapacity
    rw [hw]
    exact hx.2.2.2.2.2

theorem bank_focus (x : Children) (bank : RecoveryRowLookupStream.Data) (time : Nat)
    (h : ReadyRun RecoveryRowLookupTable.rewindMachine time
      (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity)
      (RecoveryRowLookupTable.readyTapes bank x.total x.lookupCapacity)) :
    ∃ r,runFrom bankMachine time (x.cfg bankMachine.start)=some r ∧
      r.final=({x with bank:=bank} : Children).cfg r.final.control ∧ r.steps=time := by
  obtain ⟨r,hr,hh,ht,hs⟩ := h.focus_at bankSlots bankSlots_injective x.heads x.tapes
    (by intro j; simp only [Children.tapes,bankSlots,Fin.addCases_right])
    (by intro j; simp only [Children.heads,bankSlots,Fin.addCases_right])
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht.trans (install_bank x bank)

theorem bank_run (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ r,runFrom bankMachine (bankTime x) (x.cfg bankMachine.start)=some r ∧
      r.final=(bankOutput x bits).cfg r.final.control ∧ r.steps≤bankTime x ∧
      (bankOutput x bits).Valid word bits ∧
      (bankOutput x bits).bank.found=rows.any (fun row=>decide (value x.bank.key=row.code)) ∧
      value (bankOutput x bits).bank.saved=RecoveryRowLookupTable.lookupOr rows (value x.bank.key) (value x.bank.saved) := by
  have ha : (readMany (readRow x.bank.row.width) x.total bits).isSome=true := by rw [hp]; rfl
  have hi : RecoveryRowLookupTable.Inv x.bank.row.width ⟨x.bank,bits⟩ :=
    ⟨hx.2.1.1,rfl,hx.2.1.2.2⟩
  obtain ⟨base,hrun,hbound,hheads,_,hout⟩ := RecoveryRowLookupTable.ready_run x.bank.row.width
    x.total x.lookupCapacity x.bank bits hi hx.2.2.1 hx.2.2.2.2.2
  have hready := ready_of_run RecoveryRowLookupTable.rewindMachine (bankTime x)
    (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity) base hrun hheads
  rw [hout ha] at hready
  obtain ⟨r,hr,hf,hs⟩ := bank_focus x (RecoveryRowLookupTable.output x.total x.bank bits) base.steps hready
  change base.steps≤bankTime x at hbound
  have hn : r.steps≤bankTime x := hs.le.trans hbound
  have hm := runFrom_moreFuel bankMachine base.steps (bankTime x-base.steps) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  exact ⟨r,hm,hf,hn,bank_output_valid x word bits hx ha,
    RecoveryRowLookupTable.output_lookup x.total x.bank bits rows rest hp⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
