import Proof.CaseAnalysis.WitnessTraversalLayout

/-! A fixed ordinary traversal from one framed word and blank workspace.
No prepared capacity, stack, reset tape, or tree is supplied as input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TraversalCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev driverStates := Fintype.card (RecoveryCalls.Control RecoveryEraseDriver.sizes)
abbrev walkStates := Fintype.card (RecoveryCalls.Control PCPPNativeCanonicalWalk.sizes)
def sizes : Fin 4→ℕ := ![driverStates,4,2,walkStates]
noncomputable def walk := RecoveryFocus.machine walkSlots PCPPNativeCanonicalWalk.machine
noncomputable def programs : (j : Fin 4)→Machine 36 (sizes j)
  | ⟨0,_⟩=>driver
  | ⟨1,_⟩=>erase
  | ⟨2,_⟩=>boot
  | ⟨3,_⟩=>walk
  | ⟨n+4,h⟩=>False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 36→Bool) : Option (Fin 4) :=
  if j.val=0 then some 1 else if j.val=1 then some 2 else if j.val=2 then some 3 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def time (bits : List Bool) := RecoveryEraseDriver.time bits+
  2*RecoveryReusableUnpair.capacity bits+traversalBudget bits.length+9
def budget (bits : List Bool) := 1048576*(bits.length+1)^3

theorem time_bound (bits : List Bool) : time bits≤budget bits := by
  have hd:=RecoveryEraseDriver.time_bound bits
  have hw:=traversalBudget_bound bits.length
  have hp:(bits.length+1)^2≤(bits.length+1)^3:=by
    nlinarith [Nat.zero_le (bits.length*(bits.length+1)^2)]
  have hpos:0<(bits.length+1)^3:=pow_pos (by omega) _
  simp only [RecoveryEraseDriver.budget,RecoveryEraseDriver.coefficient] at hd
  unfold time budget RecoveryReusableUnpair.capacity RecoveryTapeSupport.capacity
  nlinarith

theorem cold_run (bits : List Bool) :
    ∃ r,run machine (budget bits) (input bits)=some r ∧ r.steps≤budget bits ∧
      r.final.tapes 27=atomStream bits.length (tree (value bits)).atoms ∧
      r.final.tapes 28=List.replicate (tree (value bits)).atoms.length true ∧
      r.final.heads 26=1 := by
  have hd:=(driver_ready bits).call sizes programs 0 next 0 1 (by intro q;rfl)
  have he:=(erase_ready bits).call sizes programs 0 next 1 2 (by intro q;rfl)
  obtain ⟨bootReceipt,hboot,bootFinal,_⟩:=initialize_run bits
  obtain ⟨m,hm,hinit⟩:=call_receipt sizes programs 0 next 2 3 1 _ bootReceipt hboot (by rfl)
  rw [bootFinal] at hinit
  obtain ⟨y,base,hy,hbase,_,baseHeads,baseTapes⟩:=traversal_run (state bits) (state_valid bits) rfl
  obtain ⟨actual,hactual,_,_,actualHeads,actualTapes,_⟩:=RecoveryFocus.dock walkSlots walk_injective
    PCPPNativeCanonicalWalk.machine _ (initialized bits).heads (initialized bits).tapes _
    (initialized_heads bits) (initialized_tapes bits) base hbase
  obtain ⟨n,hn,hstop⟩:=stop_receipt sizes programs 0 next 3 (traversalBudget bits.length)
    _ actual hactual (by rfl)
  have whole:=((hd.trans he).trans hinit).trans hstop
  obtain ⟨r,hr,hf,hs⟩:=whole.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb:RecoveryEraseDriver.time bits+1+(2*RecoveryReusableUnpair.capacity bits+4+1)+m+n≤budget bits:=by
    apply (show _≤time bits from ?_).trans (time_bound bits)
    unfold time
    omega
  have more:=run_moreFuel machine _ (budget bits-(RecoveryEraseDriver.time bits+1+
      (2*RecoveryReusableUnpair.capacity bits+4+1)+m+n)) (input bits) r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,hs.le.trans hb,?_,?_,?_⟩
  · rw [hf]
    change actual.final.tapes (walkSlots 27)=_
    rw [actualTapes,baseTapes]
    change y.out=_
    rw [hy.out]
    rfl
  · rw [hf]
    change actual.final.tapes (walkSlots 28)=_
    rw [actualTapes,baseTapes]
    change List.replicate y.count true=_
    rw [hy.count]
    simp only [state,Nat.zero_add]
  · rw [hf]
    change actual.final.heads (walkSlots 26)=1
    rw [actualHeads,baseHeads]
    change y.stack.length=1
    rw [hy.stack]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.TraversalCold
