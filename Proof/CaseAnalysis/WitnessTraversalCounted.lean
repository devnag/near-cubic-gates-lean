import Proof.CaseAnalysis.CloseoutWitnessTraversalCold
import Proof.PCP.ProjectionNormalizationCounter

/-! The shared DFS feeds the existing serializer's counted-stream ABI.
The raw unary count is converted by the already accepted unit product. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TraversalCounted
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readMachine := TapeEmbedding.machine 3 (Rewind.machine TraversalCold.machine)
def countSlots : Fin 4→Fin 40 := ![28,37,38,39]
theorem count_injective : Function.Injective countSlots := by decide
noncomputable def countMachine := RecoveryFocus.machine countSlots Counter.machine
noncomputable def prefixMachine := Composition.machine readMachine countMachine
def position : Machine 40 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i=38 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine prefixMachine position
def input (bits : List Bool) : Fin 40→List Bool :=
  Fin.addCases (m:=37) (n:=3) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool) (TraversalCold.input bits) (fun _=>[]))
    (fun _=>[])
def count (bits : List Bool) := (tree (RadixSemantics.value bits)).atoms.length
def budget (bits : List Bool) := 2*TraversalCold.budget bits+Counter.budget (count bits)+5

theorem counted_run (bits : List Bool) :
    ∃ r,run machine (budget bits) (input bits)=some r ∧ r.steps≤budget bits ∧
      r.final.tapes 27=atomStream bits.length (tree (RadixSemantics.value bits)).atoms ∧
      r.final.tapes 38=CompareMachine.word (count bits) ∧
      r.final.heads 27=0 ∧ r.final.heads 38=1 := by
  obtain ⟨raw,hr,hsize,hout,hcount,_⟩:=TraversalCold.cold_run bits
  obtain ⟨restored,hrestored,rt,rh,rs,_⟩:=Rewind.reset_run TraversalCold.machine _ _ raw hr
  have ready:ReadyRun (Rewind.machine TraversalCold.machine) (2*raw.steps+2)
      (Fin.addCases (TraversalCold.input bits) (fun _ : Fin 1=>[])) restored.final.tapes:=
    ⟨restored,hrestored,rfl,rh,rs⟩
  have lifted:=ready.embed (fun _ : Fin 3=>[])
  let ambient : Fin 40→List Bool:=Fin.addCases (m:=37) (n:=3) (motive:=fun _=>List Bool)
    restored.final.tapes (fun _ : Fin 3=>[])
  have hs:ambient 28=List.replicate (count bits) true:=(rt 28).trans hcount
  obtain ⟨c,hc,c0,c2,ch,cs⟩:=Counter.counter_run (count bits)
  have cr:ReadyRun Counter.machine (Counter.budget (count bits)) (Counter.input (count bits)) c.final.tapes:=
    ⟨c,hc,rfl,ch,cs⟩
  have hcFocused:=cr.focus countSlots count_injective ambient (by
    intro j;fin_cases j
    · exact hs
    · rfl
    · rfl
    · rfl)
  let middle:=install countSlots ambient c.final.tapes
  have hp:ClockJoin.ReadyRun prefixMachine
      ((2*raw.steps+2)+1+Counter.budget (count bits)) (input bits) middle:=
    ClockJoin.join readMachine countMachine _ _ _ _ _
      (by obtain ⟨r,hr,rt,rh,rs⟩:=lifted;exact ⟨r,hr,rt,rh,rs.le⟩)
      (by obtain ⟨r,hr,rt,rh,rs⟩:=hcFocused;exact ⟨r,hr,rt,rh,rs.le⟩)
  obtain ⟨first,hfirst,ft,fh,fs⟩:=hp
  let last : Configuration 40 2:=⟨1,fun i=>if i=38 then 1 else 0,middle⟩
  have hstep:step position (initialConfiguration position middle)=some last:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;by_cases hi:i=38 <;> simp [applyAction,position,initialConfiguration,last,hi,HeadMove.apply]
    · rfl
  obtain ⟨final,hfinal,ff,ffs⟩:=(Timed.single (by rfl) hstep).run (by rfl)
  have he:Composition.restart first.final position.start=initialConfiguration position middle:=by
    apply configuration_ext
    · rfl
    · exact funext fh
    · exact ft
  rw [←he] at hfinal
  have joined:=Composition.run_join prefixMachine position _ _ _ first final hfirst hfinal
  have hb:((2*raw.steps+2)+1+Counter.budget (count bits))+1+1≤budget bits:=by
    unfold budget;omega
  have more:=run_moreFuel machine _ (budget bits-
      (((2*raw.steps+2)+1+Counter.budget (count bits))+1+1)) (input bits)
    (Composition.joinedReceipt first final) joined
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨Composition.joinedReceipt first final,more,?_,?_,?_,?_,?_⟩
  · change first.steps+1+final.steps≤_
    rw [ffs]
    omega
  · change final.final.tapes 27=_
    rw [ff]
    change install countSlots ambient c.final.tapes 27=_
    rw [install_other countSlots _ _ _ (by intro j;fin_cases j <;> decide)]
    exact (rt 27).trans hout
  · change final.final.tapes 38=_
    rw [ff]
    exact (install_slot countSlots count_injective ambient c.final.tapes 2).trans c2
  · change final.final.heads 27=0
    rw [ff];rfl
  · change final.final.heads 38=1
    rw [ff];rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.TraversalCounted
