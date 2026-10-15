import Proof.Amplification.RecoveryTseitinNativePrefix
import Proof.Amplification.RecoveryTseitinNativeErase
import Proof.Amplification.RecoveryTseitinNativeEntry

/-! The actual erase and sentinel transition join a physical raw-input
prefix to its original formula consumer, over abstract state and capacity
carriers so no unary backing is normalized inside the kernel. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def formulaSlots (i : Fin 1342) : Fin 1370:=i.castAdd 28
theorem formula_injective : Function.Injective formulaSlots := by
  intro i j he
  have hv:=congrArg Fin.val he
  exact Fin.ext hv
noncomputable def allocatedMachine {s : Nat} (p : Machine 1370 s):=Composition.machine p coldEraseProgram
noncomputable def readyMachine {s : Nat} (p : Machine 1370 s):=Composition.machine (allocatedMachine p) enterMachine
noncomputable def wholeMachine {s u : Nat} (p : Machine 1370 s) (q : Machine 1342 u):=
  Composition.machine (readyMachine p) (RecoveryFocus.machine formulaSlots q)
def wholeBudget (f g cap : Nat) := (f+1+(2*cap+4))+1+1+1+g

theorem whole_core {s u : Nat} (p : Machine 1370 s) (q : Machine 1342 u)
    (f g cap n count output : Nat) (word result : List Bool)
    (hp : ∃ a,run p f (input n count output word)=some a ∧
      a.final.tapes 1333=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n) ∧
      a.final.heads 1333=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)).length ∧
      (∀ i,i≠1333 → a.final.heads i=0) ∧
      (∀ i,retained i → a.final.tapes i=workspaceData cap n count output word i) ∧
      (∀ j,(a.final.tapes ((Reuse.scratch j).castAdd 34)).length ≤ cap) ∧ a.steps ≤ f)
    (hq : ∃ b,runFrom q g
      ⟨q.start,
        (Formula.state 0 n 0 0 word (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n))
          cap count output).heads,
        (Formula.state 0 n 0 0 word (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n))
          cap count output).tapes⟩=some b ∧
      b.final.heads 1333=result.length ∧ b.final.tapes 1333=result ∧ b.steps ≤ g) : ∃ r,
    run (wholeMachine p q) (wholeBudget f g cap) (input n count output word)=some r ∧
      r.final.heads 1333=result.length ∧ r.final.tapes 1333=result ∧ r.steps ≤ wholeBudget f g cap := by
  let out:=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)
  obtain ⟨a,ha,ao,ah,az,atapes,abound,asteps⟩:=hp
  obtain ⟨b,hb,bheads,btapes,bextra,bsteps⟩:=cold_erase_run cap n count output word
    a.final.heads a.final.tapes ao az atapes abound
  obtain ⟨ab,hab,abh,abt,abs⟩:=join_two p coldEraseProgram _ _ _ a b ha hb
  obtain ⟨c,hc,ch,ct,cs⟩:=enter_run ab.final.heads ab.final.tapes
  obtain ⟨ready,hready,rh,rt,rs⟩:=join_two (allocatedMachine p) enterMachine _ _ _ ab c hab hc
  have hheads : ready.final.heads=enterHeads a.final.heads :=
    rh.trans (ch.trans (congrArg enterHeads (abh.trans bheads)))
  have htapes : ready.final.tapes=b.final.tapes := rt.trans (ct.trans abt)
  have vh (i : Fin 1342) : ready.final.heads (formulaSlots i)=
      (Formula.state 0 n 0 0 word out cap count output).heads i :=
    (congrFun hheads (formulaSlots i)).trans (entry_heads cap n count output word out a.final.heads ah az i)
  have vt (i : Fin 1342) : ready.final.tapes (formulaSlots i)=
      (Formula.state 0 n 0 0 word out cap count output).tapes i :=
    (congrFun htapes (formulaSlots i)).trans (entry_tapes cap n count output word out b.final.tapes btapes bextra i)
  obtain ⟨last,hlast,lh,lt,ls⟩:=hq
  obtain ⟨d,hd,_dc,ds,dh,dt,_dk⟩:=RecoveryFocus.dock formulaSlots formula_injective q _
    ready.final.heads ready.final.tapes
    ⟨q.start,(Formula.state 0 n 0 0 word out cap count output).heads,
      (Formula.state 0 n 0 0 word out cap count output).tapes⟩ vh vt last hlast
  obtain ⟨r,hr,rfh,rft,rsteps⟩:=join_two (readyMachine p) (RecoveryFocus.machine formulaSlots q)
    _ _ _ ready d hready hd
  refine ⟨r,hr,(congrFun rfh 1333).trans ((dh 1333).trans lh),
    (congrFun rft 1333).trans ((dt 1333).trans lt),?_⟩
  rw [rsteps,rs,abs,cs,ds]
  unfold wholeBudget
  omega

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
