import Proof.CaseAnalysis.WitnessDAGOutput

/-! The five physical oracle tests give exactly the existing typed decoder.
One finite ordinary transition records their conjunction for the native
source call; malformed encodings cannot pass through a weaker syntax test. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGVerdict
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted (flags : Fin 5→Bool):=flags 0 && flags 1 && flags 2 && flags 3 && !(flags 4)
def machine : Machine 6 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun _ bits=>some ⟨1,fun i=>if i=5 then some (accepted (fun j=>bits (j.castAdd 1))) else none,
    fun _=>.stay⟩
def input (fields : Fin 5→List Bool) : Fin 6→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (5+1)=>List Bool) fields (fun _=>[])
def output (fields : Fin 5→List Bool) : Fin 6→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (5+1)=>List Bool) fields
    (fun _=>[accepted (fun i=>readTapeBit (fields i) 0)])

theorem verdict_run (fields : Fin 5→List Bool) :
    ClockJoin.ReadyRun machine 1 (input fields) (output fields):=by
  have hs:step machine (initialConfiguration machine (input fields))=some ⟨1,fun _=>0,output fields⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m:=5) (n:=1) ?_ ?_ i
      · intro j
        have hn:j.castAdd 1≠(5 : Fin 6):=by apply Fin.ne_of_val_ne;simp;omega
        simp [applyAction,machine,hn,initialConfiguration,input,output]
      · intro j
        have hj:j=0:=Fin.eq_zero j
        subst j
        simp [applyAction,machine,initialConfiguration,input,output,Configuration.scanned]
        change writeTapeBit [] 0 _=[_]
        rfl
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht.le⟩

theorem accepted_iff (n : ℕ) (bits : List Bool) (flags : Fin 5→Bool)
    (hh : flags 0=true ↔ PCPPNativeCanonical.headerValid bits)
    (hl : flags 1=true ↔ ∃ values,CanonicalBinary.encodeBalancedList values=value (PCPPNativeCanonical.nodeWord bits))
    (hn : flags 2=true ↔ (CanonicalBinary.decodeNat (value (PCPPNativeCanonical.outputWord bits))).isSome)
    (hv : flags 3=true ↔ ∀ i : Fin (DAGChecks.words bits).length,NodeMeaning.valid n i.val ((DAGChecks.words bits).get i))
    (ho : flags 4=true ↔ (DAGChecks.words bits).length≤DAGChecks.output bits) :
    accepted flags=true ↔ (CanonicalWitnessCodec.decodeBooleanCircuit n (value bits)).isSome:=by
  have hn':flags 2=true ↔ BitFields.passes (PCPPNativeCanonical.outputWord bits):=
    hn.trans (BitFields.passes_iff _).symm
  have hnot:(!(flags 4))=true ↔ ¬flags 4=true:=by cases flags 4 <;> decide
  apply Iff.trans ?_ (DAGChecks.checks_iff n bits)
  simp only [accepted,Bool.and_eq_true,hnot,hh,hl,hn',hv,ho,Nat.not_le,DAGChecks.checks,and_assoc]

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGVerdict
