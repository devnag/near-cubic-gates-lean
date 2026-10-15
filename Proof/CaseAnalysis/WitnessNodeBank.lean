import Proof.CaseAnalysis.WitnessNodeMetadata
import Proof.CaseAnalysis.WitnessInputPower

/-! The actual hierarchy arity bits and an input-derived width are loaded
into the allocated node bank. Scalar normalization and every allocation,
copy and join are executed by the retained finite machines. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeColdBank
open LocalBitMultitape RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankSlots (i : Fin 759) : Fin 766:=i.castAdd 7
def loopSlots (i : Fin 755) : Fin 766:=(i.castAdd 4).castAdd 7
def metadataSlots : Fin 11→Fin 766:=
  ![756,759,757,760,761,762,758,763,764,755,765]
def input (cap w : ℕ) (bits source : List Bool) (flag : Bool) : Fin 766→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (759+7)=>List Bool)
    (NodeBank.input cap ![[],List.replicate w true,[],[]] source flag)
    ![frame bits,[],[],[],[],[],[]]
noncomputable def metadata:=RecoveryFocus.machine metadataSlots NodeMetadata.machine
noncomputable def bank:=RecoveryFocus.machine bankSlots NodeBank.machine
noncomputable def machine:=Composition.machine metadata bank

theorem bank_injective : Function.Injective bankSlots:=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 766=>i.val) h)
theorem metadata_injective : Function.Injective metadataSlots:=by decide
theorem metadata_core (i : Fin 755) : ∀ j,metadataSlots j≠loopSlots i:=by
  intro j h
  have hv:=congrArg Fin.val h
  fin_cases j <;> simp [metadataSlots,loopSlots] at hv <;> omega
theorem metadata_field (j : Fin 4) :
    metadataSlots (NodeMetadata.fieldSlots j)=bankSlots (NodeBank.field j):=by
  fin_cases j <;> rfl

theorem metadata_input (cap w : ℕ) (bits source : List Bool) (flag : Bool) :
    ∀ i,input cap w bits source flag (metadataSlots i)=NodeMetadata.input w bits i:=by
  intro i
  fin_cases i <;> simp [input,metadataSlots,NodeBank.input,NodeMetadata.input,Fin.addCases]

theorem bank_input (cap w : ℕ) (bits source : List Bool) (flag : Bool) (out : Fin 11→List Bool)
    (hf : ∀ j,out (NodeMetadata.fieldSlots j)=NodeGuard.shared w (binary w (value bits)) (binary w 0) j) :
    ∀ i,install metadataSlots (input cap w bits source flag) out (bankSlots i)=
      NodeBank.input cap (NodeGuard.shared w (binary w (value bits)) (binary w 0)) source flag i:=by
  intro i
  refine Fin.addCases (m:=755) (n:=4) ?_ ?_ i
  · intro j
    change install metadataSlots _ out (loopSlots j)=_
    rw [install_other _ _ _ _ (metadata_core j)]
    simp only [input,loopSlots,Fin.addCases_left,NodeBank.input]
  · intro j
    change install metadataSlots _ out (bankSlots (NodeBank.field j))=_
    rw [←metadata_field,install_slot _ metadata_injective,hf]
    simp only [NodeBank.input,Fin.addCases_right]

theorem bank_run (cap w : ℕ) (bits source : List Bool) (flag : Bool)
    (hb : bits.length≤w) (hcap : 1≤cap)
    (hc : ∀ j,(NodeGuard.shared w (binary w (value bits)) (binary w 0) j).length≤cap) :
    ∃ out,ClockJoin.ReadyRun machine (10*cap+8*w+43) (input cap w bits source flag) out ∧
      (∀ i,out (loopSlots i)=
        NodeRound.data cap w (binary w (value bits)) (binary w 0) [] [] source flag i):=by
  obtain ⟨m,hm,hf⟩:=NodeMetadata.metadata_run w bits hb
  have h0:=hm.focus metadataSlots metadata_injective (input cap w bits source flag)
    (metadata_input cap w bits source flag)
  have h1:=(NodeBank.bank_ready cap _ source flag hc).focus bankSlots bank_injective
    (install metadataSlots (input cap w bits source flag) m) (bank_input cap w bits source flag m hf)
  have h:=ClockJoin.join metadata bank _ _ _ _ _ h0 h1
  have he:8*w+18+1+(10*cap+24)=10*cap+8*w+43:=by omega
  rw [he] at h
  refine ⟨_,h,?_⟩
  intro i
  change install bankSlots _ _ (bankSlots (i.castAdd 4))=_
  rw [install_slot _ bank_injective]
  exact NodeBank.bank_data cap w _ _ source flag hcap i

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeColdBank
