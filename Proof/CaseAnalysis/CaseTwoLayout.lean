import Proof.CaseAnalysis.CaseTwoNativeConverter
import Proof.CaseAnalysis.CaseTwoFits
import Proof.Amplification.RecoveryScratchErase
import Proof.CaseAnalysis.RowsMetadataCopy

/-! The five approved input ports remain the only cold inputs. Every
converter cell belongs to an explicit allocation or charged input copy. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots (j : Fin 57) : Fin 135:=if j=0 then 3 else if j=1 then 4 else ⟨j.val+3,by omega⟩
def nativeSlots (j : Fin 74) : Fin 135:=if j=23 then 17 else if j=32 then 3 else ⟨j.val+60,by omega⟩
def smallWork (j : Fin 25) : Fin 135:=if j.val<23 then ⟨j.val+60,by omega⟩ else if j=23 then 85 else 88
def smallSlots : Fin 27→Fin 135:=Fin.addCases (m:=25) (n:=2) smallWork ![17,84]
def longSlots : Fin 3→Fin 135:=![86,47,134]
def descSlots : Fin 4→Fin 135:=![1,60,17,84]
def tagSlots : Fin 4→Fin 135:=![58,63,17,84]
def fieldSlots : Fin 4→Fin 135:=![32,88,17,84]
theorem scalar_injective : Function.Injective scalarSlots:=by decide
theorem native_injective : Function.Injective nativeSlots:=by decide
theorem small_injective : Function.Injective smallSlots:=by decide

def input (hierarchy description address : List Bool) (R B : ℕ) (i : Fin 135):=
  if i=0 then hierarchy else if i=1 then description else if i=2 then address
  else if i=3 then List.replicate R true else if i=4 then List.replicate B true else []

structure Funded (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool) : Prop where
  hierarchy : A 0=hierarchy
  description : A 1=description
  address : A 2=address
  r_width : A 3=List.replicate R true
  full_bound : A 4=List.replicate B true
  capacity : A 17=List.replicate C true
  field : A 32=List.replicate (R+B+1) true
  long : A 47=List.replicate (16*(C+1)) true
  six : A 58=List.replicate 6 true
  fresh : ∀ i : Fin 135,60 ≤ i.val → A i=[]

def eraseInput (t C : ℕ) : Fin (t+2)→List Bool:=
  Fin.addCases (m:=t+1) (n:=1)
    (Fin.addCases (m:=t) (n:=1) (fun _=>[]) (fun _=>List.replicate C true)) (fun _=>[])
def eraseOutput (t C : ℕ) : Fin (t+2)→List Bool:=
  Fin.addCases (m:=t+1) (n:=1)
    (Fin.addCases (m:=t) (n:=1) (fun _=>List.replicate C false) (fun _=>List.replicate C true))
    (fun _=>List.replicate (C+1) false)
theorem erase_ready (t C : ℕ) : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine t) (2*C+4)
    (eraseInput t C) (eraseOutput t C):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryScratchErase.erase_ready C 0 (fun _ : Fin t=>[]) (by simp)
  refine ⟨r,?_,?_,hh,hs.le⟩
  · simp only [List.replicate_zero] at hr
    exact hr
  · simp only [Nat.zero_max] at ht
    exact ht

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
