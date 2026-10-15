import Proof.CaseAnalysis.RowsTupleSeekTermRun
import Proof.CaseAnalysis.WitnessPaddedReset
import Proof.Amplification.RecoveryScratchErase

/-! The parser's thirteen private tapes are recycled. The three family
cursors and all four append outputs remain live through selective reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateTapes (i : Fin 20) : Bool := decide (0 < i.val ∧ i.val < 14)
def localHeads (pos : Fin 3→ℕ) (out : Fin 4→List Bool) : Fin 20→ℕ :=
  ![pos 0,0,0,0,0,0,0,0,0,0,0,0,0,0,(out 0).length,pos 1,(out 1).length,pos 2,(out 2).length,(out 3).length]
def localData (src : Fin 3→List Bool) (out : Fin 4→List Bool) : Fin 20→List Bool :=
  ![src 0,[],[],[],[],[],[],[],[],[],[],[],[],[],out 0,src 1,out 1,src 2,out 2,out 3]

theorem raw_entry (keep : Bool) (src : Fin 3→List Bool) (pos : Fin 3→ℕ) (out : Fin 4→List Bool) :
    rawEntry keep src pos out=⟨(rawMachine keep).start,localHeads pos out,localData src out⟩ := by
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [rawEntry,rawInput,headerEntry,headerInput,PCPPQueryNatural.entry,
      TapeEmbedding.config,rawExtraHeads,headerExtraHeads,localHeads,Fin.addCases]
  · funext i;fin_cases i <;> simp [rawEntry,rawInput,headerEntry,headerInput,PCPPQueryNatural.entry,
      TapeEmbedding.config,rawExtraData,headerExtraData,localData,Fin.addCases]

def reuseHeads (H : Fin 20→ℕ) : Fin 23→ℕ :=
  Fin.addCases (m:=21) (n:=2) (motive:=fun _=>ℕ)
    (Fin.addCases (m:=20) (n:=1) (motive:=fun _=>ℕ) H (fun _=>0)) (fun _=>0)
def cleanData (C : ℕ) (A : Fin 20→List Bool) := fun i=>if privateTapes i then List.replicate C false else A i
def reuseData (C : ℕ) (A : Fin 20→List Bool) : Fin 23→List Bool :=
  Fin.addCases (m:=21) (n:=2) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=20) (n:=1) (motive:=fun _=>List Bool) (cleanData C A) (fun _=>List.replicate C false))
    ![List.replicate C true,List.replicate (C+1) false]
def eraseSlots : Fin 15→Fin 23 := Fin.addCases (m:=13) (n:=2) (motive:=fun _=>Fin 23)
  (fun i : Fin 13=>⟨i.val+1,by omega⟩) (fun i : Fin 2=>⟨21+i.val,by omega⟩)
noncomputable def reuseFirst {s : ℕ} (p : Machine 20 s) := TapeEmbedding.machine 2 (MaskedReset.machine p privateTapes)
noncomputable def reuseLast := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 13)
noncomputable def recycle {s : ℕ} (p : Machine 20 s) := Composition.machine (reuseFirst p) reuseLast
noncomputable def reusableMachine (keep : Bool) := recycle (rawMachine keep)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
