import Proof.CaseAnalysis.RecoveryQueryLoad

/-! The original query-list body retains the entire table bank, two paid
initial-index templates, the streaming addresses and the appended outputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQuery
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def blockData (n C : ℕ) (A : Fin 56→List Bool) (i : Fin 56):=
  if i=50 then UnaryTemplate.tape n
  else if i=42∨i=44∨i=46∨i=49∨i=52 then ZeroPadding.pad C (A i) else A i
theorem blockData_eq (n C : ℕ) (A : Fin 56→List Bool) : blockData n C A=RecoveryBoundedQueryTable.data n C A := by
  funext i
  by_cases hi : i=50
  · subst i;rfl
  simp only [blockData,if_neg hi,RecoveryBoundedQueryTable.data,Function.update_of_ne hi,
    RecoveryBoundedTableOutput.paddedData,RecoveryBoundedTableOutput.caps]
  split <;> simp only [ZeroPadding.pad_zero]

def extraHeads (pos : ℕ) (refs : List Bool) : Fin 4→ℕ:=![0,0,pos,refs.length]
def extraData (F : ℕ) (source refs : List Bool) : Fin 4→List Bool:=
  ![List.replicate 6 true,List.replicate (6+F) true,source,refs]
def heads (out : List Bool) (pos : ℕ) (refs : List Bool) : Fin 60→ℕ:=
  Fin.addCases (m:=56) (n:=4) (motive:=fun _=>ℕ) (RecoveryBoundedTableOutput.bankHeads out) (extraHeads pos refs)
def data (index base C D value F prior L : ℕ) (out priorRefs : List Bool)
    (second tag : ℕ) (address : List Bool) (n total : ℕ) (source refs : List Bool) : Fin 60→List Bool:=
  Fin.addCases (m:=56) (n:=4) (motive:=fun _=>List Bool)
    (blockData n C (RecoveryBoundedTableOutput.bankData index base C D value F prior L out priorRefs second tag address n total))
    (extraData F source refs)

theorem load_heads (out pre refs : List Bool) (j : Fin 4) :
    heads out pre.length refs (RecoveryBoundedQueryLoad.slots j)=(![1,pre.length,0,0] : Fin 4→ℕ) j := by
  fin_cases j <;> rfl
theorem load_tapes (base C D F total L : ℕ) (out pre bits tail refs : List Bool) (j : Fin 4) :
    data 6 base C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] bits.length total (pre++bits++tail) refs
      (RecoveryBoundedQueryLoad.slots j)=
      (![UnaryTemplate.tape bits.length,pre++bits++tail,List.replicate C false,List.replicate C false] : Fin 4→List Bool) j := by
  fin_cases j <;> rfl
theorem loaded_heads (out pre bits refs : List Bool) :
    RecoveryBoundedQueryLoad.heads (heads out pre.length refs) (pre.length+bits.length)=
      heads out (pre.length+bits.length) refs := by
  funext i
  fin_cases i <;> rfl
theorem loaded_tapes (base C D F total L : ℕ) (out source bits refs : List Bool) :
    RecoveryBoundedQueryLoad.output (data 6 base C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] bits.length total source refs) C bits=
      data 6 base C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 bits bits.length total source refs := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedQuery
