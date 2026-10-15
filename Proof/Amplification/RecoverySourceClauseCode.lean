import Proof.Amplification.RecoverySourceClauseLiterals
import Proof.Amplification.RecoverySourceClauseCells

/-! One original projected 3CNF clause: all three source indices and signs,
address lookups and original literal/list encodings execute. The exact
original clause value is established for the existing payload serializer. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseCode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 160) : Fin 272 := i.castAdd 112
def cellSlots (i : Fin 112) : Fin 272 :=
  if h : i.val<3 then nativeSlots (RecoverySourceClauseLiterals.bank ⟨i.val,h⟩ 44)
  else ⟨160+i.val,by have hi:=i.isLt; omega⟩
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 272=>i.val) h)
theorem cell_injective : Function.Injective cellSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h; have ha:=a.isLt; have hb:=b.isLt
  dsimp only [cellSlots,nativeSlots,RecoverySourceClauseLiterals.bank] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (codes : Fin 3→List Bool) (source : List Bool) (i : Fin 272) :=
  if h : i.val<160 then RecoverySourceClauseLiterals.input codes source ⟨i.val,h⟩ else []
noncomputable def literalMachine := RecoveryFocus.machine nativeSlots RecoverySourceClauseLiterals.machine
noncomputable def cellMachine := RecoveryFocus.machine cellSlots RecoverySourceClauseCells.machine
noncomputable def machine := Composition.machine literalMachine cellMachine

def words {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) :=
  fun i=>RecoverySourceLiteralMeaning.word pcp x randomness (clause i)
def word {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) :=
  RecoverySourceClauseCells.word (words pcp x randomness clause)
def budget {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) :=
  3*RecoverySourceLiteralMeaning.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)+2+1+
    RecoverySourceClauseCells.budget (words pcp x randomness clause)

theorem clause_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) : ∃ out,
    ClockJoin.ReadyRun machine (budget pcp x randomness clause)
      (input (fun i=>(literalCode (clause i)).bits) (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))) out ∧
      out 262=RepairOrdinary.frame (word pcp x randomness clause) ∧
      out 159=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) := by
  let codes : Fin 3→List Bool := fun i=>(literalCode (clause i)).bits
  let source := FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)
  obtain ⟨literal,hLiteral,hFields,hSource⟩ := RecoverySourceClauseLiterals.literals_run pcp x randomness clause
  have first := hLiteral.focus nativeSlots native_injective (input codes source) (by
    intro i
    simp only [input,nativeSlots,Fin.val_castAdd,i.isLt,dite_true]
    rfl)
  obtain ⟨cells,hCells,hWord⟩ := RecoverySourceClauseCells.cell_run (words pcp x randomness clause)
  have second := hCells.focus cellSlots cell_injective (install nativeSlots (input codes source) literal) (by
    intro i
    by_cases hi : i.val<3
    · simp only [cellSlots,hi,dite_true]
      rw [install_slot _ native_injective]
      simp only [RecoverySourceClauseCells.input,hi,dite_true,words]
      exact hFields ⟨i.val,hi⟩
    · have hv : (cellSlots i).val=160+i.val := by simp only [cellSlots,hi,dite_false]
      have hn : ∀ j,nativeSlots j≠cellSlots i := by
        intro j he; have hh:=congrArg Fin.val he; have hj:=j.isLt
        rw [hv] at hh
        change j.val=160+i.val at hh
        omega
      rw [install_other _ _ _ _ hn]
      have hi160 : ¬(cellSlots i).val<160 := by omega
      simp only [input,hi160,dite_false,RecoverySourceClauseCells.input,hi])
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  refine ⟨_,hall,?_,?_⟩
  · change install cellSlots _ _ (cellSlots 102)=_
    rw [install_slot _ cell_injective]
    exact hWord
  · rw [install_other _ _ _ _ (by
      intro i he
      have hv:=congrArg Fin.val he
      dsimp only [cellSlots,nativeSlots,RecoverySourceClauseLiterals.bank] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    change install nativeSlots _ _ (nativeSlots 159)=_
    rw [install_slot _ native_injective]
    exact hSource

theorem word_value {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) :
    value (word pcp x randomness clause)=Encodable.encode (CanonicalRecoveryLanguage.outerProofClause pcp x randomness clause) := by
  rw [word,RecoverySourceClauseCells.word_value]
  simp only [words,RecoverySourceLiteralMeaning.word_value]
  rfl

end NearCubicWires.RepairSource.RecoverySourceClauseCode
