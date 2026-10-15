import Proof.Amplification.RecoveryTablesGraph

/-! Exact table-buffer endpoint and paid restoration of the reused inner
source. The other streaming/scalar heads retain their actual positions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTables
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputHeads (word innerBits : List Bool) : Fin 11→Nat :=
  ![2*word.length+1,1,1,2*innerBits.length+1,0,0,1,1,0,0,0]
def outputTapes (word innerBits outerBits : List Bool) (n m width cap : Nat) : Fin 11→List Bool :=
  ![frame word,CompareMachine.word n,CompareMachine.word cap,frame innerBits,
    List.replicate (2*innerBits.length+1) false,[true],CompareMachine.word (2*width),
    CompareMachine.word m,frame outerBits,List.replicate (2*outerBits.length+1) false,[true]]

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem outer_layout {s : Nat} (q : Fin s) (word innerBits outerBits : List Bool)
    (n m width cap : Nat) :
    outer q word innerBits outerBits n m width cap=
      (⟨q,outputHeads word innerBits,outputTapes word innerBits outerBits n m width cap⟩ : Configuration 11 s) := by
  apply focus_configuration outerSlots outerSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i hi; fin_cases i <;> try rfl
    exact False.elim (hi 0 rfl)
  · intro i hi; fin_cases i <;> try rfl
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 3 rfl)
    · exact False.elim (hi 4 rfl)
    · exact False.elim (hi 5 rfl)

noncomputable def resetProgram := SelectiveReset.machine machine (3 : Fin 11)
def resetBudget (width cap : Nat) (word : List Bool) := 2*budget width cap word+2
noncomputable def restored (word innerBits outerBits : List Bool) (n m width cap logged : Nat) :=
  SelectiveReset.finished (s:=Fintype.card (RecoveryCalls.Control sizes))
    (fun i=>if i=(3 : Fin 11) then 0 else outputHeads word innerBits i)
    (outputTapes word innerBits outerBits n m width cap) logged

theorem reset_run (width cap : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom resetProgram (resetBudget width cap word)
        (Rewind.recording (initial machine.start word k width cap) 0)=some r ∧
      r.steps ≤ resetBudget width cap word ∧ r.final.heads 10=0 ∧
      r.final.tapes 10=[answer width cap word k] ∧ r.final.heads 3=0 ∧
      ∀ n innerBits m outerBits,
        readCount cap (word.drop k)=some (n,innerBits) →
        readCount cap (innerBits.drop (4*width*n))=some (m,outerBits) →
        n ≤ cap ∧ m ≤ cap ∧ ∃ logged,logged ≤ budget width cap word ∧
          r.final=restored word innerBits outerBits n m width cap logged := by
  obtain ⟨base,hr,hb,hh,ht,hready⟩ := tables_run width cap word k
  have hhead : base.final.heads (3 : Fin 11) ≤ base.steps := by
    have h := SelectiveReset.prefix_head (prefix_of_run machine _ _ base hr).1 (3 : Fin 11)
    change base.final.heads (3 : Fin 11) ≤ 0+base.steps at h
    simpa only [Nat.zero_add] using h
  obtain ⟨r,h,hfinal,hsteps,_⟩ := SelectiveReset.reset_run machine 3 _ _ base hr hhead
  have hbound : 2*base.steps+2 ≤ resetBudget width cap word := by unfold resetBudget; omega
  have hm := runFrom_moreFuel resetProgram (2*base.steps+2)
    (resetBudget width cap word-(2*base.steps+2)) _ r h
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨r,hm,by omega,?_,?_,?_,?_⟩
  · rw [hfinal]; exact hh
  · rw [hfinal]; exact ht
  · rw [hfinal]; rfl
  · intro n innerBits m outerBits hp1 hp2
    obtain ⟨hn,hm,hout⟩ := hready n innerBits m outerBits hp1 hp2
    refine ⟨hn,hm,base.steps,hb,?_⟩
    rw [hfinal,hout,outer_layout]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryColdTables
