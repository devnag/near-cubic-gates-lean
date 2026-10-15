import Proof.Amplification.RecoverySourceListCell

/-! Three original Encodable list cells execute on fixed banks. The empty
list terminator is physically written; intermediate cell fields are consumed
directly, including valid high zero bits. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseCells
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (k : Fin 3) (i : Fin 36) : Fin 112 :=
  if i.val=2 then ⟨2-k.val,by omega⟩
  else if i.val=3 then if k.val=0 then 3 else ⟨36*(k.val-1)+30,by have hk:=k.isLt; omega⟩
  else ⟨4+36*k.val+i.val,by have hk:=k.isLt; have hi:=i.isLt; omega⟩
theorem bank_injective (k : Fin 3) : Function.Injective (bank k) := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h; have ha:=a.isLt; have hb:=b.isLt; have hk:=k.isLt
  dsimp only [bank] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (words : Fin 3→List Bool) (i : Fin 112) :=
  if h : i.val<3 then RepairOrdinary.frame (words ⟨i.val,h⟩) else []
def prepared (words : Fin 3→List Bool) (i : Fin 112) :=
  if i.val=3 then RepairOrdinary.frame [] else input words i

def emptyMachine : Machine 112 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,(fun i=>if i.val=3 then some false else none),fun _=>.stay⟩ else none

theorem empty_ready (words : Fin 3→List Bool) :
    ClockJoin.ReadyRun emptyMachine 1 (input words) (prepared words) := by
  let last : Configuration 112 2 := ⟨1,fun _=>0,prepared words⟩
  have hs : step emptyMachine (initialConfiguration emptyMachine (input words))=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i.val=3
      · have he : i=3 := Fin.ext hi
        subst i; rfl
      · dsimp only [applyAction,initialConfiguration,last]
        simp only [hi,ite_false,prepared]
  obtain ⟨r,hr,hf,hsteps⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.tapes hf,(fun i=>congrArg (fun c=>c.heads i) hf),hsteps.le⟩

noncomputable def phase (k : Fin 3) := RecoveryFocus.machine (bank k) RecoverySourceListCell.machine
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine emptyMachine (phase 0)) (phase 1)) (phase 2)
def tailWord (words : Fin 3→List Bool) := RecoverySourceListCell.word (words 2) []
def midWord (words : Fin 3→List Bool) := RecoverySourceListCell.word (words 1) (tailWord words)
def word (words : Fin 3→List Bool) := RecoverySourceListCell.word (words 0) (midWord words)
def budget (words : Fin 3→List Bool) :=
  1+1+RecoverySourceListCell.budget (words 2) []+1+
    RecoverySourceListCell.budget (words 1) (tailWord words)+1+
    RecoverySourceListCell.budget (words 0) (midWord words)

theorem fresh (k : Fin 3) (i : Fin 36) (h2 : i.val≠2) (h3 : i.val≠3) :
    (bank k i).val=4+36*k.val+i.val := by simp only [bank,h2,h3,ite_false]
theorem fresh_cross (k l : Fin 3) (hk : k.val<l.val) (i : Fin 36)
    (h2 : i.val≠2) (h3 : i.val≠3) : ∀ j,bank k j≠bank l i := by
  intro j he
  have hv:=congrArg Fin.val he; have hj:=j.isLt; have hi:=i.isLt
  have hkk:=k.isLt; have hll:=l.isLt
  rw [fresh l i h2 h3] at hv
  dsimp only [bank] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem cell_run (words : Fin 3→List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget words) (input words) out ∧
      out 102=RepairOrdinary.frame (word words) := by
  obtain ⟨a,ha,aw⟩ := RecoverySourceListCell.cell_run (words 2) []
  have first := ha.focus (bank 0) (bank_injective 0) (prepared words) (by
    intro i; fin_cases i <;> rfl)
  let stage1 := install (bank 0) (prepared words) a
  obtain ⟨b,hb,bw⟩ := RecoverySourceListCell.cell_run (words 1) (tailWord words)
  have second := hb.focus (bank 1) (bank_injective 1) stage1 (by
    intro i
    by_cases h2 : i.val=2
    · have he : i=2 := Fin.ext h2
      subst i
      dsimp only [stage1]
      rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    by_cases h3 : i.val=3
    · have he : i=3 := Fin.ext h3
      subst i
      change install (bank 0) _ _ (bank 0 26)=_
      rw [install_slot _ (bank_injective 0)]
      exact aw
    dsimp only [stage1]
    rw [install_other _ _ _ _ (fresh_cross 0 1 (by decide) i h2 h3)]
    have hv:=fresh 1 i h2 h3
    have hn : ¬(bank 1 i).val<3 := by omega
    have hn3 : (bank 1 i).val≠3 := by omega
    simp only [prepared,hn3,ite_false,input,hn,RecoverySourceListCell.input,h2,h3,dite_false])
  let stage2 := install (bank 1) stage1 b
  obtain ⟨c,hc,cw⟩ := RecoverySourceListCell.cell_run (words 0) (midWord words)
  have third := hc.focus (bank 2) (bank_injective 2) stage2 (by
    intro i
    by_cases h2 : i.val=2
    · have he : i=2 := Fin.ext h2
      subst i
      dsimp only [stage2,stage1]
      rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide),
        install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    by_cases h3 : i.val=3
    · have he : i=3 := Fin.ext h3
      subst i
      change install (bank 1) _ _ (bank 1 26)=_
      rw [install_slot _ (bank_injective 1)]
      exact bw
    dsimp only [stage2,stage1]
    rw [install_other _ _ _ _ (fresh_cross 1 2 (by decide) i h2 h3),
      install_other _ _ _ _ (fresh_cross 0 2 (by decide) i h2 h3)]
    have hv:=fresh 2 i h2 h3
    have hn : ¬(bank 2 i).val<3 := by omega
    have hn3 : (bank 2 i).val≠3 := by omega
    simp only [prepared,hn3,ite_false,input,hn,RecoverySourceListCell.input,h2,h3,dite_false])
  have hall := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (empty_ready words) first) second) third
  refine ⟨_,hall,?_⟩
  change install (bank 2) _ _ (bank 2 26)=_
  rw [install_slot _ (bank_injective 2)]
  exact cw

theorem word_value (words : Fin 3→List Bool) :
    value (word words)=Nat.pair (value (words 0))
      (Nat.pair (value (words 1)) (Nat.pair (value (words 2)) 0+1)+1)+1 := by
  simp only [word,midWord,tailWord,RecoverySourceListCell.word_value,value]

end NearCubicWires.RepairSource.RecoverySourceClauseCells
