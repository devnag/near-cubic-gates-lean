import Proof.MachineModel.OrdinaryMatrixFrameCopy
import Proof.MachineModel.OrdinaryKeyAdvance

/-! Advance a right bucket using the retained fixed B word. Copy B back to
the interval operand, then execute the existing boundary/coordinate advance;
the source table and growing keyed output are never traversed. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightAdvance
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Params where
  W : ℕ
  K : ℕ
  I : ℕ
  keyCap : ℕ
  resetCap : ℕ
  B : ℕ
  source : List Bool
structure Store where
  a : ℕ
  b : ℕ
  rank : ℕ
  inner : ℕ
  upper : List Bool
  record : List Bool
  clone : List Bool
  out : List Bool

def cfg {s : ℕ} (q : Fin s) (p : Params) (v : Store) : Configuration 25 s :=
  TapeEmbedding.config (fun _ : Fin 4 => 0)
    ![List.replicate (2*p.W+1) false,frame (binary p.W p.B),List.replicate (2*p.W+1) false,List.replicate (4*p.W+3) false]
    (KeyReset.config q p.W v.a v.b v.rank v.upper v.record v.clone true p.source v.out p.K p.I v.inner p.keyCap p.resetCap)
def copied (p : Params) (v : Store) : Store := {v with b := p.B}
def advanced (p : Params) (v : Store) : Store :=
  {v with a := v.a+p.B,b := p.B,inner := v.inner+1,upper := frame (binary p.W (v.a+p.B))}
def copySlots : Fin 4 → Fin 25 := ![22,1,23,24]
def advanceSlots : Fin 22 → Fin 25 := fun i => if i.val<21 then ⟨i.val,by omega⟩ else 24
noncomputable def copy : Machine 25 6 := RecoveryFocus.machine copySlots MatrixFrameCopy.machine
noncomputable def advance : Machine 25 18 := RecoveryFocus.machine advanceSlots KeyAdvance.machine
noncomputable def machine : Machine 25 24 := Composition.machine copy advance

-- reason: measured 250k kernel exhaustion checking this finite 25-tape projection equality, with no data recursion.
set_option maxHeartbeats 1000000 in
theorem copied_tapes {s k : ℕ} (q : Fin s) (q' : Fin k) (p : Params) (v : Store)
    (i : Fin 25) (hi : i≠1) : (cfg q p v).tapes i=(cfg q' p (copied p v)).tapes i := by
  simp only [cfg,TapeEmbedding.config,KeyReset.config,KeyCell.config,RecordCell.config,CellEmit.config,
    LocalCell.input,LocalCell.raw,copied]
  fin_cases i <;> first | exact False.elim (hi rfl) | rfl

theorem copy_run (p : Params) (v : Store) :
    ∃ actual : ExecutionReceipt 25 6,runFrom copy (8*p.W+8) (cfg copy.start p v)=some actual ∧
      actual.final=cfg actual.final.control p (copied p v) ∧ actual.steps=8*p.W+8 := by
  obtain ⟨base,hb,ht,hh,hs⟩ := MatrixFrameCopy.copy_run (binary p.W p.B) (frame (binary p.W v.b)) (by simp)
  simp only [binary_length] at hb ht hs
  let entry := cfg copy.start p v
  let part := initialConfiguration MatrixFrameCopy.machine (MatrixFrameCopy.input (binary p.W p.B) (frame (binary p.W v.b)))
  have hi : RecoveryFocus.config copySlots entry.heads entry.tapes part=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [part,MatrixFrameCopy.input,initialConfiguration]
      all_goals rfl
  obtain ⟨actual,ha,hf,hsteps⟩ := RecoveryFocus.run_config copySlots (by decide) MatrixFrameCopy.machine
    entry.heads entry.tapes _ part base hb
  rw [hi] at ha
  have hp1 : RecoveryFocus.pick copySlots 1=some 1 := RecoveryFocus.pick_slot copySlots (by decide) 1
  refine ⟨actual,ha,?_,hsteps.trans hs⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i
    cases hi : RecoveryFocus.pick copySlots i with
    | none => simp only [RecoveryFocus.config,hi]; rfl
    | some j =>
      have hij := RecoveryFocus.slot_of_pick copySlots hi
      simp only [RecoveryFocus.config,hi]
      rw [hh,←hij]
      fin_cases j <;> rfl
  · funext i
    cases hi : RecoveryFocus.pick copySlots i with
    | none =>
      have hn : i≠1 := by intro he; subst i; rw [hp1] at hi; contradiction
      simp only [RecoveryFocus.config,hi]
      exact copied_tapes copy.start _ p v i hn
    | some j =>
      have hij := RecoveryFocus.slot_of_pick copySlots hi
      simp only [RecoveryFocus.config,hi]
      rw [ht,←hij]
      fin_cases j <;> rfl

theorem advance_run (p : Params) (v : Store) (hi : v.inner+1<2^p.I) (hk : 2*p.I ≤ p.keyCap)
    (ha : v.a+p.B<2^p.W) (hu : v.upper.length ≤ 2*p.W+1) :
    ∃ actual : ExecutionReceipt 25 24,runFrom machine (20*p.W+4*p.I+25)
      (cfg machine.start p v)=some actual ∧ actual.final=cfg 23 p (advanced p v) ∧
      actual.steps ≤ 20*p.W+4*p.I+25 := by
  obtain ⟨first,hfirst,hff,hfs⟩ := copy_run p v
  obtain ⟨last,hl,hlf,hls,_⟩ := KeyAdvance.advance_run p.W v.a p.B v.rank v.upper v.record v.clone true
    p.source v.out p.K p.I v.inner p.keyCap p.resetCap hi hk ha hu
  let entry := KeyAdvance.config KeyAdvance.machine.start p.W v.a p.B v.rank v.upper v.record v.clone true
    p.source v.out p.K p.I v.inner p.keyCap p.resetCap
  have hentry : RecoveryFocus.config advanceSlots first.final.heads first.final.tapes entry=
      Composition.restart first.final advance.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [hff]
      fin_cases i <;> rfl
    · intro i
      rw [hff]
      fin_cases i <;> rfl
  obtain ⟨focused,hfocus,hf,hsteps⟩ := RecoveryFocus.run_config advanceSlots (by decide) KeyAdvance.machine
    first.final.heads first.final.tapes _ entry last hl
  rw [hentry] at hfocus
  have hj := Composition.run_join copy advance (8*p.W+8) (12*p.W+4*p.I+16)
    (cfg copy.start p v) first focused hfirst hfocus
  have htime : (8*p.W+8)+1+(12*p.W+4*p.I+16)=20*p.W+4*p.I+25 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first focused,hj,?_,?_⟩
  · change Composition.rightConfig 6 focused.final=_
    rw [hf,hlf]
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick advanceSlots i with
      | none =>
        simp only [Composition.rightConfig,RecoveryFocus.config,hp]
        rw [hff]
        rfl
      | some j =>
        have hij := RecoveryFocus.slot_of_pick advanceSlots hp
        simp only [Composition.rightConfig,RecoveryFocus.config,hp]
        rw [←hij]
        fin_cases j <;> rfl
    · funext i
      cases hp : RecoveryFocus.pick advanceSlots i with
      | none =>
        have outside : 21 ≤ i.val ∧ i.val<24 := by
          have hx : ∀ j : Fin 22,advanceSlots j≠i := by
            intro j he
            have hj := RecoveryFocus.pick_slot advanceSlots (by decide) j
            rw [he,hp] at hj
            contradiction
          have hlow : 21 ≤ i.val := by
            by_contra hn
            have hsmall : i.val<21 := by omega
            let j : Fin 22 := ⟨i.val,by omega⟩
            have hj : advanceSlots j=i := by
              apply Fin.ext
              simp [advanceSlots,j,hsmall]
            exact hx j hj
          have hn24 : i≠24 := by intro he; subst i; exact hx 21 rfl
          have hval : i.val≠24 := by intro he; exact hn24 (Fin.ext he)
          omega
        simp only [Composition.rightConfig,RecoveryFocus.config,hp]
        rw [hff]
        fin_cases i <;> simp at outside <;> rfl
      | some j =>
        have hij := RecoveryFocus.slot_of_pick advanceSlots hp
        simp only [Composition.rightConfig,RecoveryFocus.config,hp]
        rw [←hij]
        fin_cases j <;> rfl
  · change first.steps+1+focused.steps ≤ _
    rw [hsteps]
    omega

end NearCubicWires.RepairOrdinary.MatrixRightAdvance
