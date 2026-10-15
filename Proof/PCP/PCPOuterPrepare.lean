import Proof.PCP.PCPOuterFields
import Proof.PCP.PCPOuterCount

namespace NearCubicWires.RepairOrdinary.PCPOuter
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 132) := i==4
noncomputable def resetCopies := MaskedReset.machine copies selected
def input (a b c d sa sb sc sd : List Bool) (i : Fin 133) : List Bool :=
  Fin.addCases (m:=132) (n:=1) (motive:=fun _ => List Bool)
    (sources a b c d sa sb sc sd) (fun _ : Fin 1 => []) i
def resetHeads (a b c d : List Bool) (i : Fin 133) : ℕ :=
  Fin.addCases (m:=132) (n:=1) (motive:=fun _ => ℕ)
    (fun i => if selected i then 0 else fieldHeads a b c d i) (fun _ : Fin 1 => 0) i
def resetTapes (a b c d sa sb sc sd : List Bool) (i : Fin 133) : List Bool :=
  Fin.addCases (m:=132) (n:=1) (motive:=fun _ => List Bool)
    (fieldTapes a b c d sa sb sc sd)
    (fun _ : Fin 1 => List.replicate (2*size a b c d+7) false) i

theorem reset_copies_run (a b c d sa sb sc sd : List Bool) :
    Exact resetCopies (4*size a b c d+16) (fun _ => 0) (input a b c d sa sb sc sd)
      (resetHeads a b c d) (resetTapes a b c d sa sb sc sd) := by
  obtain ⟨base,hb,bh,bt,bs⟩ := copies_run a b c d sa sb sc sd
  have hc : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i _
    have hh := SelectiveReset.prefix_head (prefix_of_run copies _ _ base hb).1 i
    simpa using hh
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.reset_run copies selected _ _ base hb hc
  have he : 2*base.steps+2=4*size a b c d+16 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,?_,rs.trans he⟩
  · have hi : Rewind.recording
        (⟨copies.start,fun _ => 0,sources a b c d sa sb sc sd⟩ : Configuration 132 _) 0=
        (⟨resetCopies.start,fun _ => 0,input a b c d sa sb sc sd⟩ : Configuration 133 _) := by
      apply configuration_ext
      · rfl
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          simp [Rewind.recording,Rewind.config]
      · rfl
    rw [hi] at hr
    exact hr
  · rw [rf]
    change (fun i => Fin.addCases (m:=132) (n:=1) (motive:=fun _ => ℕ)
      (fun j => if selected j then 0 else base.final.heads j) (fun _ : Fin 1 => 0) i)=_
    rw [bh]
    rfl
  · rw [rf]
    change (fun i => Fin.addCases (m:=132) (n:=1) (motive:=fun _ => List Bool)
      base.final.tapes (fun _ : Fin 1 => List.replicate base.steps false) i)=_
    rw [bt,bs]
    rfl

def preparedHeads (a b c d : List Bool) := Function.update (resetHeads a b c d) 6 1
def preparedTapes (a b c d sa sb sc sd : List Bool) :=
  Function.update (resetTapes a b c d sa sb sc sd) 6 (RepairSource.VerifierDecoding.CompareMachine.word 4)
noncomputable def preparation := Composition.machine resetCopies (countMachine (6 : Fin 133))

theorem preparation_run (a b c d sa sb sc sd : List Bool) :
    Exact preparation (4*size a b c d+27) (fun _ => 0) (input a b c d sa sb sc sd)
      (preparedHeads a b c d) (preparedTapes a b c d sa sb sc sd) := by
  have hr := reset_copies_run a b c d sa sb sc sd
  have hc := count_run (6 : Fin 133) (resetHeads a b c d) (resetTapes a b c d sa sb sc sd)
    (by rfl) (by rfl)
  have joined := exact_join hr hc
  have he : (4*size a b c d+16)+1+10=4*size a b c d+27 := by omega
  rw [he] at joined
  exact joined

def bank (i : Fin 128) : Fin 133 := ⟨4+i.val,by omega⟩
theorem bank_injective : Function.Injective bank := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [bank] at hv
  omega

theorem prepared_heads (a b c d : List Bool) (j : Fin 128) :
    preparedHeads a b c d (bank j)=PCPTraversal.heads 0 j := by
  by_cases h2 : j=2
  · subst j
    rfl
  have hb6 : bank j≠6 := by intro h; have hv := congrArg Fin.val h; simp only [bank] at hv; omega
  rw [preparedHeads,Function.update_of_ne hb6]
  rw [show bank j=(⟨4+j.val,by omega⟩ : Fin 132).castAdd 1 from rfl]
  simp only [resetHeads,Fin.addCases_left]
  change (if selected ⟨4+j.val,by omega⟩ then 0 else fieldHeads a b c d ⟨4+j.val,by omega⟩)=_
  by_cases h0 : j=0
  · subst j
    rfl
  have hn : j.val≠0 := by exact fun h => h0 (Fin.ext h)
  simp [selected,fieldHeads,PCPTraversal.heads,h0,h2,Fin.ext_iff]
  split_ifs <;> omega

theorem prepared_tapes (a b c d sa sb sc sd : List Bool) (j : Fin 128) :
    preparedTapes a b c d sa sb sc sd (bank j)=
      PCPTraversal.input (FieldList.stream (fields a b c d)) 4 j := by
  by_cases h2 : j=2
  · subst j
    rfl
  have hb6 : bank j≠6 := by intro h; have hv := congrArg Fin.val h; simp only [bank] at hv; omega
  rw [preparedTapes,Function.update_of_ne hb6]
  rw [show bank j=(⟨4+j.val,by omega⟩ : Fin 132).castAdd 1 from rfl]
  simp only [resetTapes,Fin.addCases_left]
  change fieldTapes a b c d sa sb sc sd ⟨4+j.val,by omega⟩=_
  by_cases h0 : j=0
  · subst j
    simpa [fieldTapes,PCPTraversal.input] using stream_fields a b c d
  have hn : j.val≠0 := fun h => h0 (Fin.ext h)
  simp [fieldTapes,sources,PCPTraversal.input,h0,h2,Fin.ext_iff]
  split_ifs <;> first | rfl | omega

end NearCubicWires.RepairOrdinary.PCPOuter
