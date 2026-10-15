import Proof.Supplier.EquationScalarScan

/-! Physically prepend the canonical sign to the prepared magnitude,
copy its complete frame, and rewind every local head. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Emit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def negative (negate sign nonzero : Bool) : Bool := (if negate then !sign else sign) && nonzero
def input (bits : List Bool) (sign nonzero : Bool) : Fin 5→List Bool :=
  ![frame bits,[sign],[nonzero],[],[]]
def coreInput (bits : List Bool) (sign nonzero : Bool) : Fin 4→List Bool :=
  ![frame bits,[sign],[nonzero],[]]
def output (negate : Bool) (bits : List Bool) (sign nonzero : Bool) : Fin 5→List Bool :=
  ![frame bits,[sign],[nonzero],frame (negative negate sign nonzero::bits),
    List.replicate (2*bits.length+4) false]

def bootstrap (negate : Bool) : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bs => if q.val=0 then
      some ⟨1,![none,none,none,some true],![.stay,.stay,.stay,.right]⟩
    else if q.val=1 then
      some ⟨2,![none,none,none,some (negative negate (bs 1) (bs 2))],![.stay,.stay,.stay,.right]⟩
    else none
def bootCfg (negate : Bool) (bits : List Bool) (sign nonzero : Bool) : Configuration 4 3 :=
  ⟨2,![0,0,0,2],![frame bits,[sign],[nonzero],[true,negative negate sign nonzero]]⟩

theorem boot_run (negate : Bool) (bits : List Bool) (sign nonzero : Bool) :
    ∃ r,run (bootstrap negate) 2 (coreInput bits sign nonzero)=some r ∧
      r.final=bootCfg negate bits sign nonzero ∧ r.steps=2 := by
  let middle : Configuration 4 3 := ⟨1,![0,0,0,1],![frame bits,[sign],[nonzero],[true]]⟩
  have h0 : step (bootstrap negate) (initialConfiguration (bootstrap negate) (coreInput bits sign nonzero))=some middle := by
    simp [step,bootstrap,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h1 : step (bootstrap negate) middle=some (bootCfg negate bits sign nonzero) := by
    simp [step,bootstrap,middle,Configuration.scanned,readTapeBit]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)

def slots : Fin 2→Fin 4 := ![0,3]
def copy := RecoveryFocus.machine slots Field.machine
def raw (negate : Bool) := Composition.machine (bootstrap negate) copy
def machine (negate : Bool) := Rewind.machine (raw negate)

theorem pick (i : Fin 4) : RecoveryFocus.pick slots i=
    (if i=0 then some 0 else if i=3 then some 1 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots (by decide) 0
    | exact RecoveryFocus.pick_slot slots (by decide) 1
    | decide

theorem raw_run (negate : Bool) (bits : List Bool) (sign nonzero : Bool) :
    ∃ r,run (raw negate) (2*bits.length+4) (coreInput bits sign nonzero)=some r ∧
      r.final.tapes=![frame bits,[sign],[nonzero],frame (negative negate sign nonzero::bits)] ∧
      r.steps=2*bits.length+4 := by
  obtain ⟨base,hb,hf,hs⟩ := boot_run negate bits sign nonzero
  obtain ⟨localRun,hl,lf,ls⟩ := Field.copy_run [] bits [] [true,negative negate sign nonzero]
  simp only [List.nil_append,List.append_nil,List.length_nil] at hl lf
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes
      (Field.cfg 0 (frame bits) 0 [true,negative negate sign nonzero])=
      Composition.restart base.final copy.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [hf]; fin_cases i <;> rfl
    · intro i; rw [hf]; fin_cases i <;> rfl
  obtain ⟨focused,hfocus,ff,fs⟩ := RecoveryFocus.run_config slots (by decide) Field.machine
    base.final.heads base.final.tapes _ _ localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join (bootstrap negate) copy 2 (2*bits.length+1) _ base focused hb hfocus
  have he : 2+1+(2*bits.length+1)=2*bits.length+4 := by omega
  rw [he] at hj
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_⟩
  · change focused.final.tapes=_
    rw [ff,lf,hf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick,bootCfg,Field.cfg,frame]
  · change base.steps+1+focused.steps=_
    rw [hs,fs,ls]
    omega

theorem ready (negate : Bool) (bits : List Bool) (sign nonzero : Bool) :
    ReadyRun (machine negate) (4*bits.length+10) (input bits sign nonzero) (output negate bits sign nonzero) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run negate bits sign nonzero
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace (raw negate) _ _ base hb 0
  have he : 2*base.steps+2=4*bits.length+10 := by rw [hs]; omega
  rw [he] at hr
  have hin : (Fin.addCases (m:=4) (n:=1) (motive:=fun _ : Fin 5 => List Bool)
      (coreInput bits sign nonzero) (fun _ : Fin 1 => List.replicate 0 false))=input bits sign nonzero := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨r,hr,?_,hh,hsteps.trans he⟩
  funext i; fin_cases i
  all_goals first
    | simpa [hf,output] using ht 0
    | simpa [hf,output] using ht 1
    | simpa [hf,output] using ht 2
    | simpa [hf,output] using ht 3
    | simpa [hs,output] using hc

end
end NearCubicWires.RepairOrdinary.EquationScalar.Emit
