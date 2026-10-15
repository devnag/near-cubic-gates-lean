import Proof.Supplier.RowCoefficientNormalize

/-! The physical nonnegative flag and framed absolute magnitude produce the
ordinary sign/magnitude field. Both sign writes, every magnitude bit, and
the final head reset are executed by this fixed four-tape program. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q bits=>if q.val=0 then some
    ⟨if bits 0 then 1 else 2,![none,none,some true],![.stay,.stay,.right]⟩
    else if q.val=1 ∨ q.val=2 then some
      ⟨3,![none,none,some (q.val==2)],![.stay,.stay,.right]⟩ else none
def slots : Fin 2 → Fin 3 := ![1,2]
noncomputable def copy := RecoveryFocus.machine slots Field.machine
noncomputable def raw := Composition.machine boot copy
noncomputable def machine := Rewind.machine raw
def input3 (nonnegative : Bool) (bits : List Bool) : Fin 3 → List Bool :=
  ![[nonnegative],frame bits,[]]
def input (nonnegative : Bool) (bits : List Bool) (cap : ℕ) : Fin 4 → List Bool :=
  ![[nonnegative],frame bits,[],List.replicate cap false]
def output (nonnegative : Bool) (bits : List Bool) (cap : ℕ) : Fin 4 → List Bool :=
  ![[nonnegative],frame bits,frame ((!nonnegative)::bits),
    List.replicate (max cap (2*bits.length+4)) false]
def started (nonnegative : Bool) (bits : List Bool) : Configuration 3 4 :=
  ⟨3,![0,0,2],![[nonnegative],frame bits,[true,!nonnegative]]⟩

theorem boot_run (nonnegative : Bool) (bits : List Bool) :
    ∃ r,run boot 2 (input3 nonnegative bits)=some r ∧
      r.final=started nonnegative bits ∧ r.steps=2 := by
  let mid : Configuration 3 4 := ⟨if nonnegative then 1 else 2,![0,0,1],![[nonnegative],frame bits,[true]]⟩
  have h0 : step boot (initialConfiguration boot (input3 nonnegative bits))=some mid := by
    cases nonnegative <;> simp [step,boot,initialConfiguration,input3,Configuration.scanned,readTapeBit]
    all_goals apply configuration_ext
    all_goals try rfl
    all_goals funext i; fin_cases i <;> rfl
  have h1 : step boot mid=some (started nonnegative bits) := by
    cases nonnegative <;> simp [step,boot,mid]
    all_goals apply configuration_ext
    all_goals try rfl
    all_goals funext i; fin_cases i <;> rfl
  exact ((Timed.single (by rfl) h0).trans (Timed.single (by cases nonnegative <;> rfl) h1)).run (by rfl)

theorem raw_run (nonnegative : Bool) (bits : List Bool) :
    ∃ r,run raw (2*bits.length+4) (input3 nonnegative bits)=some r ∧
      r.final.tapes=![[nonnegative],frame bits,frame ((!nonnegative)::bits)] ∧
      r.steps=2*bits.length+4 := by
  obtain ⟨first,hfirst,ff,fs⟩ := boot_run nonnegative bits
  obtain ⟨localRun,hl,lf,ls⟩ := Field.copy_run [] bits [] [true,!nonnegative]
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hl lf
  obtain ⟨last,hlast,ffinal,fsteps⟩ := RecoveryFocus.run_config slots (by decide) Field.machine
    first.final.heads first.final.tapes _ _ localRun hl
  have hi : RecoveryFocus.config slots first.final.heads first.final.tapes
      (Field.cfg 0 (frame bits) 0 [true,!nonnegative])=Composition.restart first.final copy.start := by
    rw [ff]
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at hlast
  have h := Composition.run_join boot copy 2 (2*bits.length+1) _ first last hfirst hlast
  have htime : 2+1+(2*bits.length+1)=2*bits.length+4 := by omega
  rw [htime] at h
  have hpick (i : Fin 3) : RecoveryFocus.pick slots i=(![none,some 0,some 1] : Fin 3 → Option (Fin 2)) i := by
    fin_cases i
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 0
    · exact RecoveryFocus.pick_slot slots (by decide) 1
  refine ⟨Composition.joinedReceipt first last,h,?_,?_⟩
  · change last.final.tapes=_
    rw [ffinal,lf,ff]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,hpick,Field.cfg,started,frame]
  · change first.steps+1+last.steps=_
    rw [fs,fsteps,ls,htime]

theorem emit_ready (nonnegative : Bool) (bits : List Bool) (cap : ℕ) :
    ReadyRun machine (4*bits.length+10) (input nonnegative bits cap) (output nonnegative bits cap) := by
  obtain ⟨base,hb,bt,bs⟩ := raw_run nonnegative bits
  obtain ⟨r,hr,rt,rl,rh,rs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb cap
  have he : (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      (input3 nonnegative bits) (fun _=>List.replicate cap false))=input nonnegative bits cap := by
    funext i; fin_cases i <;> simp [input,input3,Fin.addCases]
  have htime : 2*base.steps+2=4*bits.length+10 := by rw [bs]; omega
  rw [he,htime] at hr
  refine ⟨r,hr,?_,rh,rs.trans htime⟩
  funext i
  fin_cases i
  · exact (rt 0).trans (congrFun bt 0)
  · exact (rt 1).trans (congrFun bt 1)
  · exact (rt 2).trans (congrFun bt 2)
  · simpa [bs,output] using rl

end NearCubicWires.RepairOrdinary.RowCoefficientEmit
