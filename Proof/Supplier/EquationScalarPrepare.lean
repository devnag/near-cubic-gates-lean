import Proof.Supplier.EquationScalarArithmetic

/-! Cold signed-field preparation: physically save its sign, initialize
the scalar flags and isolate one-bit-wider magnitude. Every head is reset
from the executed prefix; no width or workspace is supplied separately. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def input (sign : Bool) (bits : List Bool) : Fin 12→List Bool :=
  fun i => if i=0 then frame (sign::bits) else []
def coreInput (sign : Bool) (bits : List Bool) : Fin 10→List Bool :=
  fun i => if i=0 then frame (sign::bits) else []
def booted (sign : Bool) (bits : List Bool) : Fin 10→List Bool :=
  ![frame (sign::bits),[sign],[],[],[false],[],[],[false],[],[]]
def bodyOutput (sign : Bool) (bits : List Bool) : Fin 10→List Bool :=
  Function.update (booted sign bits) 2 (frame (bits++[false]))
def output (sign : Bool) (bits : List Bool) : Fin 12→List Bool :=
  ![frame (sign::bits),[sign],frame (bits++[false]),[],[false],[],[],[false],[],[],
    List.replicate (2*bits.length+6) false,[]]

def bootstrap : Machine 10 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bs => if q.val=0 then
      some ⟨1,fun i => if i=4 ∨ i=7 then some false else none,
        fun i => if i=0 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i => if i=1 then some (bs 0) else none,
        fun i => if i=0 then .right else .stay⟩
    else none
def bootCfg (sign : Bool) (bits : List Bool) : Configuration 10 3 :=
  ⟨2,fun i => if i=0 then 2 else 0,booted sign bits⟩

theorem boot_run (sign : Bool) (bits : List Bool) :
    ∃ r,run bootstrap 2 (coreInput sign bits)=some r ∧ r.final=bootCfg sign bits ∧ r.steps=2 := by
  let middle : Configuration 10 3 :=
    ⟨1,fun i => if i=0 then 1 else 0,
      ![frame (sign::bits),[],[],[],[false],[],[],[false],[],[]]⟩
  have h0 : step bootstrap (initialConfiguration bootstrap (coreInput sign bits))=some middle := by
    simp [step,bootstrap,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h1 : step bootstrap middle=some (bootCfg sign bits) := by
    simp [step,bootstrap,middle,Configuration.scanned,frame,readTapeBit]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)

def slots : Fin 2→Fin 10 := ![0,2]
theorem pick (i : Fin 10) : RecoveryFocus.pick slots i=
    (if i=0 then some 0 else if i=2 then some 1 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots (by decide) 0
    | exact RecoveryFocus.pick_slot slots (by decide) 1
    | decide
def widen := RecoveryFocus.machine slots EquationWiden.machine
def raw := Composition.machine bootstrap widen
def machine := TapeEmbedding.machine 1 (Rewind.machine raw)
def budget (bits : List Bool) := 4*bits.length+14

theorem raw_run (sign : Bool) (bits : List Bool) :
    ∃ r,run raw (2*bits.length+6) (coreInput sign bits)=some r ∧
      r.final.tapes=bodyOutput sign bits ∧ r.steps=2*bits.length+6 := by
  obtain ⟨base,hb,hf,hs⟩ := boot_run sign bits
  obtain ⟨localRun,hl,lf,ls⟩ := EquationWiden.field_run [true,sign] bits [] []
  have hw : [true,sign]++frame bits++[]=frame (sign::bits) := by simp [frame]
  rw [hw] at hl lf
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes
      (EquationWiden.cfg 0 (frame (sign::bits)) [true,sign].length [])=
      Composition.restart base.final widen.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [hf]; fin_cases i <;> rfl
    · intro i; rw [hf]; fin_cases i <;> rfl
  obtain ⟨focused,hfocus,ff,fs⟩ := RecoveryFocus.run_config slots (by decide) EquationWiden.machine
    base.final.heads base.final.tapes _ _ localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join bootstrap widen 2 (2*bits.length+3) _ base focused hb hfocus
  have he : 2+1+(2*bits.length+3)=2*bits.length+6 := by omega
  rw [he] at hj
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_⟩
  · change focused.final.tapes=bodyOutput sign bits
    rw [ff,lf,hf]
    funext i; fin_cases i <;>
      simp [RecoveryFocus.config,pick,bootCfg,booted,
        bodyOutput,EquationWiden.cfg]
  · change base.steps+1+focused.steps=_
    rw [hs,fs,ls]
    omega

theorem ready (sign : Bool) (bits : List Bool) :
    ReadyRun machine (budget bits) (input sign bits) (output sign bits) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run sign bits
  obtain ⟨last,hl,lt,lc,lh,ls,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hc : 2*base.steps+2=budget bits := by rw [hs]; unfold budget; omega
  rw [hc] at hl
  have he := TapeEmbedding.run_embed (Rewind.machine raw) (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => []) _ _ last hl
  let r := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) last
  have hi : TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
      (initialConfiguration (Rewind.machine raw)
        (Fin.addCases (coreInput sign bits) (fun _ : Fin 1 => List.replicate 0 false)))=
      initialConfiguration machine (input sign bits) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  refine ⟨r,he,?_,?_,ls.trans hc⟩
  · have ot : last.final.tapes=Fin.addCases (motive:=fun _ : Fin (10+1) => List Bool)
        (bodyOutput sign bits) (fun _ : Fin 1 => List.replicate (2*bits.length+6) false) := by
      funext i
      refine Fin.addCases (m:=10) (n:=1) (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.addCases_left,hf] using lt j
      · fin_cases j
        change last.final.tapes 10=List.replicate (2*bits.length+6) false
        have hz : (0 : Fin 1).natAdd 10=(10 : Fin 11) := by decide
        simpa only [hz,hs,Nat.zero_max] using lc
    change (Fin.addCases (m:=11) (n:=1) (motive:=fun _ : Fin 12 => List Bool)
      last.final.tapes (fun _ : Fin 1 => []))=output sign bits
    rw [ot]
    funext i; fin_cases i <;> simp [output,bodyOutput,booted,Fin.addCases]
  · intro i
    refine Fin.addCases (m:=11) (n:=1) (fun j => ?_) (fun j => ?_) i
    · simpa only [r,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left] using lh j
    · simp only [r,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]

end
end NearCubicWires.RepairOrdinary.EquationScalar.Prepare
