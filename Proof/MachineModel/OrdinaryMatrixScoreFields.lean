import Proof.MachineModel.OrdinaryMatrixScoreGateStream
import Proof.MachineModel.OrdinaryMatrixTemplateEntries
import Proof.MachineModel.ClockScalarFields
import Proof.Amplification.RecoveryScratchErase

/-! Cold caller fields for the whole score enumeration. Raw d, M and C
produce the d sentinel, two native zero assignments, native zero id and
actual C-cell record counter; no zero-padding premise creates these tapes. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreColdFields
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroSlots (mode : Fin 3) : Fin 5 → Fin 21 :=
  if mode=0 then ![1,6,7,8,9] else if mode=1 then ![2,11,12,13,14] else ![5,15,16,17,18]
theorem zero_injective (mode : Fin 3) : Function.Injective (zeroSlots mode) := by fin_cases mode <;> decide
noncomputable def zero (mode : Fin 3) := RecoveryFocus.machine (zeroSlots mode) ClockNormalize.machine
noncomputable def first := TapeEmbedding.machine 16 MatrixRawDimension.resetMachine
noncomputable def firstA := Composition.machine first (zero 0)
noncomputable def firstD := Composition.machine firstA (zero 1)
noncomputable def firstM := Composition.machine firstD (zero 2)
def eraseSlots : Fin 3 → Fin 21 := ![19,10,20]
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine firstM erase
def input (d m c : ℕ) : Fin 21 → List Bool := fun i =>
  if i=0 then List.replicate d true else if i=5 then List.replicate m true else if i=10 then List.replicate c true else []
def budget (d m c : ℕ) := ((((4*d+8)+1+(4*d+4))+1+(4*d+4))+1+(4*m+4))+1+(2*c+4)

theorem zero_run (mode : Fin 3) (w : ℕ) (ambient : Fin 21 → List Bool)
    (hi : ∀ i,ambient (zeroSlots mode i)=ClockScalarFields.zeroInput w i) :
    ∃ actual,runFrom (zero mode) (4*w+4) (RecoveryCalls.restarted (zero mode) (fun _ => 0) ambient)=some actual ∧
      (∀ i,actual.final.heads i=0) ∧
      actual.final.tapes (zeroSlots mode 0)=List.replicate w true ∧
      actual.final.tapes (zeroSlots mode 2)=frame (binary w 0) ∧
      (∀ i,RecoveryFocus.pick (zeroSlots mode) i=none → actual.final.tapes i=ambient i) ∧ actual.steps=4*w+4 := by
  obtain ⟨base,hb,b0,_,b2,_,_,bh,bs⟩ := ClockScalarFields.zero_run w
  let localInput := initialConfiguration ClockNormalize.machine (ClockScalarFields.zeroInput w)
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config (zeroSlots mode) (zero_injective mode) ClockNormalize.machine
    (fun _ : Fin 21 => 0) ambient _ localInput base hb
  have hinput : RecoveryFocus.config (zeroSlots mode) (fun _ : Fin 21 => 0) ambient localInput=
      RecoveryCalls.restarted (zero mode) (fun _ => 0) ambient := by
    apply WilliamsSourceCrop.focus_same (zeroSlots mode) (RecoveryCalls.restarted (zero mode) (fun _ => 0) ambient)
    · intro i; rfl
    · exact hi
  rw [hinput] at hr
  have hpick (i : Fin 5) := RecoveryFocus.pick_slot (zeroSlots mode) (zero_injective mode) i
  refine ⟨actual,hr,?_,?_,?_,?_,hs.trans bs⟩
  · intro i
    rw [hf]
    simp only [RecoveryFocus.config]
    split <;> first | rfl | exact bh _
  · rw [hf]
    simpa only [RecoveryFocus.config,hpick] using b0
  · rw [hf]
    simpa only [RecoveryFocus.config,hpick] using b2
  · intro i h
    rw [hf]
    simp only [RecoveryFocus.config,h]

 theorem fields_run (d m c : ℕ) :
    ∃ actual,run machine (budget d m c) (input d m c)=some actual ∧
      (∀ i,actual.final.heads i=0) ∧
      actual.final.tapes 3=UnaryTemplate.tape d ∧
      actual.final.tapes 7=frame (binary d 0) ∧
      actual.final.tapes 12=frame (binary d 0) ∧
      actual.final.tapes 16=frame (binary m 0) ∧
      actual.final.tapes 10=List.replicate c true ∧
      actual.final.tapes 19=List.replicate c false ∧
      actual.final.tapes 20=List.replicate (c+1) false ∧
      actual.steps≤budget d m c := by
  obtain ⟨base,hb,b1,b2,b3,bh,bs⟩ := MatrixRawDimension.reset_run d
  let extras : Fin 16 → List Bool := fun i => if i=0 then List.replicate m true else if i=5 then List.replicate c true else []
  have he := TapeEmbedding.run_embed MatrixRawDimension.resetMachine (fun _ : Fin 16 => 0) extras _ _ base hb
  let expanded := TapeEmbedding.receipt (fun _ : Fin 16 => 0) extras base
  have eh (i : Fin 21) : expanded.final.heads i=0 := by
    fin_cases i <;> first | exact bh _ | rfl
  obtain ⟨a,ha,ah,a0,a2,ao,as⟩ := zero_run 0 d expanded.final.tapes (by
    intro i; fin_cases i
    · exact b1
    all_goals rfl)
  have ai : Composition.restart expanded.final (zero 0).start=
      RecoveryCalls.restarted (zero 0) (fun _ => 0) expanded.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext eh
    · rfl
  rw [← ai] at ha
  have ja := Composition.run_join first (zero 0) _ _ _ expanded a he ha
  let pa := Composition.joinedReceipt expanded a
  obtain ⟨z,hz,zh,z0,z2,zo,zs⟩ := zero_run 1 d pa.final.tapes (by
    intro i; fin_cases i
    · exact (ao 2 (by decide)).trans b2
    all_goals exact ao _ (by decide))
  have zi : Composition.restart pa.final (zero 1).start=
      RecoveryCalls.restarted (zero 1) (fun _ => 0) pa.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext ah
    · rfl
  rw [← zi] at hz
  have jz := Composition.run_join firstA (zero 1) _ _ _ pa z ja hz
  let pz := Composition.joinedReceipt pa z
  obtain ⟨id,hid,idh,id0,id2,ido,ids⟩ := zero_run 2 m pz.final.tapes (by
    intro i; fin_cases i
    all_goals exact (zo _ (by decide)).trans (ao _ (by decide)))
  have idi : Composition.restart pz.final (zero 2).start=
      RecoveryCalls.restarted (zero 2) (fun _ => 0) pz.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext zh
    · rfl
  rw [← idi] at hid
  have jid := Composition.run_join firstD (zero 2) _ _ _ pz id jz hid
  let pid := Composition.joinedReceipt pz id
  have blank (i : Fin 21) (hi : RecoveryFocus.pick (zeroSlots 2) i=none)
      (hz' : RecoveryFocus.pick (zeroSlots 1) i=none) (ha' : RecoveryFocus.pick (zeroSlots 0) i=none) :
      pid.final.tapes i=expanded.final.tapes i := (ido i hi).trans ((zo i hz').trans (ao i ha'))
  have er := RecoveryScratchErase.erase_ready c 0 (fun _ : Fin 1 => ([] : List Bool)) (by simp)
  obtain ⟨erased,her,ert,erh,ers⟩ := er
  obtain ⟨last,hl,lf,ls⟩ := RecoveryFocus.run_config eraseSlots (by decide) (RecoveryScratchErase.resetMachine 1)
    pid.final.heads pid.final.tapes _ _ erased her
  have ei : RecoveryFocus.config eraseSlots pid.final.heads pid.final.tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 1)
        (Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool)
          (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
            (fun _ : Fin 1 => ([] : List Bool)) (fun _ : Fin 1 => List.replicate c true))
          (fun _ : Fin 1 => List.replicate 0 false)))=Composition.restart pid.final erase.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact idh _
    · intro i; fin_cases i
      all_goals exact blank _ (by decide) (by decide) (by decide)
  rw [ei] at hl
  have joined := Composition.run_join firstM erase _ _ _ pid last jid hl
  have hin : Composition.leftConfig _ (Composition.leftConfig _ (Composition.leftConfig _ (Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 16 => 0) extras (initialConfiguration MatrixRawDimension.resetMachine (MatrixRawDimension.resetInput d))))))=
      initialConfiguration machine (input d m c) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have epick (i : Fin 3) := RecoveryFocus.pick_slot eraseSlots (by decide) i
  have other (i : Fin 21) (hi : RecoveryFocus.pick eraseSlots i=none) : last.final.tapes i=pid.final.tapes i := by
    rw [lf]
    simp only [RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt pid last,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    change last.final.heads i=0
    rw [lf]
    simp only [RecoveryFocus.config]
    split <;> first | exact idh _ | exact erh _
  · exact (other 3 (by decide)).trans ((blank 3 (by decide) (by decide) (by decide)).trans b3)
  · exact (other 7 (by decide)).trans ((ido 7 (by decide)).trans ((zo 7 (by decide)).trans a2))
  · exact (other 12 (by decide)).trans ((ido 12 (by decide)).trans z2)
  · exact (other 16 (by decide)).trans id2
  · change last.final.tapes (eraseSlots 1)=_
    rw [lf]
    simp only [RecoveryFocus.config,epick,ert]
    rfl
  · change last.final.tapes (eraseSlots 0)=_
    rw [lf]
    simp only [RecoveryFocus.config,epick,ert]
    rfl
  · change last.final.tapes (eraseSlots 2)=_
    rw [lf]
    simp only [RecoveryFocus.config,epick,ert]
    simp only [Fin.addCases,Nat.zero_max]
    rfl
  · change (((base.steps+1+a.steps)+1+z.steps)+1+id.steps)+1+last.steps≤_
    rw [bs,as,zs,ids,ls,ers]
    exact le_rfl

end NearCubicWires.RepairOrdinary.MatrixScoreColdFields
