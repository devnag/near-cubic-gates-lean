import Proof.PCP.VerifierDecodingFourfold

/-! Produce the reusable 4t tag-width template from a physical capped t
counter and a blank output. The sentinel write and both returns are paid. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.FourfoldReady
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val=1
  rule := fun q _ => if q.val=0 then
    some ⟨1,![none,some false],![.stay,.right]⟩ else none
def input (c t : ℕ) : Configuration 2 2 := ⟨0,![1,0],![CapMachine.counter c t,[]]⟩
def prepared (c t : ℕ) : Configuration 2 2 := ⟨1,![1,1],![CapMachine.counter c t,[false]]⟩
def data (c t : ℕ) : Fin 2 → List Bool := ![CapMachine.counter c t,CompareMachine.word (4*t)]

theorem boot_run (c t : ℕ) :
    ∃ r, runFrom boot 1 (input c t)=some r ∧ r.final=prepared c t ∧ r.steps=1 := by
  have he : step boot (input c t)=some (prepared c t) := by
    simp [step,boot,input]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [applyAction,writeTapeBit,prepared]
  exact (Timed.single (by rfl : boot.halted (0 : Fin 2)=false) he).run (by rfl)

theorem word_reset (n : ℕ) :
    ∃ r, runFrom UnaryTemplate.machine (n+2)
        (UnaryTemplate.config 0 (CompareMachine.word n) (n+1))=some r ∧
      r.final=UnaryTemplate.config 2 (CompareMachine.word n) 1 ∧ r.steps=n+2 := by
  have hp := UnaryTemplate.return_prefix (CompareMachine.word n) n (by rfl) (by
    intro k hk
    change readTapeBit (List.replicate n true) k=true
    rw [SliceMachine.read_unary]
    simp [hk])
  have hp' : Timed UnaryTemplate.machine (n+1)
      (UnaryTemplate.config 1 (CompareMachine.word n) n) (UnaryTemplate.config 2 (CompareMachine.word n) 1) :=
    ⟨_,hp⟩
  have hs := Timed.single (by rfl : UnaryTemplate.machine.halted (0 : Fin 3)=false)
    (UnaryTemplate.start_step (CompareMachine.word n) n)
  have hall := hs.trans hp'
  have ht : 1+(n+1)=n+2 := by omega
  rw [ht] at hall
  exact hall.run (by rfl)

theorem output_reset (c t : ℕ) :
    ∃ r, runFrom (CounterReset.program (1 : Fin 2)) (4*t+2)
        ⟨0,![1,4*t+1],data c t⟩=some r ∧
      r.final=⟨2,![1,1],data c t⟩ ∧ r.steps=4*t+2 := by
  obtain ⟨base,hb,hf,hs⟩ := word_reset (4*t)
  obtain ⟨r,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config (CounterReset.slot (1 : Fin 2))
    (CounterReset.slot_injective _) UnaryTemplate.machine ![1,4*t+1] (data c t) _ _ base hb
  have hi : RecoveryFocus.config (CounterReset.slot (1 : Fin 2)) ![1,4*t+1] (data c t)
      (UnaryTemplate.config 0 (CompareMachine.word (4*t)) (4*t+1))=
      (⟨0,![1,4*t+1],data c t⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,CounterReset.slot_pick,UnaryTemplate.config]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,CounterReset.slot_pick,UnaryTemplate.config,data]
  rw [hi] at hr
  refine ⟨r,hr,?_,by omega⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,CounterReset.slot_pick,UnaryTemplate.config]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,CounterReset.slot_pick,UnaryTemplate.config,data]

noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine boot Fourfold.machine) (CounterReset.program (0 : Fin 2)))
  (CounterReset.program (1 : Fin 2))
noncomputable def initial (c t : ℕ) :=
  Composition.leftConfig 3 (Composition.leftConfig 3 (Composition.leftConfig 5 (input c t)))

theorem ready_run (c t : ℕ) (ht : t≤c) :
    ∃ r, runFrom machine (9*t+9) (initial c t)=some r ∧
      r.final=⟨12,![1,1],data c t⟩ ∧ r.steps=9*t+9 := by
  obtain ⟨a,ha,haf,has⟩ := boot_run c t
  obtain ⟨b,hb,hbf,hbs⟩ := Fourfold.fourfold_run c t
  have hboot : Composition.restart a.final Fourfold.machine.start=Fourfold.cfg 0 c t 0 0 := by rw [haf]; rfl
  rw [←hboot] at hb
  have hab := Composition.run_join boot Fourfold.machine 1 (4*t+1) _ a b ha hb
  obtain ⟨d,hd,hdf,hds⟩ := CounterReset.reset_run (0 : Fin 2) ![t+1,4*t+1] (data c t)
    c t t ht (Nat.le_refl _) (by rfl) (by rfl)
  have hi : Composition.restart (Composition.joinedReceipt a b).final (CounterReset.program (0 : Fin 2)).start=
      (⟨0,![t+1,4*t+1],data c t⟩ : Configuration 2 3) := by
    change Composition.restart (Composition.rightConfig 2 b.final) _=_
    rw [hbf]
    rfl
  rw [←hi] at hd
  have habd := Composition.run_join (Composition.machine boot Fourfold.machine) (CounterReset.program (0 : Fin 2))
    (1+1+(4*t+1)) (t+2) _ (Composition.joinedReceipt a b) d hab hd
  obtain ⟨e,he,hef,hes⟩ := output_reset c t
  have hi' : Composition.restart (Composition.joinedReceipt (Composition.joinedReceipt a b) d).final
      (CounterReset.program (1 : Fin 2)).start=(⟨0,![1,4*t+1],data c t⟩ : Configuration 2 3) := by
    change Composition.restart (Composition.rightConfig 7 d.final) _=_
    rw [hdf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [←hi'] at he
  have hall := Composition.run_join (Composition.machine (Composition.machine boot Fourfold.machine)
      (CounterReset.program (0 : Fin 2))) (CounterReset.program (1 : Fin 2))
    ((1+1+(4*t+1))+1+(t+2)) (4*t+2) _ (Composition.joinedReceipt (Composition.joinedReceipt a b) d) e habd he
  have htime : ((1+1+(4*t+1))+1+(t+2))+1+(4*t+2)=9*t+9 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt (Composition.joinedReceipt a b) d) e,hall,?_,?_⟩
  · change Composition.rightConfig 10 e.final=_
    rw [hef]
    rfl
  · change a.steps+1+b.steps+1+d.steps+1+e.steps=_
    omega

end NearCubicWires.RepairSource.VerifierDecoding.FourfoldReady
