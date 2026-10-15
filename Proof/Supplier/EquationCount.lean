import Proof.Supplier.EquationCountReady

/-! The original framed equation-row input supplies the complete physical
count/capacity bank. Its raw cut cursor and external source are retained. -/
namespace NearCubicWires.RepairOrdinary.EquationCountCold
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 32) : Fin 62 :=
  if j.val=0 then 12 else if j.val=1 then 22 else if j.val=2 then 32
  else if j.val=3 then 33 else ⟨j.val+30,by omega⟩
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 28 EquationHeaderBoot.machine
noncomputable def last := RecoveryFocus.machine slots EquationCountReady.machine
noncomputable def machine := Composition.machine first last
def input (d p g : ℕ) (odd : Bool) (suffix : List Bool) : Fin 62 → List Bool :=
  fun i => if i=0 then frame (EquationHeaderRead.word d p g (odd::suffix)) else []
def budget (d p g : ℕ) (odd : Bool) (suffix : List Bool) :=
  EquationHeaderBoot.budget d p g odd suffix+1+EquationCountReady.budget d p g

theorem cold_run (d p g : ℕ) (odd : Bool) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g odd suffix) (input d p g odd suffix)=some actual ∧
    actual.final.tapes 0=frame (EquationHeaderRead.word d p g (odd::suffix)) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) ∧
      actual.final.heads 1=(EquationHeaderRead.header d p g).length+1 ∧
    (∀ j,actual.final.tapes (slots j)=EquationCountCapacity.data8 d p g odd j ∧
      actual.final.heads (slots j)=0) ∧ actual.steps ≤ budget d p g odd suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,bd,bdh,bp,bph,bg,bgh,bo,boh,bs⟩ :=
    EquationHeaderBoot.headers_run d p g odd suffix
  let prepared := TapeEmbedding.receipt (fun _ : Fin 28 => 0) (fun _ : Fin 28 => []) base
  have he := TapeEmbedding.run_embed EquationHeaderBoot.machine (fun _ : Fin 28 => 0)
    (fun _ : Fin 28 => []) _ _ base hb
  have oldT (i : Fin 34) : prepared.final.tapes (i.castAdd 28)=base.final.tapes i := by
    change (Fin.addCases (m := 34) (n := 28) (motive := fun _ => List Bool)
      base.final.tapes (fun _ => [])) (i.castAdd 28)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin 34) : prepared.final.heads (i.castAdd 28)=base.final.heads i := by
    change (Fin.addCases (m := 34) (n := 28) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd 28)=_
    rw [Fin.addCases_left]
  obtain ⟨body,hbody,bodyT,bodyH,bodyS⟩ := EquationCountReady.ready d p g odd
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes
      (initialConfiguration EquationCountReady.machine (EquationCountReady.input d p g odd))=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · exact (oldH 12).trans bdh
      · exact (oldH 22).trans bph
      · exact (oldH 32).trans bgh
      · exact (oldH 33).trans boh
      all_goals rfl
    · intro j
      fin_cases j
      · exact (oldT 12).trans bd
      · exact (oldT 22).trans bp
      · exact (oldT 32).trans bg
      · exact (oldT 33).trans bo
      all_goals rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective EquationCountReady.machine
    prepared.final.heads prepared.final.tapes _ _ body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 28 => 0) (fun _ : Fin 28 => [])
        (initialConfiguration EquationHeaderBoot.machine (EquationHeaderBoot.input d p g odd suffix)))=
      initialConfiguration machine (input d p g odd suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have otherT (i : Fin 34) (hn : RecoveryFocus.pick slots (i.castAdd 28)=none) :
      focused.final.tapes (i.castAdd 28)=base.final.tapes i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact oldT i
  have otherH (i : Fin 34) (hn : RecoveryFocus.pick slots (i.castAdd 28)=none) :
      focused.final.heads (i.castAdd 28)=base.final.heads i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact oldH i
  refine ⟨Composition.joinedReceipt prepared focused,hj,
    (otherT 0 (by decide)).trans bt0,(otherH 0 (by decide)).trans bh0,
    (otherT 1 (by decide)).trans bt1,(otherH 1 (by decide)).trans bh1,?_,?_⟩
  · intro j
    have pick : RecoveryFocus.pick slots (slots j)=some j := RecoveryFocus.pick_slot slots slots_injective j
    change focused.final.tapes (slots j)=_ ∧ focused.final.heads (slots j)=0
    rw [ff]
    simp only [RecoveryFocus.config,pick,bodyT]
    exact ⟨True.intro,bodyH j⟩
  · change base.steps+1+focused.steps ≤ _
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationCountCold
