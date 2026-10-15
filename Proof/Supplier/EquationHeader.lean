import Proof.Supplier.EquationCount
import Proof.Supplier.EquationHeaders

/-! The original framed row now supplies the exact output headers as well
as every retained loop/count/capacity input. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderCold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 52 → Fin 111 := ![42,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,44,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,50,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110]
theorem slots_injective : Function.Injective slots := by decide
def bank (j : Fin 32) : Fin 111 := (EquationCountCold.slots j).castAdd 49
theorem bank_other (j : Fin 32) (h12 : j≠12) (h14 : j≠14) (h20 : j≠20) :
    RecoveryFocus.pick slots (bank j)=none := by
  fin_cases j
  all_goals first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 49 EquationCountCold.machine
noncomputable def last := RecoveryFocus.machine slots EquationHeaders.machine
noncomputable def machine := Composition.machine first last
def values (d p g : ℕ) : Fin 3 → ℕ := ![d,p+1,2*g]
def input (d p g : ℕ) (odd : Bool) (suffix : List Bool) : Fin 111 → List Bool :=
  fun i => if i=0 then frame (EquationHeaderRead.word d p g (odd::suffix)) else []
def budget (d p g : ℕ) (odd : Bool) (suffix : List Bool) :=
  EquationCountCold.budget d p g odd suffix+1+EquationHeaders.budget (values d p g)

theorem cold_run (d p g : ℕ) (odd : Bool) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g odd suffix) (input d p g odd suffix)=some actual ∧
    actual.final.tapes 0=frame (EquationHeaderRead.word d p g (odd::suffix)) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) ∧
      actual.final.heads 1=(EquationHeaderRead.header d p g).length+1 ∧
    actual.final.tapes 110=EquationHeaderRead.header d (p+1) (2*g) ∧
      actual.final.heads 110=(EquationHeaderRead.header d (p+1) (2*g)).length ∧
    (∀ j,j≠12 → j≠14 → j≠20 →
      actual.final.tapes (bank j)=EquationCountCapacity.data8 d p g odd j ∧ actual.final.heads (bank j)=0) ∧
    actual.steps ≤ budget d p g odd suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,fields,bs⟩ := EquationCountCold.cold_run d p g odd suffix
  let prepared := TapeEmbedding.receipt (fun _ : Fin 49 => 0) (fun _ : Fin 49 => []) base
  have he := TapeEmbedding.run_embed EquationCountCold.machine (fun _ : Fin 49 => 0)
    (fun _ : Fin 49 => []) _ _ base hb
  have oldT (i : Fin 62) : prepared.final.tapes (i.castAdd 49)=base.final.tapes i := by
    change (Fin.addCases (m := 62) (n := 49) (motive := fun _ => List Bool)
      base.final.tapes (fun _ => [])) (i.castAdd 49)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin 62) : prepared.final.heads (i.castAdd 49)=base.final.heads i := by
    change (Fin.addCases (m := 62) (n := 49) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd 49)=_
    rw [Fin.addCases_left]
  obtain ⟨body,hbody,bodyT,bodyH,bodyS⟩ := EquationHeaders.headers_run (values d p g) []
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes
      (EquationHeaders.entry (values d p g) [])=Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · exact (oldH (EquationCountCold.slots 12)).trans (fields 12).2
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldH (EquationCountCold.slots 14)).trans (fields 14).2
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldH (EquationCountCold.slots 20)).trans (fields 20).2
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · intro j
      fin_cases j
      · exact (oldT (EquationCountCold.slots 12)).trans (fields 12).1
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldT (EquationCountCold.slots 14)).trans (fields 14).1
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldT (EquationCountCold.slots 20)).trans (fields 20).1
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective EquationHeaders.machine
    prepared.final.heads prepared.final.tapes _ _ body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 49 => 0) (fun _ : Fin 49 => [])
        (initialConfiguration EquationCountCold.machine (EquationCountCold.input d p g odd suffix)))=
      initialConfiguration machine (input d p g odd suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have otherT (i : Fin 62) (hn : RecoveryFocus.pick slots (i.castAdd 49)=none) :
      focused.final.tapes (i.castAdd 49)=base.final.tapes i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact oldT i
  have otherH (i : Fin 62) (hn : RecoveryFocus.pick slots (i.castAdd 49)=none) :
      focused.final.heads (i.castAdd 49)=base.final.heads i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact oldH i
  have pick : RecoveryFocus.pick slots (slots 51)=some 51 := RecoveryFocus.pick_slot slots slots_injective 51
  refine ⟨Composition.joinedReceipt prepared focused,hj,
    (otherT 0 (by decide)).trans bt0,(otherH 0 (by decide)).trans bh0,
    (otherT 1 (by decide)).trans bt1,(otherH 1 (by decide)).trans bh1,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 51)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    have ht : body.final.tapes 51=[]++EquationHeaderRead.header d (p+1) (2*g) := bodyT
    simpa only [List.nil_append] using ht
  · change focused.final.heads (slots 51)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    have hh : body.final.heads 51=([]++EquationHeaderRead.header d (p+1) (2*g)).length := bodyH
    simpa only [List.nil_append] using hh
  · intro j h12 h14 h20
    exact ⟨(otherT (EquationCountCold.slots j) (bank_other j h12 h14 h20)).trans (fields j).1,
      (otherH (EquationCountCold.slots j) (bank_other j h12 h14 h20)).trans (fields j).2⟩
  · change base.steps+1+focused.steps ≤ _
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationHeaderCold
