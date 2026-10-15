import Proof.Supplier.EquationNaturalHeader
import Proof.PCP.PCPPQueryField

/-! One runtime natural value produces and appends its exact canonical
header. The existing self-delimiting field copier supplies its own counter. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderAppend
open LocalBitMultitape RecoveryExecution RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 18 := ![14,16,17]
noncomputable def first := TapeEmbedding.machine 2 EquationNaturalHeader.machine
noncomputable def last := RecoveryFocus.machine slots (PCPPQueryField.machine true)
noncomputable def machine := Composition.machine first last
def heads (out : List Bool) (i : Fin 18) := if i=17 then out.length else 0
def tapes (n : ℕ) (out : List Bool) (i : Fin 18) :=
  if i=0 then List.replicate n true else if i=17 then out else []
noncomputable def entry (n : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,tapes n out⟩ : Configuration 18 _)
def budget (n : ℕ) := 16*n^2+72*n+12*natBitLength n+58

theorem append_run (n : ℕ) (out : List Bool) : ∃ actual,
    runFrom machine (budget n) (entry n out)=some actual ∧
    actual.final.tapes 17=out++natWord n ∧ actual.final.heads 17=(out++natWord n).length ∧
    actual.final.tapes 1=List.replicate n true ∧ actual.final.heads 1=0 ∧
    actual.steps ≤ budget n := by
  obtain ⟨made,⟨base,hb,bt,bh,bs⟩,b1,b14⟩ := EquationNaturalHeader.header_ready n
  let extraH : Fin 2 → ℕ := ![0,out.length]
  let extraT : Fin 2 → List Bool := ![[],out]
  let prepared := TapeEmbedding.receipt extraH extraT base
  have he := TapeEmbedding.run_embed EquationNaturalHeader.machine extraH extraT _ _ base hb
  have oldT (i : Fin 16) : prepared.final.tapes (i.castAdd 2)=made i := by
    change (Fin.addCases (m := 16) (n := 2) (motive := fun _ => List Bool)
      base.final.tapes extraT) (i.castAdd 2)=_
    rw [Fin.addCases_left,bt]
  have oldH (i : Fin 16) : prepared.final.heads (i.castAdd 2)=0 := by
    change (Fin.addCases (m := 16) (n := 2) (motive := fun _ => ℕ)
      base.final.heads extraH) (i.castAdd 2)=_
    rw [Fin.addCases_left]
    exact bh i
  obtain ⟨copy,hc,cf,cs⟩ := PCPPQueryField.nat_run true [] [] [] out n
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes
      (PCPPQueryField.cfg 0 ([]++natWord n++[]) ([] : List Bool).length [] 0 out)=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact oldH 14
      all_goals rfl
    · intro i; fin_cases i
      · change prepared.final.tapes 14=natWord n++[]
        rw [List.append_nil]
        exact (oldT 14).trans b14
      all_goals rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots (by decide) (PCPPQueryField.machine true)
    prepared.final.heads prepared.final.tapes _ _ copy hc
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig 4
      (TapeEmbedding.config extraH extraT (initialConfiguration EquationNaturalHeader.machine
        (EquationNaturalHeader.input n)))=entry n out := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have htime : (EquationNaturalHeader.budget n+2)+1+(2*natBitLength n+3)=budget n := by
    unfold EquationNaturalHeader.budget budget
    omega
  rw [htime] at hj
  have pick (i : Fin 3) : RecoveryFocus.pick slots (slots i)=some i :=
    RecoveryFocus.pick_slot slots (by decide) i
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 2)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick,cf,PCPPQueryField.payload,PCPPQueryField.cfg,
      PCPPQueryField.selected,ite_true]
    rfl
  · change focused.final.heads (slots 2)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick,cf,PCPPQueryField.payload,PCPPQueryField.cfg,
      PCPPQueryField.selected,ite_true]
    rfl
  · change focused.final.tapes 1=_
    rw [ff]
    change prepared.final.tapes 1=_
    exact (oldT 1).trans b1
  · change focused.final.heads 1=0
    rw [ff]
    change prepared.final.heads 1=0
    exact oldH 1
  · change base.steps+1+focused.steps ≤ _
    rw [fs,cs]
    omega

end NearCubicWires.RepairOrdinary.EquationHeaderAppend
