import Proof.MachineModel.UWholeChecked
import Proof.MachineModel.UAcceptanceCarrier

/-! One fixed ordinary verifier, with a control-state acceptance gate and
the actual all-input dyadic clock. All work starts on ordinary input tapes. -/
namespace NearCubicWires.RepairOrdinary.UWhole
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def verifier : Verifier := UAcceptanceCarrier.verifier checkedMachine (by decide) 176
def time := UAggregateClock.time
def literalInput (t : ℕ) (raw witness : List Bool) : Fin t → List Bool := fun i =>
  if i.val=0 then frame raw else if i.val=1 then frame witness else []
def extendInput {t : ℕ} (u : ℕ) (tapes : Fin t → List Bool) : Fin (t+u) → List Bool :=
  fun i => Fin.addCases tapes (fun _ : Fin u => []) i

theorem extend_input {t u : ℕ} (ht : 2≤t) (raw witness : List Bool) :
    extendInput u (literalInput t raw witness)=
      literalInput (t+u) raw witness := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [extendInput,Fin.addCases_left,literalInput,Fin.val_castAdd]
    rfl
  · have h0 : t+j.val≠0 := by omega
    have h1 : t+j.val≠1 := by omega
    simp only [extendInput,Fin.addCases_right,literalInput,Fin.val_natAdd,if_neg h0,if_neg h1]

theorem input_eq (raw witness : List Bool) : input raw witness=verifier.inputTapes raw witness := by
  change input raw witness=literalInput 178 raw witness
  change extendInput 20 (extendInput 1 (extendInput 18 (extendInput 42
    (extendInput 16 (extendInput 12 (extendInput 19 (literalInput 50 raw witness))))))) =
    literalInput 178 raw witness
  rw [extend_input (by decide : 2≤50),extend_input (by decide : 2≤69),
    extend_input (by decide : 2≤81),extend_input (by decide : 2≤97),
    extend_input (by decide : 2≤139),extend_input (by decide : 2≤157),
    extend_input (by decide : 2≤158)]

theorem budget_le_time (raw : List Bool) : checkedBudget raw+2≤time raw.length := by
  apply (show checkedBudget raw+2≤UAggregateClock.fuel raw.length from ?_).trans
    (UAggregateClock.fuel_le_time raw.length)
  dsimp [checkedBudget,UAggregateClock.fuel,UEmission.budget]
  omega

theorem whole_run (raw witness : List Bool) :
    ∃ r,run verifier.machine (time raw.length) (verifier.inputTapes raw witness)=some r ∧
      r.steps≤time raw.length ∧
      (verifier.accepting r.final.control=true ↔ UEmission.Accepted raw witness) := by
  obtain ⟨r,hr,hsteps,_,hmeaning⟩ := checked_run raw witness
  rw [input_eq raw witness] at hr
  obtain ⟨hjoined,haccept⟩ := UAcceptanceCarrier.verifier_run checkedMachine (by decide) 176
    (checkedBudget raw) raw witness r hr
  have hb := budget_le_time raw
  let result := UAcceptanceCarrier.receipt (176 : Fin 178) r
  have hmore := run_moreFuel verifier.machine (checkedBudget raw+2)
    (time raw.length-(checkedBudget raw+2)) (verifier.inputTapes raw witness) result hjoined
  rw [Nat.add_sub_of_le hb] at hmore
  have hs : result.steps=r.steps+2 := (UAcceptanceCarrier.receipt_fields (176 : Fin 178) r).2.2.1
  refine ⟨result,hmore,by rw [hs]; omega,?_⟩
  exact (congrArg (fun b : Bool => b=true) haccept).to_iff.trans hmeaning

theorem acceptsAt_iff (raw witness : List Bool) :
    verifier.acceptsAt (time raw.length) raw witness ↔ UEmission.Accepted raw witness := by
  obtain ⟨r,hr,_,hm⟩ := whole_run raw witness
  constructor
  · rintro ⟨r',hr',ha⟩
    have he : r'=r := Option.some.inj (hr'.symm.trans hr)
    exact hm.mp (he ▸ ha)
  · exact fun h => ⟨r,hr,hm.mpr h⟩

theorem accepts_iff (raw witness : List Bool) :
    verifier.accepts raw witness ↔ UEmission.Accepted raw witness := by
  obtain ⟨r,hr,_,_,hm⟩ := checked_run raw witness
  rw [input_eq raw witness] at hr
  exact (UAcceptanceCarrier.accepts_transfer checkedMachine (by decide) 176
    (checkedBudget raw) raw witness r hr).trans hm

end NearCubicWires.RepairOrdinary.UWhole
