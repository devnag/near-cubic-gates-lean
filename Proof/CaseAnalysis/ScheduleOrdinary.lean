import Proof.CaseAnalysis.ScheduleFramed
import Proof.MachineModel.OrdinaryOracleCompose

/-! One ordinary word program computes the same canonical source length.
The static input-port renaming changes no execution cost. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Ordinary
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def source (w : Nat) := Framed.old w (Cold.extra w 0)
def zero (w : Nat) : Fin (Framed.tapes w) := ⟨0,by dsimp [Framed.tapes,Cold.tapes]; omega⟩
def layout (w : Nat) := Equiv.swap (source w) (zero w)

theorem input_eq (w : Nat) (bits : List Bool) : Framed.input w bits =
    fun i => if i.val=w+6 then frame bits else [] := by
  funext i
  refine Fin.addCases (m := Cold.tapes w) (n := 3) (fun j => ?_) (fun j => ?_) i
  · simp only [Framed.input,Fin.addCases_left,Fin.val_castAdd,Cold.input]
    rfl
  · simp only [Framed.input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by dsimp [Cold.tapes]; omega)]

theorem input_rename (w : Nat) (bits : List Bool) : Framed.input w bits ∘ (layout w).symm =
    fun i => if i.val=0 then frame bits else [] := by
  funext i
  rw [input_eq]
  simp only [Function.comp_apply]
  have he : ((layout w).symm i).val=w+6 ↔ i.val=0 := by
    have hi : ((layout w).symm i).val=w+6 ↔ (layout w).symm i=source w :=
      ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    rw [hi,Equiv.symm_apply_eq]
    change i=Equiv.swap (source w) (zero w) (source w) ↔ i.val=0
    rw [Equiv.swap_apply_left]
    exact ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩
  simp only [he]

theorem output_fresh (w : Nat) : (layout w (Framed.fresh w 2)).val ≠ 0 := by
  have h0 : Framed.fresh w 2 ≠ source w := by
    intro h
    have hv := congrArg Fin.val h
    simp [Framed.fresh,source,Framed.old,Cold.extra,Cold.tapes] at hv
  have h1 : Framed.fresh w 2 ≠ zero w := by
    intro h
    have hv := congrArg Fin.val h
    simp [Framed.fresh,zero,Cold.tapes] at hv
  rw [layout,Equiv.swap_apply_of_ne_of_ne h0 h1]
  simp [Framed.fresh,Cold.tapes]

def ports (w : Nat) : Ports (Framed.tapes w) where
  twoTapes := by dsimp [Framed.tapes,Cold.tapes]; omega
  outputTape := layout w (Framed.fresh w 2)
  outputFresh := output_fresh w
  queryTape := layout w (Framed.fresh w 2)
  queryFresh := output_fresh w
def machine (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (A B : Nat) :=
  TapeRenaming.machine (layout (Step.workTapes sources k D)) (Framed.machine sources k D copies clock A B)
def program (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (A B : Nat) :=
  (ports (Step.workTapes sources k D)).program (ordinary (machine sources k D copies clock A B))

theorem ordinary_of_ready {w states fuel : Nat} (p : Machine (Framed.tapes w) states)
    (bits answer : List Bool) (out : Fin (Framed.tapes w) → List Bool)
    (ready : ClockJoin.ReadyRun p fuel (Framed.input w bits) out)
    (hout : out (Framed.fresh w 2) = frame answer) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat
      ((ports w).program (ordinary (TapeRenaming.machine (layout w) p))) bits answer fuel := by
  obtain ⟨r,hr,ht,_hh,hs⟩ := ready
  have renamed := TapeRenaming.run_rename (layout w) p fuel _ r hr
  have hi : TapeRenaming.config (layout w) (initialConfiguration p (Framed.input w bits)) =
      initialConfiguration (TapeRenaming.machine (layout w) p)
        (((ports w).program (ordinary (TapeRenaming.machine (layout w) p))).base.inputTapes bits) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact input_rename w bits
  rw [hi] at renamed
  refine ⟨r.steps,(TapeRenaming.receipt (layout w) r).final,hs,
    ordinary_trace (ports w) (TapeRenaming.machine (layout w) p) _ _ _ renamed,?_,?_⟩
  · exact (prefix_of_run p fuel _ r hr).2
  · change r.final.tapes ((layout w).symm (layout w (Framed.fresh w 2))) = _
    rw [Equiv.symm_apply_apply,ht]
    exact hout

theorem exists_program (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) :
    ∃ C E : Nat, ∃ p : OrdinaryOracleProgram, ∀ bits : List Bool,
      OrdinaryOracleRuns RecoveryOracle.correctedSat p bits
        (List.replicate (Framed.selectedLength (CloseoutLanguage.widthAt sources k clock copies D) bits.length) true)
        (C*(2^bits.length+1)^E) := by
  obtain ⟨A,B,hrun⟩ := Framed.exists_framed sources k D copies clock hD
  refine ⟨Framed.coefficient A B,A+1,program sources k D copies clock A B,?_⟩
  intro bits
  obtain ⟨out,hr,_hx,hout⟩ := hrun bits
  exact ordinary_of_ready _ bits _ out hr hout

end
end NearCubicWires.RepairSource.CloseoutSchedule.Ordinary
