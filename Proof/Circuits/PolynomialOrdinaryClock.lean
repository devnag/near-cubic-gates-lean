import Proof.Circuits.PolynomialClockTotal

/-! Literal ordinary time constructibility of n^(k+2). The same program also
retains a sharper input-linear, polylogarithmic execution receipt. -/
namespace NearCubicWires.RepairOrdinary.PolynomialClock
open LocalBitMultitape RepairSource SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroTape (k : ℕ) := old k (HierarchyFromInput.field (k+2) 0)
def layout (k : ℕ) : Fin (tapes k) ≃ Fin (tapes k) := Equiv.swap (inputTape k) (zeroTape k)

theorem input_eq (k n : ℕ) : input k n =
    fun i : Fin (tapes k) => if i.val=2 then frame (List.replicate n true) else [] := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [input,Fin.addCases_left,Fin.val_castAdd,HierarchyFromInput.input]
    rfl
  · have ht := HierarchyFromInput.tapes_lower (k+2)
    simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem input_rename (k n : ℕ) : input k n ∘ (layout k).symm =
    fun i : Fin (tapes k) => if i.val=0 then frame (List.replicate n true) else [] := by
  funext i
  rw [input_eq]
  simp only [Function.comp_apply]
  have he : ((layout k).symm i).val=2 ↔ i.val=0 := by
    have heq : ((layout k).symm i).val=2 ↔ (layout k).symm i=inputTape k :=
      ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    rw [heq,Equiv.symm_apply_eq]
    change i=Equiv.swap (inputTape k) (zeroTape k) (inputTape k) ↔ i.val=0
    rw [Equiv.swap_apply_left]
    exact ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩
  simp only [he]

theorem output_fresh (k : ℕ) : (layout k (outputTape k)).val≠0 := by
  have ht := HierarchyFromInput.tapes_lower (k+2)
  have h0 : outputTape k≠inputTape k := by
    intro h; have hv := congrArg Fin.val h
    simp [outputTape,fresh,inputTape,old,HierarchyFromInput.field] at hv
    omega
  have h1 : outputTape k≠zeroTape k := by
    intro h; have hv := congrArg Fin.val h
    simp [outputTape,fresh,zeroTape,old,HierarchyFromInput.field] at hv
  rw [layout,Equiv.swap_apply_of_ne_of_ne h0 h1]
  simp [outputTape,fresh]

noncomputable def program (k : ℕ) : Program where
  tapeCount := tapes k
  stateCount := Fintype.card (RecoveryCalls.Control (sizes k))
  twoTapes := by have h := HierarchyFromInput.tapes_lower (k+2); dsimp [tapes]; omega
  machine := TapeRenaming.machine (layout k) (machine k)
  outputTape := layout k (outputTape k)
  outputFresh := output_fresh k

def sharpBudget (k n : ℕ) :=
  PolynomialClockPower.finalCoefficient (k+2)*(n+1)*(PCPResourceLedger.ell n+1)^2

noncomputable def computer (k : ℕ) : WordFunction ℕ
    (fun n => List.replicate n true) (fun n => (n^(k+2)).bits) (sharpBudget k) where
  program := program k
  realizes := by
    intro n
    obtain ⟨out,hready,hout⟩ := total_run k n
    obtain ⟨base,hb,ht,hh,hs⟩ := ClockJoin.enlarge _ _ _ _ _ hready (sharp_bound k n)
    have hrename := TapeRenaming.run_rename (layout k) (machine k) (sharpBudget k n) _ base hb
    have hi : TapeRenaming.config (layout k) (initialConfiguration (machine k) (input k n))=
        initialConfiguration (program k).machine ((program k).inputTapes (List.replicate n true)) := by
      apply configuration_ext
      · rfl
      · rfl
      · exact input_rename k n
    rw [hi] at hrename
    refine ⟨TapeRenaming.receipt (layout k) base,hrename,?_⟩
    change base.final.tapes ((layout k).symm (layout k (outputTape k)))=_
    rw [Equiv.symm_apply_apply,ht]
    exact hout

noncomputable def ordinaryClock (k : ℕ) : OrdinaryClock (fun n => n^(k+2)) where
  atLeastInput := fun n => Nat.le_self_pow (by omega) n
  polynomial := ⟨1,k+2,by omega,fun n => by simpa using Nat.pow_le_pow_left (Nat.le_succ n) (k+2)⟩
  coefficient := 32*PolynomialClockPower.finalCoefficient (k+2)
  coefficientPositive := by
    dsimp [PolynomialClockPower.finalCoefficient]
    omega
  computer := (computer k).enlargeBudget (PolynomialClockPower.ordinary_budget_bound k)

end NearCubicWires.RepairOrdinary.PolynomialClock
