import Proof.Hierarchy.CompetitorDimensionBootstrap

/-! Actual production of the scalar width and workspace-capacity drivers
from the runtime short-width tape. No binary or unary capacity is supplied.
The finite constant 4096 is printed, and all products allocate their output. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDimensions
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 13) : Fin 19 := i.castAdd 6
def extendTapes (tapes : Fin 13 → List Bool) : Fin 19 → List Bool :=
  Fin.addCases (m := 13) (n := 6) (motive := fun _ => List Bool) tapes (fun _ => [])
def input (b : ℕ) := extendTapes (bootstrapInput b)
def squareSlots : Fin 4 → Fin 19 := ![9,11,13,14]
def wideSlots : Fin 4 → Fin 19 := ![10,3,15,16]
def capacitySlots : Fin 4 → Fin 19 := ![13,5,17,18]
noncomputable def bootProgram := RecoveryFocus.machine native bootstrapProgram
noncomputable def squareProgram := RecoveryFocus.machine squareSlots ClockUnaryProduct.machine
noncomputable def wideProgram := RecoveryFocus.machine wideSlots ClockUnaryProduct.machine
noncomputable def capacityProgram := RecoveryFocus.machine capacitySlots ClockUnaryProduct.machine
noncomputable def productsProgram := Composition.machine squareProgram (Composition.machine wideProgram capacityProgram)
noncomputable def machine := Composition.machine bootProgram productsProgram
def budget (b : ℕ) := bootstrapBudget b+1+(WilliamsUnaryProduct.budget (b+1) (b+1)+1+
  (WilliamsUnaryProduct.budget (b+1) 2+1+WilliamsUnaryProduct.budget ((b+1)*(b+1)) 4096))

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 19 => a.val) h)
theorem unary_ready (d e : ℕ) : ClockJoin.ReadyRun ClockUnaryProduct.machine
    (WilliamsUnaryProduct.budget d e) (WilliamsUnaryProduct.input d e) (WilliamsUnaryProduct.output d e) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready d e
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem dimensions_run (b : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget b) (input b) out ∧
    out 0=List.replicate b true ∧ out 15=List.replicate (CompetitorRationalDecision.width b) true ∧
    out 17=List.replicate (CompetitorReusableDecision.capacity b) true := by
  obtain ⟨boot,hboot,h0,h3,h5,h9,h10,h11⟩ := bootstrap_run b
  have hin : ∀ i,input b (native i)=bootstrapInput b i := by intro i; simp [input,extendTapes,native]
  have hb := bounded_focus native native_injective _ _ _ hboot (input b) hin
  have hbootOutput : install native (input b) boot=extendTapes boot := by
    funext i
    refine Fin.addCases (m := 13) (n := 6) ?_ ?_ i
    · intro j
      simp only [extendTapes,Fin.addCases_left]
      exact install_slot native native_injective _ boot j
    · intro j
      simp only [extendTapes,Fin.addCases_right]
      have hn : ∀ k,native k≠j.natAdd 13 := by
        intro k hk
        have hv := congrArg (fun a : Fin 19 => a.val) hk
        change k.val=13+j.val at hv
        omega
      exact (install_other native (input b) boot (j.natAdd 13) hn).trans (by simp [input,extendTapes])
  rw [hbootOutput] at hb
  let initial := extendTapes boot
  have hiSquare : ∀ i,initial (squareSlots i)=WilliamsUnaryProduct.input (b+1) (b+1) i := by
    intro i
    fin_cases i
    · exact h9
    · exact h11
    · rfl
    · rfl
  let squared := install squareSlots initial (WilliamsUnaryProduct.output (b+1) (b+1))
  have hsquared := bounded_focus squareSlots (by decide) _ _ _ (unary_ready (b+1) (b+1)) initial hiSquare
  have hiWide : ∀ i,squared (wideSlots i)=WilliamsUnaryProduct.input (b+1) 2 i := by
    intro i
    fin_cases i
    · exact (install_other squareSlots _ _ 10 (by decide)).trans h10
    · exact (install_other squareSlots _ _ 3 (by decide)).trans h3
    · exact install_other squareSlots _ _ 15 (by decide)
    · exact install_other squareSlots _ _ 16 (by decide)
  let widened := install wideSlots squared (WilliamsUnaryProduct.output (b+1) 2)
  have hwidened := bounded_focus wideSlots (by decide) _ _ _ (unary_ready (b+1) 2) squared hiWide
  have hiCapacity : ∀ i,widened (capacitySlots i)=WilliamsUnaryProduct.input ((b+1)*(b+1)) 4096 i := by
    intro i
    fin_cases i
    · exact (install_other wideSlots _ _ 13 (by decide)).trans
        (install_slot squareSlots (by decide) _ (WilliamsUnaryProduct.output (b+1) (b+1)) 2)
    · exact (install_other wideSlots _ _ 5 (by decide)).trans
        ((install_other squareSlots _ _ 5 (by decide)).trans h5)
    · exact (install_other wideSlots _ _ 17 (by decide)).trans (install_other squareSlots _ _ 17 (by decide))
    · exact (install_other wideSlots _ _ 18 (by decide)).trans (install_other squareSlots _ _ 18 (by decide))
  let out := install capacitySlots widened (WilliamsUnaryProduct.output ((b+1)*(b+1)) 4096)
  have hcapacity := bounded_focus capacitySlots (by decide) _ _ _ (unary_ready ((b+1)*(b+1)) 4096) widened hiCapacity
  have hlast := ClockJoin.join wideProgram capacityProgram _ _ _ _ _ hwidened hcapacity
  have hproducts := ClockJoin.join squareProgram (Composition.machine wideProgram capacityProgram) _ _ _ _ _ hsquared hlast
  have hall := ClockJoin.join bootProgram productsProgram _ _ _ _ _ hb hproducts
  refine ⟨out,hall,?_,?_,?_⟩
  · exact (install_other capacitySlots _ _ 0 (by decide)).trans
      ((install_other wideSlots _ _ 0 (by decide)).trans ((install_other squareSlots _ _ 0 (by decide)).trans h0))
  · have ht : out 15=WilliamsUnaryProduct.output (b+1) 2 2 :=
      (install_other capacitySlots widened (WilliamsUnaryProduct.output ((b+1)*(b+1)) 4096) 15 (by decide)).trans
        (install_slot wideSlots (by decide) squared (WilliamsUnaryProduct.output (b+1) 2) 2)
    have hwidth : (b+1)*2=CompetitorRationalDecision.width b := by unfold CompetitorRationalDecision.width; omega
    apply ht.trans
    change List.replicate ((b+1)*2) true=List.replicate (CompetitorRationalDecision.width b) true
    rw [hwidth]
  · change install capacitySlots widened (WilliamsUnaryProduct.output ((b+1)*(b+1)) 4096) (capacitySlots 2)=_
    have ht := install_slot capacitySlots (by decide) widened (WilliamsUnaryProduct.output ((b+1)*(b+1)) 4096) 2
    have hcapacity : (b+1)*(b+1)*4096=CompetitorReusableDecision.capacity b := by
      unfold CompetitorReusableDecision.capacity
      ring
    apply ht.trans
    change List.replicate ((b+1)*(b+1)*4096) true=List.replicate (CompetitorReusableDecision.capacity b) true
    rw [hcapacity]

theorem budget_bound (b : ℕ) : budget b≤10*CompetitorReusableDecision.capacity b := by
  unfold budget bootstrapBudget WilliamsUnaryProduct.budget CompetitorReusableDecision.capacity
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorDimensions
