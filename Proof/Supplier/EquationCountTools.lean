import Proof.Supplier.EquationWeightCount
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.UWalkUnary

/-! Exact standard unary interfaces used by the row's physical count caller. -/
namespace NearCubicWires.RepairOrdinary.EquationCountTools
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem template_source (n : ℕ) : UWalkUnary.source (n+2) n=UnaryTemplate.tape n := by
  have hn : n+2-(CompareMachine.word n).length=1 := by
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega
  rw [UWalkUnary.source,ZeroPadding.pad,hn]
  rfl

theorem word_source (n : ℕ) : UWalkUnary.source (n+1) n=CompareMachine.word n := by
  simp [UWalkUnary.source,ZeroPadding.pad,CompareMachine.word]

theorem template_ready (sentinel extra : Bool) (n : ℕ) :
    ClockJoin.ReadyRun (UWalkUnary.machine sentinel extra) (2*n+6)
      ![UnaryTemplate.tape n,[],[]]
      ![UnaryTemplate.tape n,UWalkUnary.output sentinel extra n,List.replicate (n+2) false] := by
  simpa only [UWalkUnary.input,UWalkUnary.result,template_source] using
    UWalkUnary.ready sentinel extra (n+2) n

theorem word_ready (sentinel extra : Bool) (n : ℕ) :
    ClockJoin.ReadyRun (UWalkUnary.machine sentinel extra) (2*n+6)
      ![CompareMachine.word n,[],[]]
      ![CompareMachine.word n,UWalkUnary.output sentinel extra n,List.replicate (n+2) false] := by
  simpa only [UWalkUnary.input,UWalkUnary.result,word_source] using
    UWalkUnary.ready sentinel extra (n+1) n

theorem product_ready (d e : ℕ) :
    ClockJoin.ReadyRun ClockUnaryProduct.machine (2*(d*(2*e+3)+2)+2)
      ![List.replicate d true,CompareMachine.word e,[],[]]
      ![List.replicate d true,CompareMachine.word e,List.replicate (d*e) true,
        List.replicate (d*(2*e+3)+2) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run d e
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate d true,false::List.replicate e true,[]] (fun _ : Fin 1 => []))=
      (![List.replicate d true,CompareMachine.word e,[],[]] : Fin 4 → List Bool) := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end NearCubicWires.RepairOrdinary.EquationCountTools
