import Proof.Amplification.RecoveryBoundedNativeLiteralStackRun
import Proof.Amplification.RecoveryTseitinRawIncrement

/-! The next literal's base is the current actual output address plus one.
The address scratch keeps its allocated false suffix across paid reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeAdvance
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem advance_ready (ref base C : ℕ) (hb : base ≤ ref) (hC : ref+1 ≤ C) :
    ReadyRun PCPPNativeQueryAdvance.machine (2*ref+4)
      ![ZeroPadding.pad C (List.replicate ref true),List.replicate base true,List.replicate C false]
      ![ZeroPadding.pad C (List.replicate (ref+1) true),List.replicate (ref+1) true,List.replicate C false] := by
  obtain ⟨a,ha,atapes,ah,as⟩:=PCPPNativeQueryAdvance.advance_ready ref base C hb hC
  let caps : Fin 3→ℕ:=![C,0,0]
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config PCPPNativeQueryAdvance.machine caps _ _ a ha
  have hi : ZeroPadding.config caps (initialConfiguration PCPPNativeQueryAdvance.machine
      ![List.replicate ref true,List.replicate base true,List.replicate C false])=
      initialConfiguration PCPPNativeQueryAdvance.machine
        ![ZeroPadding.pad C (List.replicate ref true),List.replicate base true,List.replicate C false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i
      · rfl
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans as⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps i) (a.final.tapes i))=_
    rw [atapes]
    funext i
    fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
  · intro i
    rw [rf]
    exact ah i

theorem erase_ready (ref C : ℕ) (hC : ref ≤ C) :
    ReadyRun (RecoveryScratchErase.resetMachine 1) (2*C+4)
      ![ZeroPadding.pad C (List.replicate ref true),List.replicate C true,List.replicate (C+1) false]
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
  have hr:=RecoveryScratchErase.erase_ready C (C+1)
    (fun _ : Fin 1=>ZeroPadding.pad C (List.replicate ref true))
    (by intro i; simp only [ZeroPadding.pad_length,List.length_replicate]; omega)
  have hi : (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>ZeroPadding.pad C (List.replicate ref true)) (fun _=>List.replicate C true))
      (fun _=>List.replicate (C+1) false))=
      ![ZeroPadding.pad C (List.replicate ref true),List.replicate C true,List.replicate (C+1) false] := by
    funext i; fin_cases i <;> rfl
  have ho : (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>List.replicate C false) (fun _=>List.replicate C true))
      (fun _=>List.replicate (max (C+1) (C+1)) false))=
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
    simp only [max_self]
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hr
  exact hr

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeAdvance
