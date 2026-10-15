import Proof.Amplification.RecoveryBoundedNativeUnaryOriginal
import Proof.PCP.PCPUnaryStackPop

/-! Pop a saved original compiler reference into reusable allocated storage.
The consumed stack suffix is actually erased, and its live cursor is kept. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pop_run (ref C z : ℕ) (pre : List Bool) (hC : 2*ref+2 ≤ C) :
    ∃ r, runFrom PCPUnaryStackPop.machine (8*ref+9)
      ⟨PCPUnaryStackPop.machine.start,![pre.length+2*ref+1,0,0,0,0],
        ![pre++(frame (List.replicate ref true)).reverse++List.replicate z false,
          List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false]⟩=some r ∧
      r.final.heads=![pre.length,0,0,0,0] ∧
      r.final.tapes=![pre++List.replicate (2*ref+1+z) false,
        ZeroPadding.pad C (frame (List.replicate ref true)),List.replicate C false,
        ZeroPadding.pad C (List.replicate ref true),List.replicate C false] ∧ r.steps=8*ref+9 := by
  obtain ⟨a,ha,atapes,ah,as⟩:=PCPUnaryStackPop.pop_run ref pre z
  let caps : Fin 5→ℕ:=![0,C,C,C,C]
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config PCPUnaryStackPop.machine caps _ _ a ha
  have hi : ZeroPadding.config caps (PCPUnaryStackPop.entry ref pre z)=
      (⟨PCPUnaryStackPop.machine.start,![pre.length+2*ref+1,0,0,0,0],
        ![pre++(frame (List.replicate ref true)).reverse++List.replicate z false,
          List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false]⟩ : Configuration 5 _) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i
      · change pre.length+(frame (List.replicate ref true)).length=pre.length+2*ref+1
        simp [frame_length,Nat.add_assoc]
      all_goals rfl
    · funext i
      fin_cases i
      · exact ZeroPadding.pad_zero _
      all_goals rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans as⟩
  · rw [rf]
    exact ah
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps i) (a.final.tapes i))=_
    rw [atapes]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad C (List.replicate (2*ref+2) false)=List.replicate C false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
    · rfl
    · change ZeroPadding.pad C (List.replicate ref false)=List.replicate C false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
