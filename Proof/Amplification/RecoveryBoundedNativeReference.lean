import Proof.Amplification.RecoveryBoundedNativeUnarySchedule
import Proof.PCP.PCPUnaryStackPush

/-! The emitted grammar literal's actual output address is base plus its
runtime polarity bit. Its unary stack entry and both reset logs are
produced by paid scans; the stack keeps its live append cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeReference
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flag_pad (negative : Bool) : ZeroPadding.pad 1 (List.replicate negative.toNat true)=[negative] := by
  cases negative <;> rfl

theorem sum_ready (base C : ℕ) (negative : Bool) (hC : base+3≤C) :
    ClockJoin.ReadyRun ClockUnarySum.machine (2*(base+negative.toNat)+6)
      ![List.replicate base true,[negative],[],List.replicate C false]
      ![List.replicate base true,[negative],List.replicate (base+negative.toNat) true,List.replicate C false] := by
  obtain ⟨a,ha,atapes,ah,as⟩:=ClockUnarySum.sum_ready base negative.toNat
  let caps : Fin 4→ℕ:=![0,1,0,C]
  obtain ⟨b,hb,bf,bs,_⟩:=ZeroPadding.run_config ClockUnarySum.machine caps _ _ a ha
  have initial : ZeroPadding.config caps (initialConfiguration ClockUnarySum.machine
      ![List.replicate base true,List.replicate negative.toNat true,[],[]])=
      initialConfiguration ClockUnarySum.machine ![List.replicate base true,[negative],[],List.replicate C false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i
      · exact ZeroPadding.pad_zero _
      · exact flag_pad negative
      · rfl
      · rfl
  rw [initial] at hb
  refine ⟨b,hb,?_,?_,bs.le.trans as⟩
  · rw [bf]
    change (fun i=>ZeroPadding.pad (caps i) (a.final.tapes i))=_
    rw [atapes]
    have hneg : negative.toNat≤1 := by cases negative <;> decide
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact flag_pad negative
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad C (List.replicate (base+negative.toNat+2) false)=List.replicate C false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · intro i
    rw [bf]
    exact ah i

theorem push_run (ref C : ℕ) (stack : List Bool) (hC : 2*ref+2≤C) :
    ∃ r,runFrom PCPUnaryStackPush.machine (4*ref+6)
      ⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
        ![List.replicate ref true,stack,List.replicate C false]⟩=some r ∧
      r.final.tapes=![List.replicate ref true,stack++(frame (List.replicate ref true)).reverse,List.replicate C false] ∧
      r.final.heads=![0,stack.length+2*ref+1,0] ∧ r.steps≤4*ref+6 := by
  obtain ⟨a,ha,atapes,ah,as⟩:=PCPUnaryStackPush.push_run ref stack
  let caps : Fin 3→ℕ:=![0,0,C]
  obtain ⟨b,hb,bf,bs,_⟩:=ZeroPadding.run_config PCPUnaryStackPush.machine caps _ _ a ha
  have initial : ZeroPadding.config caps (PCPUnaryStackPush.entry ref stack)=
      (⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
        ![List.replicate ref true,stack,List.replicate C false]⟩ : Configuration 3 6) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _
      · rfl
  rw [initial] at hb
  refine ⟨b,hb,?_,?_,bs.le.trans as.le⟩
  · rw [bf]
    change (fun i=>ZeroPadding.pad (caps i) (a.final.tapes i))=_
    rw [atapes]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad C (List.replicate (2*ref+2) false)=List.replicate C false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · rw [bf]
    exact ah

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeReference
