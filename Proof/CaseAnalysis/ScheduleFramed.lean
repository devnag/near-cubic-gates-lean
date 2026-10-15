import Proof.CaseAnalysis.ScheduleOutput

/-! The cold canonical schedule returns an ordinary framed unary request.
Its original input is retained for the final requested language bit. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Framed
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (w : Nat) := Cold.tapes w+3
def old (w : Nat) (i : Fin (Cold.tapes w)) : Fin (tapes w) := i.castAdd 3
def fresh (w : Nat) (i : Fin 3) : Fin (tapes w) := i.natAdd (Cold.tapes w)
def outputSlots (w : Nat) : Fin 4 → Fin (tapes w) :=
  ![old w (Cold.port w 2),fresh w 0,fresh w 1,fresh w 2]
def input (w : Nat) (bits : List Bool) : Fin (tapes w) → List Bool :=
  Fin.addCases (Cold.input w bits) (fun _ : Fin 3 => [])
def selectedLength (width : Nat → Nat) (n : Nat) :=
  if CloseoutLanguage.selectedIndex width n = 0 then 0 else 2^(CloseoutLanguage.selectedIndex width n)

theorem old_injective (w : Nat) : Function.Injective (old w) := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes w) => i.val) h)
theorem old_fresh (w : Nat) (i : Fin (Cold.tapes w)) (j : Fin 3) : old w i ≠ fresh w j := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  change i.val = Cold.tapes w+j.val at hv
  omega
theorem output_injective (w : Nat) : Function.Injective (outputSlots w) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;>
    simp [outputSlots,old,fresh,Cold.port,Cold.core,Cold.tapes] at hv ⊢
  omega
theorem output_source (w : Nat) (i : Fin 4) :
    outputSlots w i ≠ old w (Cold.extra w 0) := by
  intro h
  have hv := congrArg Fin.val h
  fin_cases i <;>
    simp [outputSlots,old,fresh,Cold.port,Cold.core,Cold.extra,Cold.tapes] at hv
theorem selectedLength_bound (width : Nat → Nat) (n : Nat) : selectedLength width n ≤ 2^n := by
  unfold selectedLength
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right (by decide) (CloseoutLanguage.selectedIndex_le width n)

def first (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (A B : Nat) :=
  RecoveryFocus.machine (old (Step.workTapes sources k D)) (Cold.machine sources k D copies clock A B)
def second (w : Nat) := RecoveryFocus.machine (outputSlots w) Output.machine
def machine (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (A B : Nat) :=
  Composition.machine (first sources k D copies clock A B) (second (Step.workTapes sources k D))
def coefficient (A B : Nat) := Cold.coefficient A B+22

theorem exists_framed (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) :
    ∃ A B : Nat, ∀ bits : List Bool, ∃ out,
      ClockJoin.ReadyRun (machine sources k D copies clock A B)
        (coefficient A B*(2^bits.length+1)^(A+1))
        (input (Step.workTapes sources k D) bits) out ∧
      out (old (Step.workTapes sources k D) (Cold.extra (Step.workTapes sources k D) 0)) = frame bits ∧
      out (fresh (Step.workTapes sources k D) 2) = frame
        (List.replicate (selectedLength (CloseoutLanguage.widthAt sources k clock copies D) bits.length) true) := by
  obtain ⟨A,B,hrun⟩ := Cold.exists_schedule sources k D copies clock hD
  refine ⟨A,B,?_⟩
  intro bits
  let w := Step.workTapes sources k D
  let N := selectedLength (CloseoutLanguage.widthAt sources k clock copies D) bits.length
  let C := CloseoutCapacity.capacity A B bits.length
  obtain ⟨out,hr,hx,hN⟩ := hrun bits
  let a := install (old w) (input w bits) out
  have ha := hr.focus (old w) (old_injective w) (input w bits) (fun i => Fin.addCases_left i)
  have hsource : a (old w (Cold.port w 2)) = ZeroPadding.pad C (List.replicate N true) :=
    (install_slot (old w) (old_injective w) (input w bits) out (Cold.port w 2)).trans hN
  have hfresh (i : Fin 3) : a (fresh w i) = [] :=
    (install_other (old w) (input w bits) out (fresh w i) (fun j => old_fresh w j i)).trans
      (Fin.addCases_right i)
  obtain ⟨framed,hframed,hvalue⟩ := Output.output_run C N
  have hb := hframed.focus (outputSlots w) (output_injective w) a (by
    intro i; fin_cases i
    · exact hsource
    · exact hfresh 0
    · exact hfresh 1
    · exact hfresh 2)
  refine ⟨install (outputSlots w) a framed,?_,?_,?_⟩
  · apply ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha hb)
    let P := (2^bits.length+1)^(A+1)
    have hp : 2^bits.length+1 ≤ P := Nat.le_self_pow (by omega) _
    have hNbound := selectedLength_bound (CloseoutLanguage.widthAt sources k clock copies D) bits.length
    change N ≤ 2^bits.length at hNbound
    change Cold.coefficient A B*P+1+(6*N+15) ≤ coefficient A B*P
    unfold coefficient
    nlinarith
  · exact (install_other (outputSlots w) a framed (old w (Cold.extra w 0)) (output_source w)).trans
      ((install_slot (old w) (old_injective w) (input w bits) out (Cold.extra w 0)).trans hx)
  · exact (install_slot (outputSlots w) (output_injective w) a framed 3).trans hvalue

end
end NearCubicWires.RepairSource.CloseoutSchedule.Framed
