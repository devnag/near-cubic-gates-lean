import Proof.CaseAnalysis.ScheduleGuardedLayout

/-! Complete cold schedule continuation: the fixed onset test and refuter
request framing retain the original language address, with all costs added. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Guarded
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem continuation_run {w states fuel : Nat} (p : Machine (Cold.tapes w) states)
    (bits : List Bool) (onset C N : Nat) (native : Fin (Cold.tapes w)→List Bool)
    (hr : ClockJoin.ReadyRun p fuel (Cold.input w bits) native)
    (hx : native (Cold.extra w 0)=frame bits)
    (hN : native (Cold.port w 2)=ZeroPadding.pad C (List.replicate N true)) :
    ∃ out,ClockJoin.ReadyRun (machine p onset)
      (fuel+1+(6*onset+18)+1+(6*N+15)) (input w bits) out ∧
      out (old w (Cold.extra w 0))=frame bits ∧
      out (fresh w 4)=[decide (onset≤N)] ∧
      out (fresh w 8)=frame (List.replicate N true):=by
  let a:=install (old w) (input w bits) native
  have ha:=hr.focus (old w) (old_injective w) (input w bits) (fun i=>Fin.addCases_left i)
  have an : a (old w (Cold.port w 2))=ZeroPadding.pad C (List.replicate N true):=
    (install_slot _ (old_injective w) _ _ _).trans hN
  have ax : a (old w (Cold.extra w 0))=frame bits:=
    (install_slot _ (old_injective w) _ _ _).trans hx
  have af (j : Fin 9) : a (fresh w j)=[]:=
    (install_other _ _ _ _ (fun i=>old_fresh w i j)).trans (Fin.addCases_right j)
  have hin (i : Fin 7) : a (guardSlots w i)=OnsetGuard.input C N i:=by
    fin_cases i
    · exact an
    · exact af 0
    · exact af 1
    · exact af 2
    · exact af 3
    · exact af 4
    · exact af 5
  let b:=install (guardSlots w) a (OnsetGuard.output onset C N)
  have hb:=(OnsetGuard.guard_run onset C N).focus (guardSlots w) (guard_injective w) a hin
  have bn : b (old w (Cold.port w 2))=ZeroPadding.pad C (List.replicate N true):=by
    change install (guardSlots w) _ _ (guardSlots w 0)=_
    rw [install_slot _ (guard_injective w)]
    exact OnsetGuard.output_length onset C N
  have bf (j : Fin 9) (hj : 6≤j.val) : b (fresh w j)=[]:=
    (install_other _ _ _ _ (fun i=>guard_unused w i j hj)).trans (af j)
  have bin (i : Fin 4) : b (frameSlots w i)=Output.input C N i:=by
    fin_cases i
    · exact bn
    · exact bf 6 (by decide)
    · exact bf 7 (by decide)
    · exact bf 8 (by decide)
  obtain ⟨framed,hframed,hword⟩:=Output.output_run C N
  have hc:=hframed.focus (frameSlots w) (frame_injective w) b bin
  refine ⟨install (frameSlots w) b framed,
    ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha hb) hc,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (frame_source w)]
    exact (install_other _ _ _ _ (guard_source w)).trans ax
  · rw [install_other _ _ _ _ (frame_flag w)]
    change install (guardSlots w) _ _ (guardSlots w 5)=_
    rw [install_slot _ (guard_injective w)]
    exact OnsetGuard.output_flag onset C N
  · change install (frameSlots w) _ _ (frameSlots w 3)=_
    rw [install_slot _ (frame_injective w)]
    exact hword

theorem selected_guard (width : Nat→Nat) (n onset : Nat) (ho : 1≤onset) :
    onset≤Framed.selectedLength width n ↔
      1≤CloseoutLanguage.selectedIndex width n ∧
        onset≤2^(CloseoutLanguage.selectedIndex width n):=by
  by_cases hz:CloseoutLanguage.selectedIndex width n=0
  · unfold Framed.selectedLength
    rw [if_pos hz,hz]
    omega
  · simp only [Framed.selectedLength,if_neg hz]
    have hp:1≤CloseoutLanguage.selectedIndex width n:=by omega
    exact (and_iff_right hp).symm

end
end NearCubicWires.RepairSource.CloseoutSchedule.Guarded
