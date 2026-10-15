import Proof.CaseAnalysis.SchedulePrepared

/-! The full cold schedule executes from the actual language word and
retains that word together with the canonically selected source length. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def loopProgram (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) :=
  RecoveryFocus.machine (core (Step.workTapes sources k D))
    (Dock.machine (Step.machine sources k D copies clock))
def machine (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (A B : Nat) :=
  Composition.machine (prepare (Step.workTapes sources k D) A B) (loopProgram sources k D copies clock)
def budget (A B : Nat) (bits : List Bool) :=
  prepareBudget A B bits+1+(bits.length*(16*CloseoutCapacity.capacity A B bits.length+67)+7)

theorem data_old {t : Nat} (native : Fin t → List Bool) (total : Nat) (i : Fin t) :
    Dock.data native total (i.castAdd 1) = native i := Fin.addCases_left i

theorem loop_input (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (C n : Nat)
    (ambient : Fin (tapes (Step.workTapes sources k D)) → List Bool)
    (hw : ∀ i : Fin (Step.workTapes sources k D),
      ambient (core (Step.workTapes sources k D) (i.castAdd 6)) = List.replicate C false)
    (hp : ∀ i, ambient (port (Step.workTapes sources k D) i) = readyPorts C n i)
    (i : Fin (Step.workTapes sources k D+6)) :
    ambient (core (Step.workTapes sources k D) i) = Dock.data (Loop.input sources k D copies clock C n 0) n i := by
  refine Fin.addCases (m := Step.tapes sources k D) (n := 1) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m := Step.workTapes sources k D) (n := 5) (fun a => ?_) (fun a => ?_) j
    · simp only [Dock.data,Loop.input,Loop.best,Step.bank,Fin.addCases_left]
      exact hw a
    · fin_cases a
      all_goals simp only [Dock.data,Loop.input,Loop.best,Step.bank,Fin.addCases_left,Fin.addCases_right]
      · exact hp 0
      · exact hp 1
      · change ambient (port (Step.workTapes sources k D) 2) = ZeroPadding.pad C []
        exact (hp 2).trans (by simp [readyPorts,ZeroPadding.pad])
      · exact hp 3
      · exact hp 4
  · fin_cases j
    simp only [Dock.data,Fin.addCases_right]
    exact hp 5

theorem schedule_run (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (A B : Nat) (bits : List Bool) (hD : 1 ≤ D)
    (hn : bits.length+3 ≤ CloseoutCapacity.capacity A B bits.length)
    (hN : 2^bits.length+3 ≤ CloseoutCapacity.capacity A B bits.length)
    (hcost : ∀ s, s ≤ bits.length → Test.budget sources k D copies clock s bits.length+1 ≤
      CloseoutCapacity.capacity A B bits.length) : ∃ out,
    ClockJoin.ReadyRun (machine sources k D copies clock A B) (budget A B bits)
      (input (Step.workTapes sources k D) bits) out ∧
    out (extra (Step.workTapes sources k D) 0) = frame bits ∧
    out (port (Step.workTapes sources k D) 2) =
      ZeroPadding.pad (CloseoutCapacity.capacity A B bits.length)
        (List.replicate (Loop.best (CloseoutLanguage.widthAt sources k clock copies D) bits.length bits.length) true) := by
  let w := Step.workTapes sources k D
  let C := CloseoutCapacity.capacity A B bits.length
  obtain ⟨a,ha,hx,hw,hp⟩ := prepare_run w A B bits
  have hloop := Dock.schedule_ready sources k D copies clock C bits.length hD hn hN hcost
  have hf := hloop.focus (core w) (core_injective w) a (loop_input sources k D copies clock C bits.length a hw hp)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ ha hf,?_,?_⟩
  · exact (install_other (core w) a _ (extra w 0) (fun j => core_extra w j 0)).trans hx
  · change install (core w) a _ (core w (((2 : Fin 5).natAdd w).castAdd 1)) = _
    rw [install_slot _ (core_injective w)]
    exact (data_old (Loop.input sources k D copies clock C bits.length bits.length) bits.length
      (Step.port sources k D 2)).trans
        (Step.bank_port sources k D C (bits.length+1) bits.length
          (Loop.best (CloseoutLanguage.widthAt sources k clock copies D) bits.length bits.length) 2)

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold
