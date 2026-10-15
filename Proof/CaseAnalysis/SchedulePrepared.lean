import Proof.CaseAnalysis.CloseoutScheduleColdMetadata

/-! Complete cold capacity, metadata and initial workspace preparation from
one actual framed input. No prepared schedule field is assumed. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def prepare (w A B : Nat) :=
  Composition.machine (Composition.machine (capacityProgram w A B) (metadataProgram w)) (clearProgram w)
def prepareBudget (A B : Nat) (bits : List Bool) :=
  CloseoutCapacity.budget A B bits+1+(8*bits.length+30)+1+(2*CloseoutCapacity.capacity A B bits.length+4)
def readyPorts (C n : Nat) : Fin 6 → List Bool :=
  ![UnaryTemplate.tape 1,UnaryTemplate.tape n,List.replicate C false,
    List.replicate C true,List.replicate (C+1) false,CompareMachine.word n]

theorem prepare_run (w A B : Nat) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (prepare w A B) (prepareBudget A B bits) (input w bits) out ∧
    out (extra w 0) = frame bits ∧
    (∀ i : Fin w, out (core w (i.castAdd 6)) = List.replicate (CloseoutCapacity.capacity A B bits.length) false) ∧
    (∀ i : Fin 6, out (port w i) = readyPorts (CloseoutCapacity.capacity A B bits.length) bits.length i) := by
  let C := CloseoutCapacity.capacity A B bits.length
  obtain ⟨a,ha,hC,hx,hcore,he⟩ := capacity_run w A B bits
  obtain ⟨b,hb,bf,bw,bp⟩ := metadata_run w bits a hx hcore he
  have bbest : b (port w 2) = [] := (bp 2 (by decide)).trans
    (hcore ((2 : Fin 6).natAdd w) (by change w+2 ≠ w+3; omega))
  have bdriver : b (port w 3) = List.replicate C true := (bp 3 (by decide)).trans hC
  have blog : b (port w 4) = [] := (bp 4 (by decide)).trans
    (hcore ((4 : Fin 6).natAdd w) (by change w+4 ≠ w+3; omega))
  obtain ⟨c,hc,cw,cb,cd,cl,cp,ce⟩ := clear_run w C b bw bbest bdriver blog
  refine ⟨c,ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha hb) hc,?_,cw,?_⟩
  · rw [ce 0]
    exact bf 0
  · intro i
    fin_cases i
    · exact (cp 0 (by decide)).trans (bf 6)
    · exact (cp 1 (by decide)).trans (bf 4)
    · exact cb
    · exact cd
    · exact cl
    · exact (cp 5 (by decide)).trans (bf 1)

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold
