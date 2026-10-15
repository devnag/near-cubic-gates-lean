import Proof.Amplification.RecoveryMarkerSaveCalls

/-! Physical marker polarity retention and final result writes. The
polarity survives later prefix-literal sign checks in a distinct cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerFlags
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flat (x : State) : State := {x with outer:={x.outer with result:=x.inner.data.flag}}
def answered (x : State) (bit : Bool) : State := {x with inner:={x.inner with present:=bit}}
def flatMachine := RecoveryBankPair.flagMachine (56 : Fin 57) 23
def answerMachine (bit : Bool) : Machine 57 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=28 then some bit else none,fun _=>.stay⟩ else none

theorem result_tapes (s : RecoveryClauseState.State) (bit : Bool) :
    ({s with result:=bit} : RecoveryClauseState.State).tapes=Function.update s.tapes 27 [bit] := by
  have h : (fun _ : Fin 1=>[bit])=Function.update (fun _ : Fin 1=>[s.result]) 0 [bit] := by
    funext i; fin_cases i; rfl
  change Fin.addCases (m:=24) (n:=4) (motive:=fun _=>List Bool) s.core
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) s.fields (fun _=>[bit]))=_
  rw [h,bank_update_right,bank_update_right]
  rfl

theorem flat_tapes (x : State) : (flat x).tapes=Function.update x.tapes 56 [x.inner.data.flag] := by
  change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool) x.inner.tapes
    ({x.outer with result:=x.inner.data.flag} : RecoveryClauseState.State).tapes=_
  rw [result_tapes,bank_update_right]
  rfl

theorem answered_tapes (x : State) (bit : Bool) : (answered x bit).tapes=Function.update x.tapes 28 [bit] := by
  have h : (fun _ : Fin 1=>[bit])=Function.update (fun _ : Fin 1=>[x.inner.present]) 0 [bit] := by
    funext i; fin_cases i; rfl
  change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) x.inner.data.tapes (fun _=>[bit])) x.outer.tapes=_
  rw [h,bank_update_right,bank_update_left]
  rfl

theorem flat_ready (x : State) : ReadyRun flatMachine 1 x.tapes (flat x).tapes := by
  have h := RecoveryBankPair.flag_run (56 : Fin 57) 23 (fun _=>0) x.tapes
    x.outer.result x.inner.data.flag rfl rfl rfl rfl
  obtain ⟨r,hr,hs,hh,ht⟩ := h
  refine ⟨r,hr,ht.trans (flat_tapes x).symm,?_,hs⟩
  intro i
  rw [hh]

theorem answer_ready (x : State) (bit : Bool) : ReadyRun (answerMachine bit) 1 x.tapes (answered x bit).tapes := by
  have h : step (answerMachine bit) (initialConfiguration (answerMachine bit) x.tapes)=
      some ((answered x bit).cfg 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · change _=(answered x bit).tapes
      rw [answered_tapes]
      funext i
      by_cases hi : i=28
      · subst i
        change writeTapeBit [x.inner.present] 0 bit=[bit]
        rfl
      · simp only [applyAction,if_neg hi,Function.update_of_ne hi]
        rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,by intro i; rw [hf]; rfl,hs⟩

theorem flat_valid (x : State) (hx : x.Valid) : (flat x).Valid := hx
theorem answered_valid (x : State) (bit : Bool) (hx : x.Valid) : (answered x bit).Valid := hx

end NearCubicWires.RepairOrdinary.RecoveryMarkerFlags
