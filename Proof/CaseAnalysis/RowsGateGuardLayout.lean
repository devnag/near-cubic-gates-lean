import Proof.CaseAnalysis.RowsGateCounts

/-! The exact all-raw gate worker retains the already paid source-domain
template beside its bank. Only its two count ports are selected by the
small arity guard; the framed native request is left in place. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads : Fin 3 → ℕ := ![1,0,0]
def extraData (core : ℕ) : Fin 3 → List Bool := ![UnaryTemplate.tape core,[],[]]
def heads : Fin 1038 → ℕ := Fin.addCases (m := 1035) (n := 3) (motive := fun _ => ℕ)
  (fun _ => 0) extraHeads
def extend (core : ℕ) (old : Fin 1035 → List Bool) : Fin 1038 → List Bool :=
  Fin.addCases (m := 1035) (n := 3) (motive := fun _ => List Bool) old (extraData core)
def input (core : ℕ) (bits : List Bool) := extend core (CloseoutRowsGateCold.input bits)
def slots : Fin 5 → Fin 1038 := ![368,861,1035,1036,1037]
theorem injective : Function.Injective slots := by decide
noncomputable def first (compressed : Bool) := TapeEmbedding.machine 3 (CloseoutRowsGateCold.actualMachine compressed)
noncomputable def second := RecoveryFocus.machine slots CloseoutRowsGateCounts.machine
noncomputable def machine (compressed : Bool) :=
  CloseoutRowsGateColdPair.machine (first compressed) second (fun bits => bits 1018)
def budget (bits : List Bool) := CloseoutRowsGateRawRun.budget bits+1+(4*bits.length+12)+1

theorem old_port (core : ℕ) (old : Fin 1035 → List Bool) (i : Fin 1035) :
    extend core old (i.castAdd 3)=old i := by simp only [extend,Fin.addCases_left]
theorem new_port (core : ℕ) (old : Fin 1035 → List Bool) (i : Fin 3) :
    extend core old (i.natAdd 1035)=extraData core i := by simp only [extend,Fin.addCases_right]
theorem selected_heads (i : Fin 5) : heads (slots i)=CloseoutRowsGateCounts.heads i := by
  fin_cases i <;> rfl

theorem first_run (compressed : Bool) (core : ℕ) (bits : List Bool) (out : Fin 1035 → List Bool)
    (h : ClockJoin.ReadyRun (CloseoutRowsGateCold.actualMachine compressed)
      (CloseoutRowsGateRawRun.budget bits) (CloseoutRowsGateCold.input bits) out) :
    ReadyAt (first compressed) (CloseoutRowsGateRawRun.budget bits) heads (input core bits) (extend core out) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := h
  have run := TapeEmbedding.run_embed (CloseoutRowsGateCold.actualMachine compressed)
    extraHeads (extraData core) _ _ r hr
  refine ⟨TapeEmbedding.receipt extraHeads (extraData core) r,run,?_,?_,rs⟩
  · change (TapeEmbedding.config extraHeads (extraData core) r.final).tapes=_
    simp only [TapeEmbedding.config,rt]
    rfl
  · change (TapeEmbedding.config extraHeads (extraData core) r.final).heads=_
    have he : r.final.heads=(fun _ => 0) := funext rh
    simp only [TapeEmbedding.config,he]
    rfl

theorem second_run (core n k : ℕ) (old : Fin 1035 → List Bool)
    (hn : old 368=CompareMachine.word n) (hk : old 861=CompareMachine.word k) :
    ReadyAt second (CloseoutRowsGateCounts.budget n k core) heads (extend core old)
      (install slots (extend core old) (CloseoutRowsGateCounts.output n k core)) := by
  obtain ⟨base,hbase,bt,bh,bs⟩ := CloseoutRowsGateCounts.counts_run n k core
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slots injective CloseoutRowsGateCounts.machine
    heads (extend core old) _ _ base hbase
  have start : RecoveryFocus.config slots heads (extend core old)
      (RecoveryCalls.restarted CloseoutRowsGateCounts.machine CloseoutRowsGateCounts.heads
        (CloseoutRowsGateCounts.data n k core [] []))=
      RecoveryCalls.restarted second heads (extend core old) := by
    exact WilliamsSourceCrop.focus_same slots
      (⟨0,heads,extend core old⟩ : Configuration 1038 1)
      (RecoveryCalls.restarted CloseoutRowsGateCounts.machine CloseoutRowsGateCounts.heads
        (CloseoutRowsGateCounts.data n k core [] [])) selected_heads (by
          intro i;fin_cases i
          · exact hn
          · exact hk
          · rfl
          · rfl
          · rfl)
  rw [start] at hr
  refine ⟨r,hr,?_,?_,hs ▸ bs⟩
  · rw [hf]
    change install slots (extend core old) base.final.tapes=_
    rw [bt]
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp only [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      rw [←he]
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots injective,bh]
      exact (selected_heads j).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
