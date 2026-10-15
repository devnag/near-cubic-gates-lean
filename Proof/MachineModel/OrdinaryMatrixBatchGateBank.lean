import Proof.MachineModel.OrdinaryMatrixBatchGateReset

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateBank
open LocalBitMultitape SignedSortKey MatrixScoreBatch RecoveryRootRound
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padCaps (r : Request) : Fin 4 → ℕ := ![0,D r,0,D r]
def bankTapes (r : Request) (gate : Fin r.Gates) (pre suffix : List Bool) : Fin 4 → List Bool :=
  ![pre++cutWord r.p (r.cuts.get gate)++suffix,List.replicate (D r) false,
    UnaryTemplate.tape r.width,List.replicate (D r) false]
noncomputable def bankInput (r : Request) (gate : Fin r.Gates) (pre suffix : List Bool) :=
  RecoveryCalls.restarted MatrixScoreBankReady.machine ![pre.length,0,1,0] (bankTapes r gate pre suffix)
theorem counter_fits (r : Request) : MatrixScoreBankCut.budget r.width r.p≤D r := by
  have hh := MatrixScoreReusableRanks.capacity_gap r
  have hw := r.widthLe
  unfold MatrixScoreRawRanksBounds.capacity MatrixScoreBankCut.budget at *
  have hp : 1≤(r.d+r.p+1)^2 := by
    have hpos : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hu := Nat.mul_le_mul_right ((r.d+r.p+1)^2) (Nat.le_add_left 1 r.U)
  nlinarith

theorem padded_bank_run (r : Request) (gate : Fin r.Gates) (pre suffix : List Bool) :
    ∃ actual,runFrom MatrixScoreBankReady.machine (MatrixScoreBankReady.budget r.width r.p)
      (bankInput r gate pre suffix)=some actual ∧
      actual.final.heads= ![pre.length+(cutWord r.p (r.cuts.get gate)).length,0,1,0] ∧
      actual.final.tapes= ![pre++cutWord r.p (r.cuts.get gate)++suffix,
        ZeroPadding.pad (D r) (cutWord r.p (r.cuts.get gate)),UnaryTemplate.tape r.width,List.replicate (D r) false] ∧
      actual.steps≤MatrixScoreBankReady.budget r.width r.p := by
  obtain ⟨cap,hcap,base,hb,bh,bt,bs⟩ := MatrixScoreBankReady.bank_run r gate pre suffix
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config MatrixScoreBankReady.machine (padCaps r) _ _ base hb
  have hi : ZeroPadding.config (padCaps r)
      (RecoveryCalls.restarted MatrixScoreBankReady.machine ![pre.length,0,1,0]
        ![pre++cutWord r.p (r.cuts.get gate)++suffix,[],UnaryTemplate.tape r.width,[]])=
      bankInput r gate pre suffix := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,padCaps,bankInput,bankTapes,RecoveryCalls.restarted,ZeroPadding.pad]
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,has.trans_le bs⟩
  · rw [haf]
    exact bh
  · rw [haf]
    simp only [ZeroPadding.config]
    rw [bt]
    funext i
    fin_cases i
    · simp [padCaps]
    · rfl
    · simp [padCaps]
    · change ZeroPadding.pad (D r) (List.replicate cap false)=List.replicate (D r) false
      simp [ZeroPadding.pad,Nat.add_sub_of_le (hcap.trans (counter_fits r))]

def slots : Fin 4 → Fin 48 := ![46,0,17,47]
theorem slots_injective : Function.Injective slots := by decide
def picked : Fin 48 → Option (Fin 4) :=
  ![some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 2,none,none,none,none,none,
    none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,some 3]
theorem pick_slots (i : Fin 48) : RecoveryFocus.pick slots i=picked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot slots slots_injective 0
    | exact RecoveryFocus.pick_slot slots slots_injective 1
    | exact RecoveryFocus.pick_slot slots slots_injective 2
    | exact RecoveryFocus.pick_slot slots slots_injective 3
noncomputable def bank := RecoveryFocus.machine slots MatrixScoreBankReady.machine
def loaded (r : Request) (gate : Fin r.Gates) (i : Fin 30) :=
  if i=0 then ZeroPadding.pad (D r) (cutWord r.p (r.cuts.get gate)) else List.replicate (D r) false
noncomputable def input (r : Request) (gate : Fin r.Gates) (cap : ℕ) (pre suffix out : List Bool) :=
  RecoveryCalls.restarted bank (heads pre.length out.length)
    (tapes r 0 0 cap (pre++cutWord r.p (r.cuts.get gate)++suffix) out (fun _ => List.replicate (D r) false))

theorem bank_run (r : Request) (gate : Fin r.Gates) (cap : ℕ) (pre suffix out : List Bool) :
    ∃ actual,runFrom bank (MatrixScoreBankReady.budget r.width r.p) (input r gate cap pre suffix out)=some actual ∧
      actual.final.heads=heads (pre.length+(cutWord r.p (r.cuts.get gate)).length) out.length ∧
      actual.final.tapes=tapes r 0 0 cap (pre++cutWord r.p (r.cuts.get gate)++suffix) out (loaded r gate) ∧
      actual.steps≤MatrixScoreBankReady.budget r.width r.p := by
  obtain ⟨base,hb,bh,bt,bs⟩ := padded_bank_run r gate pre suffix
  let entry := input r gate cap pre suffix out
  have hi : RecoveryFocus.config slots entry.heads entry.tapes (bankInput r gate pre suffix)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [entry,input,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
        MatrixBatchGateClear.stable,slots,bankInput,bankTapes,RecoveryCalls.restarted]
  obtain ⟨actual,ha,haf,has⟩ := RecoveryFocus.run_config slots slots_injective MatrixScoreBankReady.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,has.trans_le bs⟩
  · rw [haf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_slots,picked,bh,entry,input,RecoveryCalls.restarted,heads]
  · rw [haf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_slots,picked,bt,entry,input,RecoveryCalls.restarted,tapes,
      install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable,loaded]

end NearCubicWires.RepairOrdinary.MatrixBatchGateBank
