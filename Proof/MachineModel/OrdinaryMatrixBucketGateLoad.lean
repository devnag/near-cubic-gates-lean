import Proof.MachineModel.OrdinaryMatrixBucketGatePrepare

/-! The reusable gate bank physically clears and loads the next full ranked
packet. Only the global source cursor advances; the key append cursor and
all retained native fields are preserved. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketGateLoad
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch MatrixBatchBucketEndpoints MatrixBucketGatePrepare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 35 := ![34,15,31]
noncomputable def last := RecoveryFocus.machine slots MatrixRankPacketLoad.machine
noncomputable def machine := Composition.machine MatrixBucketGatePrepare.machine last
def loadBudget (r : Request) := 2*((r.U+r.U)*(4*H r+3)+3)+2
def budget (r : Request) := MatrixBucketGatePrepare.budget r+1+loadBudget r
noncomputable def input (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (pos : ℕ) :=
  Composition.leftConfig 9 (cfg r inner boundary rank upper record clone packet out unused source pos)

theorem packet_same (r : Request) (inner rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (i : Fin 35) (hi : i≠15) :
    data r inner 0 rank upper record clone [] out unused source i=
      data r inner 0 rank upper record clone packet out unused source i := by
  revert hi
  refine Fin.addCases (m := 23) (n := 12)
    (motive := fun j => j≠15 →
      data r inner 0 rank upper record clone [] out unused source j=
        data r inner 0 rank upper record clone packet out unused source j)
    (fun j => ?_) (fun j => ?_) i
  · intro hi
    by_cases hj : j=15
    · subst j
      exact (hi rfl).elim
    simp only [data,Fin.addCases_left,native_core]
    apply congrArg (ZeroPadding.pad (MatrixScoreReusableRanks.D r))
    fin_cases j <;> first | exact (hj rfl).elim | simp only [core,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · intro _
    simp only [data,Fin.addCases_right]

theorem load_run (r : Request) (gate : Fin r.Gates) (inner boundary rank : ℕ)
    (upper record clone packet out : List Bool) (unused : Fin 3 → List Bool) (pre suffix : List Bool)
    (hpacket : packet.length ≤ MatrixScoreReusableRanks.D r) :
    ∃ actual,runFrom machine (budget r)
      (input r inner boundary rank upper record clone packet out unused
        (pre++MatrixScoreRawRanks.output r gate++suffix) pre.length)=some actual ∧
      actual.final.heads=heads out.length (pre.length+(MatrixScoreRawRanks.output r gate).length) ∧
      actual.final.tapes=data r inner 0 rank upper record clone (MatrixScoreRawRanks.output r gate) out unused
        (pre++MatrixScoreRawRanks.output r gate++suffix) ∧ actual.steps=budget r := by
  let D := MatrixScoreReusableRanks.D r
  let source := pre++MatrixScoreRawRanks.output r gate++suffix
  obtain ⟨prepared,hp,ph,pt,ps⟩ := MatrixBucketGatePrepare.prepare_run r inner boundary rank
    upper record clone packet out unused source pre.length hpacket
  obtain ⟨base,hb,bh,bt,bs⟩ := MatrixRankPacketLoad.padded_run D
    (MatrixBatchRankedGate.rankWords r gate) pre suffix
    (MatrixBatchRankedGate.words_nonempty r gate) (MatrixBatchRankedGate.packet_fits r gate)
  have htime : MatrixRankPacketLoad.budget (MatrixBatchRankedGate.rankWords r gate)=loadBudget r := by
    unfold MatrixRankPacketLoad.budget
    rw [MatrixBatchRankedGate.packet_budget]
    rfl
  rw [htime] at hb bs
  let entry := MatrixRankPacketLoad.paddedInput D (MatrixBatchRankedGate.rankWords r gate) pre suffix
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [MatrixRankPacketLoad.padded_heads,ph]
      fin_cases i <;> rfl
    · intro i
      rw [MatrixRankPacketLoad.padded_tapes,pt,MatrixBatchRankedGate.stream_eq]
      fin_cases i <;> rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots (by decide) MatrixRankPacketLoad.machine
    prepared.final.heads prepared.final.tapes _ entry base hb
  rw [hi] at hf
  have joined := Composition.run_join MatrixBucketGatePrepare.machine last _ _ _ prepared focused hp hf
  rw [MatrixBatchRankedGate.stream_eq] at bh bt
  have fslot (i : Fin 3) : focused.final.tapes (slots i)=
      (![source,ZeroPadding.pad D (MatrixScoreRawRanks.output r gate),List.replicate D false] : Fin 3 → List Bool) i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),bt]
    rfl
  have fold (i : Fin 35) (hi : ∀ j,slots j≠i) :
      focused.final.tapes i=data r inner 0 rank upper record clone [] out unused source i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick]
    simp only [not_exists.mpr hi,↓reduceDIte,pt]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,?_⟩
  · change focused.final.heads=_
    rw [ff]
    funext i
    cases hi : RecoveryFocus.pick slots i with
    | none =>
      simp only [RecoveryFocus.config,hi,ph]
      have hne : i≠34 := by
        intro he; subst i
        have hs := RecoveryFocus.pick_slot slots (by decide) 0
        change RecoveryFocus.pick slots 34=some 0 at hs
        rw [hi] at hs
        contradiction
      simp [heads,hne]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hi
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),bh]
      fin_cases j <;> rfl
  · change focused.final.tapes=_
    funext i
    by_cases h15 : i=15
    · subst i
      exact fslot 1
    by_cases h31 : i=31
    · subst i
      exact fslot 2
    by_cases h34 : i=34
    · subst i
      exact fslot 0
    apply (fold i (by intro j; fin_cases j <;> simp [slots,Ne.symm h15,Ne.symm h31,Ne.symm h34])).trans
    exact packet_same r inner rank upper record clone (MatrixScoreRawRanks.output r gate) out unused source i h15
  · change prepared.steps+1+focused.steps=budget r
    rw [ps,fs,bs]
    rfl

end NearCubicWires.RepairOrdinary.MatrixBucketGateLoad
