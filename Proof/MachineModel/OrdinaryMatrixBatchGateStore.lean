import Proof.MachineModel.OrdinaryMatrixBatchGateBody

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateStore
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads scratchSlots scratchPick stable)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store (r : Request) where
  assignment : ℕ
  id : ℕ
  cap : ℕ
  backing : Fin 30 → List Bool
  bounded : ∀ i,(backing i).length≤D r
def budget (r : Request) := 16*D r+40
noncomputable def data (r : Request) (source : List Bool) (pos : ℕ) (out : List Bool) (s : Store r) :=
  RecoveryCalls.restarted MatrixBatchGateBody.machine (heads pos out.length)
    (tapes r s.assignment s.id s.cap source out s.backing)

theorem budget_le (r : Request) (gate : Fin r.Gates) : MatrixBatchGateBody.budget r gate≤budget r := by
  have hc := (MatrixScoreReusableRanks.small_bounds r).1
  have hcopy : 4*r.width+8*r.M≤4*MatrixScoreLeftLoop.C r := by
    have hm := common_width r
    have hwl := r.widthLe
    unfold MatrixScoreLeftLoop.C
    omega
  have hbank := MatrixBatchGateBank.counter_fits r
  have hpacket := MatrixBatchRankedGate.packet_fits r gate
  have hscore := (MatrixScoreReusableRanks.budget_le r gate).trans_lt (MatrixScoreRawRanksBounds.budget_lt r gate)
  have hgap := MatrixScoreReusableRanks.capacity_gap r
  unfold MatrixBatchGateBody.budget MatrixBatchGatePrepare.budget MatrixBatchGateReset.budget
    MatrixScoreBankReady.budget MatrixBatchRankedGate.budget MatrixBatchRankAppend.budget budget
  omega

theorem scratch_local (i : Fin 30) (h29 : i≠29) : (scratchSlots i).val<41 := by
  fin_cases i <;> first | contradiction | decide
theorem fixed_partition (i : Fin 48) (hi : scratchPick i=none) :
    i.val<29 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 := by
  fin_cases i <;> simp [scratchPick] at hi ⊢

/-- The gate field held by batch tape `i < 29`: the same index below 27, the next one from 27 on. -/
def gateOf (i : Fin 29) : Fin 30 := if i.val<27 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
theorem native_gateOf (i : Fin 29) : MatrixBatchGateBody.native ((gateOf i).castAdd 14)=i.castAdd 19 := by
  fin_cases i <;> rfl

theorem fixed_field (r : Request) (gate : Fin r.Gates) (state : MatrixScoreLeftLoop.State r)
    (cap : ℕ) (source out : List Bool) (i : Fin 30)
    (hi : scratchPick (MatrixBatchGateBody.native (i.castAdd 14))=none) :
    ZeroPadding.pad (MatrixScoreReusableRanks.capacities r (i.castAdd 12))
      (MatrixScoreRetainedRanks.finalFields r gate state i)=
      stable r (r.phi (r.U-1)) (r.U+(r.U-1)) cap source out (MatrixBatchGateBody.native (i.castAdd 14)) := by
  fin_cases i <;> simp [scratchPick,MatrixBatchGateBody.native] at hi
  all_goals simp [MatrixScoreReusableRanks.capacities,MatrixScoreReusableRanks.fixed,ZeroPadding.pad,
    MatrixScoreRetainedRanks.finalFields,MatrixScoreHalvesReset.tapes,MatrixScoreLeftEnumeration.tapes,
    MatrixScorePhiLayout.tapes,MatrixScoreLeftCycle.tapes,MatrixScoreRecordDock.tapes,MatrixScoreLeftFields.tapes,
    MatrixScoreFoldEntry.tapes,MatrixScoreWeight.zeros,stable,Fin.addCases,MatrixBatchGateBody.native]

theorem rebuild (r : Request) (assignment id cap : ℕ) (source out : List Bool)
    (actual : Fin 48 → List Bool)
    (hfixed : ∀ i,scratchPick i=none → actual i=stable r assignment id cap source out i) :
    actual=tapes r assignment id cap source out (fun i => actual (scratchSlots i)) := by
  funext i
  unfold tapes install
  cases hp : RecoveryFocus.pick scratchSlots i with
  | none =>
    have hi : scratchPick i=none := (MatrixBatchGateClear.pick_scratch i).symm.trans hp
    exact hfixed i hi
  | some j =>
    have hi := RecoveryFocus.slot_of_pick scratchSlots hp
    change actual i = actual (scratchSlots j)
    rw [hi]

theorem step_run (r : Request) (gate : Fin r.Gates) (pre suffix out : List Bool) (s : Store r) :
    ∃ next : Store r,∃ actual,
      runFrom MatrixBatchGateBody.machine (budget r)
        (data r (pre++cutWord r.p (r.cuts.get gate)++suffix) pre.length out s)=some actual ∧
      actual.final.heads=(data r (pre++cutWord r.p (r.cuts.get gate)++suffix)
        (pre.length+(cutWord r.p (r.cuts.get gate)).length) (out++MatrixScoreRawRanks.output r gate) next).heads ∧
      actual.final.tapes=(data r (pre++cutWord r.p (r.cuts.get gate)++suffix)
        (pre.length+(cutWord r.p (r.cuts.get gate)).length) (out++MatrixScoreRawRanks.output r gate) next).tapes ∧
      actual.steps≤budget r := by
  obtain ⟨state,actual,ha,ah,a41,a43,a44,a45,a46,a47,af,ab,as⟩ :=
    MatrixBatchGateBody.body_run r gate s.assignment s.id s.cap pre suffix out s.backing s.bounded
  let backing := fun i : Fin 30 => actual.final.tapes (scratchSlots i)
  have bounded : ∀ i,(backing i).length≤D r := by
    intro i
    by_cases h29 : i=29
    · subst i
      change (actual.final.tapes 47).length≤D r
      rw [a47,List.length_replicate]
    let j : Fin 41 := ⟨(scratchSlots i).val,scratch_local i h29⟩
    have hj : j.castAdd 7=scratchSlots i := by apply Fin.ext; rfl
    have hh := ab j
    rw [hj] at hh
    exact hh
  let next : Store r := ⟨r.phi (r.U-1),r.U+(r.U-1),max s.cap (D r+1),backing,bounded⟩
  have hfixed : ∀ i,scratchPick i=none → actual.final.tapes i=
      stable r next.assignment next.id next.cap (pre++cutWord r.p (r.cuts.get gate)++suffix)
        (out++MatrixScoreRawRanks.output r gate) i := by
    intro i hi
    rcases fixed_partition i hi with hl | rfl | rfl | rfl | rfl | rfl | rfl
    · let j : Fin 29 := ⟨i.val,hl⟩
      have he : MatrixBatchGateBody.native ((gateOf j).castAdd 14)=i := (native_gateOf j).trans (by apply Fin.ext; rfl)
      have hj : scratchPick (MatrixBatchGateBody.native ((gateOf j).castAdd 14))=none := by rw [he]; exact hi
      have h24 : gateOf j≠24 := by
        intro h
        rw [h] at hj
        change (some (15 : Fin 30) : Option (Fin 30)) = none at hj
        contradiction
      have hh := (af (gateOf j) h24).trans (fixed_field r gate state next.cap
        (pre++cutWord r.p (r.cuts.get gate)++suffix) (out++MatrixScoreRawRanks.output r gate) (gateOf j) hj)
      simpa only [he] using hh
    · exact a41
    · exact (af 27 (by decide)).trans (fixed_field r gate state next.cap
        (pre++cutWord r.p (r.cuts.get gate)++suffix) (out++MatrixScoreRawRanks.output r gate) 27 (by decide))
    · exact a43
    · exact a44
    · exact a45
    · exact a46
  have ht := rebuild r next.assignment next.id next.cap _ _ actual.final.tapes hfixed
  have hb := budget_le r gate
  have he := runFrom_moreFuel MatrixBatchGateBody.machine _ (budget r-MatrixBatchGateBody.budget r gate) _ actual ha
  rw [Nat.add_sub_of_le hb] at he
  exact ⟨next,actual,he,ah,ht,as.trans hb⟩

end NearCubicWires.RepairOrdinary.MatrixBatchGateStore
