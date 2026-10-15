import Proof.CaseAnalysis.RecoveryUnaryReuseBank

/-! Every returned unary-expression port, including the bounded erased
stack and the retained value, is identified before the next graph append. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def forward {n bound : ℕ} (row : Fin (bound+1)) (start base value limit : ℕ) (out : List Bool) :=
  (RecoveryBoundedNativeUnaryLoop.initial (n:=n) row start base out []).iterate value limit
def result {n bound : ℕ} (row : Fin (bound+1)) (start base value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  RecoveryBoundedNativeFoldLoop.State.iterate true
    (literalReferences base (unaryItems row start limit value hblock)).reverse
    ⟨(forward (n:=n) row start base value limit out).position,0,0,
      (forward (n:=n) row start base value limit out).out++RecoveryBoundedNativeUnaryPhase.trueBits⟩

theorem fold_pick_old (j : Fin 34) : RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (j.castAdd 2)=some (j.castAdd 1) := by
  simpa only [RecoveryBoundedNativeUnaryJoin.foldSlots,Fin.addCases_left] using
    RecoveryFocus.pick_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide) (j.castAdd 1)
theorem fold_pick_value : RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (34 : Fin 36)=none := by
  simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,RecoveryBoundedNativeUnaryJoin.foldSlots j=(34 : Fin 36))]
theorem fold_pick_driver : RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (35 : Fin 36)=some 34 :=
  RecoveryFocus.pick_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide) 34

theorem final_heads {n bound : ℕ} (row : Fin (bound+1)) (start base C value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (RecoveryBoundedNativeUnaryJoin.finalState row start base C value limit out [] hblock).heads=
      Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
        (RecoveryBoundedNativeFold.heads (result row start base value limit out hblock).out 0) (fun _=>1) := by
  rfl

theorem final_tapes {n bound : ℕ} (row : Fin (bound+1)) (start base C value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (RecoveryBoundedNativeUnaryJoin.finalState row start base C value limit out [] hblock).tapes=
      Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
        (RecoveryBoundedNativeFold.data 0 (result row start base value limit out hblock).acc C
          (forward (n:=n) row start base value limit out).flag (result row start base value limit out hblock).out
          (List.replicate (result row start base value limit out hblock).erased false) [])
        (fun _=>CompareMachine.word (literalReferences base (unaryItems row start limit value hblock)).length) := by
  rfl

theorem complete_heads {n bound : ℕ} (row : Fin (bound+1)) (start base C value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (RecoveryBoundedNativeUnaryJoin.completeState row start base C value limit out [] hblock).heads=
      RecoveryBoundedNativeUnaryJoin.foldHeads (result row start base value limit out hblock).out 0 limit 1 := by
  unfold RecoveryBoundedNativeUnaryJoin.completeState
  simp only [RecoveryFocus.config,final_heads]
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [fold_pick_old,RecoveryBoundedNativeUnaryJoin.foldHeads,Fin.addCases_left]
  · fin_cases j
    · change (match RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (34 : Fin 36) with
        | some j=>Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
            (RecoveryBoundedNativeFold.heads (result row start base value limit out hblock).out 0) (fun _=>1) j
        | none=>limit)=limit
      rw [fold_pick_value]
    · change (match RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (35 : Fin 36) with
        | some j=>Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
            (RecoveryBoundedNativeFold.heads (result row start base value limit out hblock).out 0) (fun _=>1) j
        | none=>limit)=1
      rw [fold_pick_driver]
      rfl

theorem complete_tapes {n bound : ℕ} (row : Fin (bound+1)) (start base C value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (RecoveryBoundedNativeUnaryJoin.completeState row start base C value limit out [] hblock).tapes=
      RecoveryBoundedNativeUnaryJoin.foldData (result row start base value limit out hblock).acc C value limit
        (forward (n:=n) row start base value limit out).flag (result row start base value limit out hblock).out
        (List.replicate (result row start base value limit out hblock).erased false) := by
  have hl : (literalReferences base (unaryItems row start limit value hblock)).length=limit := by
    simp only [references_length,unaryItems,List.length_ofFn]
  unfold RecoveryBoundedNativeUnaryJoin.completeState
  simp only [RecoveryFocus.config,final_tapes,hl]
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [fold_pick_old,RecoveryBoundedNativeUnaryJoin.foldData,Fin.addCases_left]
  · fin_cases j
    · change (match RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (34 : Fin 36) with
        | some j=>Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
            (RecoveryBoundedNativeFold.data 0 (result row start base value limit out hblock).acc C
              (forward (n:=n) row start base value limit out).flag (result row start base value limit out hblock).out
              (List.replicate (result row start base value limit out hblock).erased false) [])
            (fun _=>CompareMachine.word limit) j
        | none=>List.replicate value true)=List.replicate value true
      rw [fold_pick_value]
    · change (match RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots (35 : Fin 36) with
        | some j=>Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
            (RecoveryBoundedNativeFold.data 0 (result row start base value limit out hblock).acc C
              (forward (n:=n) row start base value limit out).flag (result row start base value limit out hblock).out
              (List.replicate (result row start base value limit out hblock).erased false) [])
            (fun _=>CompareMachine.word limit) j
        | none=>List.replicate value true)=CompareMachine.word limit
      rw [fold_pick_driver]
      rfl

theorem finished_heads {n bound : ℕ} (row : Fin (bound+1)) (start base C D value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (finished row start base C D value limit out hblock).heads=heads (result row start base value limit out hblock).out := by
  unfold finished
  simp only [TapeEmbedding.config,ZeroPadding.config,complete_heads]
  funext i
  fin_cases i
  all_goals first | (change (0 : ℕ)=0;rfl) | (change (1 : ℕ)=1;rfl) |
    (change (result row start base value limit out hblock).out.length=(result row start base value limit out hblock).out.length;rfl)

theorem finished_tapes {n bound : ℕ} (row : Fin (bound+1)) (start base C D value limit : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) (hz : (result row start base value limit out hblock).erased ≤ C) :
    (finished row start base C D value limit out hblock).tapes=
      data 0 (result row start base value limit out hblock).acc C D value limit
        (forward (n:=n) row start base value limit out).flag (result row start base value limit out hblock).out := by
  unfold finished
  simp only [TapeEmbedding.config,ZeroPadding.config,complete_tapes]
  funext i
  fin_cases i
  all_goals first | rfl | (change ZeroPadding.pad 0 _=_;exact ZeroPadding.pad_zero _) |
    (change ZeroPadding.pad C (List.replicate C false)=List.replicate C false; exact RecoveryBoundedSelectorLoop.pad_erased C C (Nat.le_refl _)) |
    (change ZeroPadding.pad C (List.replicate (result row start base value limit out hblock).erased false)=List.replicate C false;
      exact RecoveryBoundedSelectorLoop.pad_erased C _ hz)

end NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
