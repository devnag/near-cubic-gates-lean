import Proof.CaseAnalysis.RecoverySelectorReference

/-! Join the original guarded head to its actual output-reference push and
next-node counter. All forty-one tapes are retained across the handoff. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorJoin
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counter {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (hblock : start+limit ≤ rowWidth n bound) :=
  b.nodes.length+prefixCount (unaryItems row start limit value hblock)+limit

private theorem counter_port {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out pre skipped tail : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out pre skipped tail hblock).heads 25=0 ∧
    (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out pre skipped tail hblock).tapes 25=
      List.replicate (counter b row start limit value hblock) true := by
  have hp : RecoveryFocus.pick RecoveryBoundedNativeGuarded.slots 25=some 25 := by
    have he : RecoveryBoundedNativeGuarded.slots 25=(25 : Fin 37) := rfl
    rw [←he]
    exact RecoveryFocus.pick_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective 25
  change (RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out pre hblock).heads 25=0 ∧
    ZeroPadding.pad 0 (ZeroPadding.pad 0
      ((RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out pre hblock).tapes 25))=_
  simp only [ZeroPadding.pad_zero,RecoveryBoundedNativeGuarded.completeState,RecoveryFocus.config,hp]
  exact ⟨rfl,rfl⟩

private theorem scratch_port {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out pre skipped tail : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out pre skipped tail hblock).heads 32=0 ∧
    (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out pre skipped tail hblock).tapes 32=
      List.replicate C false := by
  have hg : RecoveryFocus.pick RecoveryBoundedNativeGuarded.slots 32=none := by
    have hn : ¬∃ j,RecoveryBoundedNativeGuarded.slots j=32 := by decide
    simp only [RecoveryFocus.pick,dif_neg hn]
  have hf : RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots 32=some 32 := by
    have he : RecoveryBoundedNativeUnaryJoin.foldSlots 32=(32 : Fin 36) := rfl
    rw [←he]
    exact RecoveryFocus.pick_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide) 32
  change (RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out pre hblock).heads 32=0 ∧
    ZeroPadding.pad 0 (ZeroPadding.pad 0
      ((RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out pre hblock).tapes 32))=_
  simp only [ZeroPadding.pad_zero,RecoveryBoundedNativeGuarded.completeState,RecoveryFocus.config,hg]
  change (RecoveryBoundedNativeUnaryJoin.completeState row start b.nodes.length C value limit out pre hblock).heads 32=0 ∧
    (RecoveryBoundedNativeUnaryJoin.completeState row start b.nodes.length C value limit out pre hblock).tapes 32=_
  simp only [RecoveryBoundedNativeUnaryJoin.completeState,RecoveryFocus.config,hf]
  exact ⟨rfl,rfl⟩

def slots : Fin 3→Fin 41:=![25,40,32]
noncomputable def first:=TapeEmbedding.machine 1 RecoveryBoundedSelectorReset.machine
noncomputable def last:=RecoveryFocus.machine slots RecoveryBoundedSelectorReference.machine
noncomputable def machine:=Composition.machine first last
def budget (ref limit acc C : ℕ):=RecoveryBoundedSelectorReset.budget ref limit C+1+(8*acc+22)
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit ref : ℕ) (out pre skipped tail stack : List Bool) :=
  restart (TapeEmbedding.config (fun _ : Fin 1=>stack.length) (fun _=>stack)
    (RecoveryBoundedSelectorReset.entry (n:=n) row start base C D value limit ref out pre skipped tail)) machine.start
noncomputable def completeState {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out pre skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  let before:=TapeEmbedding.config (fun _ : Fin 1=>stack.length) (fun _=>stack)
    (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out pre skipped tail hblock)
  let acc:=counter b row start limit value hblock
  RecoveryFocus.config slots before.heads before.tapes
    (⟨RecoveryBoundedSelectorReference.machine.start,
      RecoveryBoundedSelectorReference.heads (RecoveryBoundedSelectorReference.pushed acc stack),
      RecoveryBoundedSelectorReference.data (acc+2) C
        (RecoveryBoundedSelectorReference.pushed acc stack)⟩ : Configuration 3 _)

theorem join_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D : ℕ) (out pre skipped tail stack : List Bool)
    (wire : LiveWire b) (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedReferenceAppend.budget wire.output.val limit C ≤ D) :
    ∃ r,runFrom machine (budget wire.output.val limit (counter b row start limit value hblock) C)
      (entry (n:=n) row start b.nodes.length C D value limit wire.output.val out pre skipped tail stack)=some r ∧
      r.steps ≤ budget wire.output.val limit (counter b row start limit value hblock) C ∧
      r.final.heads=(completeState b row start limit value C D wire.output.val out pre skipped tail stack hblock).heads ∧
      r.final.tapes=(completeState b row start limit value C D wire.output.val out pre skipped tail stack hblock).tapes := by
  let acc:=counter b row start limit value hblock
  have ha : acc ≤ W := by
    have h:=prefixCount_bound (unaryItems row start limit value hblock)
    have hl : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
    rw [hl] at h
    dsimp only [acc,counter]
    omega
  have hc : 2*(acc+1)+2 ≤ C := by nlinarith [Nat.zero_le (W*W)]
  obtain ⟨u,hu,us,uh,ut⟩:=RecoveryBoundedSelectorReset.reset_run
    b row start limit value W C D out pre skipped tail wire hblock hi hp hC hD
  let a:=TapeEmbedding.receipt (fun _ : Fin 1=>stack.length) (fun _=>stack) u
  have ar:=TapeEmbedding.run_embed RecoveryBoundedSelectorReset.machine
    (fun _ : Fin 1=>stack.length) (fun _=>stack) _ _ u hu
  obtain ⟨v,hv,vh,vt,vs⟩:=RecoveryBoundedSelectorReference.reference_run acc C stack hc
  have inHeads (j : Fin 3) : a.final.heads (slots j)=
      (RecoveryBoundedSelectorReference.entry acc C stack).heads j := by
    fin_cases j
    · change u.final.heads 25=0
      rw [uh]
      exact (counter_port b row start limit value C D wire.output.val out pre skipped tail hblock).1
    · rfl
    · change u.final.heads 32=0
      rw [uh]
      exact (scratch_port b row start limit value C D wire.output.val out pre skipped tail hblock).1
  have inTapes (j : Fin 3) : a.final.tapes (slots j)=
      (RecoveryBoundedSelectorReference.entry acc C stack).tapes j := by
    fin_cases j
    · change u.final.tapes 25=List.replicate acc true
      rw [ut]
      exact (counter_port b row start limit value C D wire.output.val out pre skipped tail hblock).2
    · rfl
    · change u.final.tapes 32=List.replicate C false
      rw [ut]
      exact (scratch_port b row start limit value C D wire.output.val out pre skipped tail hblock).2
  obtain ⟨z,hz,_zc,zs,zh,zt,zk⟩:=RecoveryFocus.dock slots (by decide)
    RecoveryBoundedSelectorReference.machine _ a.final.heads a.final.tapes
    (RecoveryBoundedSelectorReference.entry acc C stack) inHeads inTapes v hv
  have full:=Composition.run_join first last _ _ _ a z ar hz
  refine ⟨joinedReceipt a z,full,?_,?_,?_⟩
  · change u.steps+1+z.steps ≤ _
    rw [zs]
    unfold budget
    omega
  · change z.final.heads=_
    funext i
    cases hpick : RecoveryFocus.pick slots i with
    | some j=>
      have he:=RecoveryFocus.slot_of_pick slots hpick
      rw [←he]
      simp only [completeState,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
      exact (zh j).trans (congrFun vh j)
    | none=>
      have away : ∀ j,slots j≠i := by
        intro j he
        have h:=RecoveryFocus.pick_slot slots (by decide) j
        rw [he,hpick] at h
        contradiction
      rw [(zk i away).1]
      simp only [completeState,RecoveryFocus.config,hpick]
      change (Fin.addCases (m:=40) (n:=1) (motive:=fun _=>ℕ) u.final.heads (fun _=>stack.length)) i=_
      rw [uh]
      rfl
  · change z.final.tapes=_
    funext i
    cases hpick : RecoveryFocus.pick slots i with
    | some j=>
      have he:=RecoveryFocus.slot_of_pick slots hpick
      rw [←he]
      simp only [completeState,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
      exact (zt j).trans (congrFun vt j)
    | none=>
      have away : ∀ j,slots j≠i := by
        intro j he
        have h:=RecoveryFocus.pick_slot slots (by decide) j
        rw [he,hpick] at h
        contradiction
      rw [(zk i away).2]
      simp only [completeState,RecoveryFocus.config,hpick]
      change (Fin.addCases (m:=40) (n:=1) (motive:=fun _=>List Bool) u.final.tapes (fun _=>stack)) i=_
      rw [ut]
      rfl

theorem budget_cubic (ref limit acc W : ℕ) (hr : ref ≤ W) (hl : limit ≤ W) (ha : acc ≤ W) :
    budget ref limit acc (16384*(W+1)^2) ≤ 33554432*(W+1)^3 := by
  have h:=RecoveryBoundedSelectorReset.budget_cubic ref limit W hr hl
  have hp : W+1 ≤ (W+1)^3 := by nlinarith [Nat.zero_le (W*W),Nat.zero_le (W*W*W)]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorJoin
