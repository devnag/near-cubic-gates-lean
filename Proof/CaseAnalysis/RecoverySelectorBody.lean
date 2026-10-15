import Proof.CaseAnalysis.RecoverySelectorBodyLayout

/-! The complete ordinary selector body emits the original guard/AND,
saves its output, advances the graph counter, and restores every consumed
field for the next value. It keeps the graph and outer-stream cursors. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=TapeEmbedding.machine 1 RecoveryBoundedSelectorJoin.machine
noncomputable def last:=RecoveryFocus.machine restoreSlots RecoveryBoundedSelectorRestore.machine
noncomputable def machine:=Composition.machine first last
def budget (ref limit acc index value C : ℕ):=
  RecoveryBoundedSelectorJoin.budget ref limit acc C+1+(2*C+2*index+2*value+14)
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit ref : ℕ) (out skipped tail stack : List Bool) :=
  restart (TapeEmbedding.config (fun _ : Fin 1=>0)
    (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true)
    (ZeroPadding.config (flagCaps C)
      (RecoveryBoundedSelectorJoin.entry (n:=n) row start base C D value limit ref out [] skipped tail stack))) machine.start
noncomputable def doneState {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  let before:=post b row start limit value C D ref out skipped tail stack hblock
  {before with tapes:=(install restoreSlots before.tapes
    (RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
      ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 3))}

theorem body_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D : ℕ) (out skipped tail stack : List Bool)
    (wire : LiveWire b) (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hv : value≤W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedReferenceAppend.budget wire.output.val limit C ≤ D) :
    ∃ r,runFrom machine (budget wire.output.val limit (RecoveryBoundedSelectorJoin.counter b row start limit value hblock)
        (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) value C)
      (entry (n:=n) row start b.nodes.length C D value limit wire.output.val out skipped tail stack)=some r ∧
      r.steps ≤ budget wire.output.val limit (RecoveryBoundedSelectorJoin.counter b row start limit value hblock)
        (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) value C ∧
      r.final.heads=(doneState b row start limit value C D wire.output.val out skipped tail stack hblock).heads ∧
      r.final.tapes=(doneState b row start limit value C D wire.output.val out skipped tail stack hblock).tapes := by
  have hr : wire.output.val≤W := by have h:=wire.output.isLt; omega
  have hiC : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+1≤C := by
    nlinarith [Nat.zero_le (W*W)]
  have hrC : wire.output.val≤C := by nlinarith [Nat.zero_le (W*W)]
  have hvC : value+1≤C := by nlinarith [Nat.zero_le (W*W)]
  obtain ⟨u,hu,us,uh,ut⟩:=RecoveryBoundedSelectorJoin.join_run
    b row start limit value W C D out [] skipped tail stack wire hblock hi hp hC hD
  obtain ⟨p,hpRun,pf,ps,_pp⟩:=ZeroPadding.run_config RecoveryBoundedSelectorJoin.machine (flagCaps C) _ _ u hu
  let a:=TapeEmbedding.receipt (fun _ : Fin 1=>0)
    (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true) p
  have ar:=TapeEmbedding.run_embed RecoveryBoundedSelectorJoin.machine (fun _ : Fin 1=>0)
    (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true) _ _ p hpRun
  have ah : a.final.heads=(post b row start limit value C D wire.output.val out skipped tail stack hblock).heads := by
    change (Fin.addCases (m:=41) (n:=1) (motive:=fun _=>ℕ) p.final.heads (fun _=>0))=_
    rw [pf]
    simp only [ZeroPadding.config]
    rw [uh]
    rfl
  have atapes : a.final.tapes=(post b row start limit value C D wire.output.val out skipped tail stack hblock).tapes := by
    change (Fin.addCases (m:=41) (n:=1) (motive:=fun _=>List Bool) p.final.tapes
      (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true))=_
    rw [pf]
    simp only [ZeroPadding.config]
    rw [ut]
    rfl
  obtain ⟨z,hz,zh,zt,zs⟩:=
    (RecoveryBoundedSelectorRestore.restore_ready (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
      wire.output.val value C (lastFlag (n:=n) row start b.nodes.length value limit out) hiC hrC hvC).focus_at
      restoreSlots (by decide) a.final.heads a.final.tapes
      (by rw [atapes]; exact restore_tapes b row start limit value C D wire.output.val out skipped tail stack hblock)
      (by rw [ah]; exact restore_heads b row start limit value C D wire.output.val out skipped tail stack hblock)
  have full:=Composition.run_join first last _ _ _ a z ar hz
  refine ⟨joinedReceipt a z,full,?_,?_,?_⟩
  · change p.steps+1+z.steps ≤ _
    rw [ps,zs]
    unfold budget
    omega
  · change z.final.heads=_
    rw [zh,ah]
    rfl
  · change z.final.tapes=_
    rw [zt,atapes]
    rfl

theorem budget_cubic (ref limit acc index value W : ℕ)
    (hr : ref≤W) (hl : limit≤W) (ha : acc≤W) (hi : index≤W) (hv : value≤W) :
    budget ref limit acc index value (16384*(W+1)^2) ≤ 67108864*(W+1)^3 := by
  have h:=RecoveryBoundedSelectorJoin.budget_cubic ref limit acc W hr hl ha
  have h1 : W+1 ≤ (W+1)^3 := by nlinarith [Nat.zero_le (W*W),Nat.zero_le (W*W*W)]
  have h2 : (W+1)^2 ≤ (W+1)^3 := by nlinarith [Nat.zero_le (W*W),Nat.zero_le (W*W*W)]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
