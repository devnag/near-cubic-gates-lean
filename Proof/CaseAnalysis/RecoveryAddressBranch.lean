import Proof.CaseAnalysis.RecoveryAddressBank

/-! Read the actual address bit and run precisely the original child:
its unary field equality when true, its false constant otherwise. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryExecution RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dispatch : Machine 40 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def stateCount {t s : ℕ} (_ : Machine t s):=s
noncomputable def branchSizes : Fin 3→ℕ:=![1,stateCount unary,stateCount seed]
noncomputable def branchPrograms : (j : Fin 3)→Machine 40 (branchSizes j)
  | ⟨0,_⟩=>dispatch
  | ⟨1,_⟩=>unary
  | ⟨2,_⟩=>seed
  | ⟨j+3,h⟩=>False.elim (by omega)
def branchNext (j : Fin 3) (_ : Fin (branchSizes j)) (bits : Fin 40→Bool) : Option (Fin 3):=
  if j.val=0 then some (if bits 37 then 1 else 2) else none
noncomputable def branch:=RecoveryCalls.machine branchSizes branchPrograms 0 branchNext
def branchBudget (limit C : ℕ):=RecoveryBoundedUnaryReuse.budget limit C+RecoveryBoundedSelectorFinish.falseBits.length+2

theorem dispatch_run (j : Fin 3) (hj : j=1 ∨ j=2) (fuel : ℕ)
    (hh : Fin 40→ℕ) (tt : Fin 40→List Bool) (r : ExecutionReceipt 40 (branchSizes j))
    (hc : j=if readTapeBit (tt 37) (hh 37) then 1 else 2)
    (hr : runFrom (branchPrograms j) fuel ⟨(branchPrograms j).start,hh,tt⟩=some r) :
    ∃ z,runFrom branch (fuel+2) ⟨branch.start,hh,tt⟩=some z ∧
      z.steps ≤ fuel+2 ∧ z.final.heads=r.final.heads ∧ z.final.tapes=r.final.tapes := by
  let source : Configuration 40 1:=⟨0,hh,tt⟩
  have hn : branchNext 0 source.control source.scanned=some j := by
    change some (if readTapeBit (tt 37) (hh 37) then (1 : Fin 3) else 2)=some j
    exact congrArg some hc.symm
  have hstep:=RecoveryCalls.return_step branchSizes branchPrograms 0 branchNext 0 j source (by rfl) hn
  have h0:=Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hstep
  have hstop : branchNext j r.final.control r.final.scanned=none := by
    rcases hj with rfl|rfl <;> rfl
  obtain ⟨k,hk,h1⟩:=stop_receipt branchSizes branchPrograms 0 branchNext j fuel _ r hr hstop
  have hall:=h0.trans h1
  obtain ⟨z,hz,zf,zs⟩:=hall.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : 1+k ≤ fuel+2 := by omega
  have more:=runFrom_moreFuel branch (1+k) (fuel+2-(1+k)) _ z hz
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨z,more,zs.le.trans hb,by rw [zf];rfl,by rw [zf];rfl⟩

theorem branch_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D pos retained : ℕ) (out source stack : List Bool)
    (bit : Bool) (hread : readTapeBit source pos=bit)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C ≤ D) :
    let expression:=if bit then unaryEqualsExpr row start limit value hblock else .const false
    let compiled:=compileExpr b expression
    let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
    let flag:=bit && (RecoveryBoundedUnaryReuse.forward (n:=n) row start b.nodes.length value limit out).flag
    ∃ r,runFrom branch (branchBudget limit C)
      ⟨branch.start,heads out stack pos,data index b.nodes.length C D value limit false out source stack retained⟩=some r ∧
      r.steps ≤ branchBudget limit C ∧ r.final.heads=heads emitted stack pos ∧
      r.final.tapes=data (if bit then 0 else index) compiled.output.val C D value limit flag emitted source stack retained := by
  cases bit
  · obtain ⟨p,hpRun,ps,ph,pt⟩:=seed_run (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
      b.nodes.length C D value limit pos retained out source stack
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run 2 (Or.inr rfl) _ (heads out stack pos)
      (data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) b.nodes.length C D value limit false out source stack retained) p
      (by change (2 : Fin 3)=if readTapeBit source pos then 1 else 2;rw [hread];rfl) hpRun
    have hb : RecoveryBoundedSelectorFinish.falseBits.length+2 ≤ branchBudget limit C := by unfold branchBudget;omega
    have more:=runFrom_moreFuel branch _ (branchBudget limit C-(RecoveryBoundedSelectorFinish.falseBits.length+2)) _ z hz
    rw [Nat.add_sub_of_le hb] at more
    exact ⟨z,more,zs.trans hb,zh.trans ph,zt.trans pt⟩
  · obtain ⟨p,hpRun,ps,ph,pt⟩:=unary_run b row start limit value W C D pos retained out source stack hblock hi hp hC hD
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run 1 (Or.inl rfl) _ (heads out stack pos)
      (data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) b.nodes.length C D value limit false out source stack retained) p
      (by change (1 : Fin 3)=if readTapeBit source pos then 1 else 2;rw [hread];rfl) hpRun
    have hb : RecoveryBoundedUnaryReuse.budget limit C+2 ≤ branchBudget limit C := by unfold branchBudget;omega
    have more:=runFrom_moreFuel branch _ (branchBudget limit C-(RecoveryBoundedUnaryReuse.budget limit C+2)) _ z hz
    rw [Nat.add_sub_of_le hb] at more
    exact ⟨z,more,zs.trans hb,zh.trans ph,zt.trans pt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
