import Proof.CaseAnalysis.RecoveryGrammarDriverInitial
import Proof.Circuits.DecompositionCountPosition

/-! Refresh only the candidate driver after the retained raw candidate has
advanced. Its old backing is erased, the existing printer runs, and head one
is restored; the full-bound driver and every other tape are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
open LocalBitMultitape Composition RecoveryRootRound
open private install_eq from Proof.Amplification.RecoveryRowLookupCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions (d : HeadMove) : Fin 114→HeadMove:=fun i=>if i=113 then d else .stay
def shift (d : HeadMove):=DecompositionCountPosition.move (directions d)

theorem shift_run (d : HeadMove) (H : Fin 114→ℕ) (A : Fin 114→List Bool) :
    ∃ r,runFrom (shift d) 1 ⟨(shift d).start,H,A⟩=some r ∧ r.steps=1 ∧
      r.final.heads=Function.update H 113 (d.apply (H 113)) ∧ r.final.tapes=A := by
  obtain ⟨r,rr,rf,rs⟩:=DecompositionCountPosition.move_run (directions d) H A
  refine ⟨r,rr,rs,?_,congrArg Configuration.tapes rf⟩
  rw [rf]
  funext i
  by_cases hi : i=113
  · subst i;simp [directions]
  · simp [directions,hi,HeadMove.apply]

def erasePorts : Fin 3→Fin 114:=![113,76,77]
noncomputable def erase:=RecoveryFocus.machine erasePorts (RecoveryScratchErase.resetMachine 1)

theorem erase_run (B : ℕ) (bits : List Bool) (H : Fin 114→ℕ) (A : Fin 114→List Bool)
    (hbits : bits.length≤B) (hin : ∀ j,A (erasePorts j)=![bits,List.replicate B true,List.replicate (B+1) false] j)
    (hh : ∀ j,H (erasePorts j)=0) :
    ∃ r,runFrom erase (2*B+4) ⟨erase.start,H,A⟩=some r ∧ r.steps≤2*B+4 ∧
      r.final.heads=H ∧ r.final.tapes=Function.update A 113 (List.replicate B false) := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(RecoveryBoundedGrammarScalarAdd.erase_ready bits B hbits).focus_at
    erasePorts (by decide) H A hin hh
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt]
  apply install_eq erasePorts (by decide)
  · intro j
    have hd : (113 : Fin 114)=erasePorts 0:=rfl
    rw [hd]
    by_cases hj : j=0
    · subst j;rw [Function.update_self];rfl
    · rw [Function.update_of_ne ((show Function.Injective erasePorts by decide).ne hj)]
      have same : ![List.replicate B false,List.replicate B true,List.replicate (B+1) false] j=
          ![bits,List.replicate B true,List.replicate (B+1) false] j := by fin_cases j <;> simp_all
      exact same.trans (hin j).symm
  · intro i hi
    exact (Function.update_of_ne (Ne.symm (hi 0)) _ _).symm

noncomputable def refresh:=Composition.machine
  (Composition.machine (Composition.machine (shift .left) erase) (emit false)) (shift .right)
def refreshBudget (B count : ℕ):=((1+1+(2*B+4))+1+(2*count+8))+1+1

theorem refresh_run (B count : ℕ) (H : Fin 114→ℕ) (A : Fin 114→List Bool)
    (hcount : count+3≤B) (hold : (A 113).length≤B)
    (rawCount : A 101=ZeroPadding.pad B (List.replicate count true))
    (log : A 78=List.replicate B false)
    (driver : A 76=List.replicate B true) (eraseLog : A 77=List.replicate (B+1) false)
    (hc : H 101=0) (hl : H 78=0) (hd : H 76=0) (he : H 77=0) (hp : H 113=1) :
    ∃ r,runFrom refresh (refreshBudget B count) ⟨refresh.start,H,A⟩=some r ∧
      r.steps≤refreshBudget B count ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A 113
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))) := by
  let H0:=Function.update H 113 0
  let A0:=Function.update A 113 (List.replicate B false)
  let next:=ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))
  obtain ⟨a,ar,as,ah,atapes⟩:=shift_run .left H A
  have ah' : a.final.heads=H0:=by simpa only [hp,HeadMove.apply] using ah
  obtain ⟨b,br,bs,bh,bt⟩:=erase_run B (A 113) H0 A hold
    (by intro j;fin_cases j <;> simp [erasePorts,driver,eraseLog])
    (by intro j;fin_cases j <;> simp [erasePorts,H0,hd,he])
  have br' : runFrom erase (2*B+4) (restart a.final erase.start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah',atapes]
    exact br
  obtain ⟨c,cr,cs,ch,ct⟩:=emit_run false B count H0 A0 hcount
    (by intro j;fin_cases j <;> simp [ports,A0,CloseoutRecoveryGrammarDriverReady.input,rawCount,log])
    (by intro j;fin_cases j <;> simp [ports,H0,hc,hl])
  have cr' : runFrom (emit false) (2*count+8) (restart b.final (emit false).start)=some c := by
    change runFrom _ _ ⟨_,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]
    exact cr
  change c.final.tapes=Function.update A0 113 next at ct
  have ct' : c.final.tapes=Function.update A 113 next:=by simpa only [A0,Function.update_idem] using ct
  obtain ⟨z,zr,zs,zh,zt⟩:=shift_run .right H0 (Function.update A 113 next)
  have returned : Function.update H0 113 (HeadMove.right.apply (H0 113))=H := by
    simp only [H0,Function.update_self,HeadMove.apply,Function.update_idem,Nat.zero_add]
    rw [←hp,Function.update_eq_self]
  rw [returned] at zh
  have zr' : runFrom (shift .right) 1 (restart c.final (shift .right).start)=some z := by
    change runFrom _ _ ⟨_,c.final.heads,c.final.tapes⟩=some z
    rw [ch,ct']
    exact zr
  have r1:=Composition.run_join (shift .left) erase _ _ _ a b ar br'
  have r2:=Composition.run_join (Composition.machine (shift .left) erase) (emit false) _ _ _
    (joinedReceipt a b) c r1 cr'
  have r3:=Composition.run_join (Composition.machine (Composition.machine (shift .left) erase) (emit false))
    (shift .right) _ _ _ (joinedReceipt (joinedReceipt a b) c) z r2 zr'
  refine ⟨joinedReceipt (joinedReceipt (joinedReceipt a b) c) z,r3,?_,zh,zt⟩
  change ((a.steps+1+b.steps)+1+c.steps)+1+z.steps≤refreshBudget B count
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_right as.le 1) bs) 1) cs) 1) zs.le

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
