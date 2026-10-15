import Proof.CaseAnalysis.RecoveryGrammarFinishScan
import Proof.CaseAnalysis.RecoveryGrammarDriverReady

/-! Physically print the two finite-driver words from the retained raw
bound/candidate scalars, using the existing log. No scalar copy is introduced. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
open LocalBitMultitape RecoveryRootRound RecoveryExecution RecoveryBoundedGrammarCold
open RepairSource.ProjectionNormalization
open private install_eq from Proof.Amplification.RecoveryRowLookupCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ports (isBound : Bool) : Fin 3→Fin 114:=if isBound then ![102,112,78] else ![101,113,78]
def destination (isBound : Bool) : Fin 114:=if isBound then 112 else 113
noncomputable def emit (isBound : Bool):=RecoveryFocus.machine (ports isBound) (DimensionTemplate.machine true)

theorem injective (isBound : Bool) : Function.Injective (ports isBound) := by cases isBound <;> decide

theorem emit_run (isBound : Bool) (B n : ℕ) (H : Fin 114→ℕ) (A : Fin 114→List Bool)
    (hB : n+3≤B) (hin : ∀ j,A (ports isBound j)=CloseoutRecoveryGrammarDriverReady.input B n j)
    (hh : ∀ j,H (ports isBound j)=0) :
    ∃ r,runFrom (emit isBound) (2*n+8) ⟨(emit isBound).start,H,A⟩=some r ∧
      r.steps≤2*n+8 ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A (destination isBound)
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (n+1))) := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(CloseoutRecoveryGrammarDriverReady.ready B n hB).focus_at
    (ports isBound) (injective isBound) H A hin hh
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt]
  apply install_eq (ports isBound) (injective isBound)
  · intro j
    have hd : destination isBound=ports isBound 1:=by cases isBound <;> rfl
    rw [hd]
    by_cases hj : j=1
    · subst j
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne ((injective isBound).ne hj)]
      have same : CloseoutRecoveryGrammarDriverReady.output B n j=CloseoutRecoveryGrammarDriverReady.input B n j := by
        fin_cases j <;> simp_all [CloseoutRecoveryGrammarDriverReady.output,CloseoutRecoveryGrammarDriverReady.input]
      exact same.trans (hin j).symm
  · intro i hi
    have hd : destination isBound=ports isBound 1:=by cases isBound <;> rfl
    rw [hd]
    exact (Function.update_of_ne (Ne.symm (hi 1)) _ _).symm

def advanceBoth : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun _=>.right⟩ else none
def driverPorts : Fin 2→Fin 114:=![112,113]
noncomputable def position:=RecoveryFocus.machine driverPorts advanceBoth

theorem position_run (H : Fin 112→ℕ) (A : Fin 114→List Bool) :
    ∃ r,runFrom position 1 ⟨position.start,scanHeads H 0 0,A⟩=some r ∧ r.steps=1 ∧
      r.final.heads=scanHeads H 1 1 ∧ r.final.tapes=A := by
  let bits:=fun j=>A (driverPorts j)
  obtain ⟨a,ar,af,as⟩:=(Timed.single (by rfl)
    (show step advanceBoth (⟨0,fun _=>0,bits⟩ : Configuration 2 2)=some ⟨1,fun _=>1,bits⟩ from rfl)).run (by rfl)
  obtain ⟨r,rr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock driverPorts (by decide) advanceBoth _
    (scanHeads H 0 0) A ⟨0,fun _=>0,bits⟩ (by intro j;fin_cases j <;> rfl) (by intro j;rfl) a ar
  refine ⟨r,rr,rs.trans as,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=112) (n:=2) (fun j=>?_) (fun j=>?_) i
    · have hk : ∀ k,driverPorts k≠j.castAdd 2 := by
        intro k he
        have hv:=congrArg Fin.val he
        fin_cases k <;> simp [driverPorts] at hv <;> omega
      have k:=(keep (j.castAdd 2) hk).1
      have split : j.castAdd 2=(j.castAdd 1).castAdd 1:=by apply Fin.ext;rfl
      rw [split] at k ⊢
      simpa only [scanHeads,RecoveryBoundedGrammarDriver.heads,Fin.addCases_left] using k
    · fin_cases j
      · change r.final.heads (driverPorts 0)=1
        simpa only [af] using rh 0
      · change r.final.heads (driverPorts 1)=1
        simpa only [af] using rh 1
  · funext i
    by_cases h : ∃ j,driverPorts j=i
    · obtain ⟨j,rfl⟩:=h
      rw [rt,af]
    · exact (keep i (by simpa only [not_exists] using h)).2

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
