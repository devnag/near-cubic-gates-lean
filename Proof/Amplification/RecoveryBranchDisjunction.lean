import Proof.Amplification.RecoveryRawBranchCanonical

/-! A paid physical disjunction for the two independently sound checker
branches. Running the branches in disjoint banks avoids a second semantic
classifier; every source datum and retained cursor stays in its own bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBranchDisjunction
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagMachine {t u : Nat} (a : Fin t) (b : Fin u) : Machine (t+u) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then
    some ⟨1,fun i=>if i=a.castAdd u then some (bits (a.castAdd u) || bits (b.natAdd t)) else none,fun _=>.stay⟩ else none

theorem flag_run {t u : Nat} (a : Fin t) (b : Fin u)
    (lh : Fin t→Nat) (lt : Fin t→List Bool) (rh : Fin u→Nat) (rt : Fin u→List Bool)
    (left right : Bool) (hlh : lh a=0) (hlt : lt a=[left]) (hrh : rh b=0) (hrt : rt b=[right]) :
    ∃ r,runFrom (flagMachine a b) 1 (RecoveryBankPair.cfg lh lt rh rt (0 : Fin 2))=some r ∧ r.steps=1 ∧
      r.final.heads=Fin.addCases lh rh ∧
      r.final.tapes=Function.update (Fin.addCases lt rt) (a.castAdd u) [left || right] := by
  have hs : step (flagMachine a b) (RecoveryBankPair.cfg lh lt rh rt (0 : Fin 2))=
      some (⟨1,Fin.addCases lh rh,Function.update (Fin.addCases lt rt) (a.castAdd u) [left || right]⟩ : Configuration (t+u) 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=a.castAdd u
      · subst i
        simp only [applyAction,ite_true,Function.update_self]
        simp [RecoveryBankPair.cfg,Configuration.scanned,hlh,hlt,hrh,hrt,readTapeBit,writeTapeBit]
      · simp only [applyAction,RecoveryBankPair.cfg,if_neg hi,Function.update_of_ne hi]
  obtain ⟨r,hr,hf,hn⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,hn,by rw [hf],by rw [hf]⟩

def sizes (s v : Nat) : Fin 3→Nat := ![s,v,2]
def programs {t u s v : Nat} (p : Machine t s) (q : Machine u v) (a : Fin t) (b : Fin u) :
    (j : Fin 3)→Machine (t+u) (sizes s v j)
  | ⟨0,_⟩=>RecoveryBankPair.leftMachine p
  | ⟨1,_⟩=>RecoveryBankPair.rightMachine q
  | ⟨2,_⟩=>flagMachine a b
  | ⟨n+3,h⟩=>False.elim (by omega)
def route {s v t : Nat} (j : Fin 3) (_ : Fin (sizes s v j)) (_ : Fin t→Bool) : Option (Fin 3) :=
  ![some 1,some 2,none] j
noncomputable def machine {t u s v : Nat} (p : Machine t s) (q : Machine u v) (a : Fin t) (b : Fin u) :=
  RecoveryCalls.machine (sizes s v) (programs p q a b) 0 route

end NearCubicWires.RepairOrdinary.RecoveryBranchDisjunction
