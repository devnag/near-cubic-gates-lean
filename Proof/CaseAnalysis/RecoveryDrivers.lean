import Proof.CaseAnalysis.RecoveryArity
import Proof.CaseAnalysis.RecoveryGrammarDriverReady

/-! Print both original grammar drivers and use the first one immediately
for the physical description arity, before positioning any scan head. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdDrivers
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (bound width B : ℕ) (bd cd arity : List Bool) : Fin 7→List Bool:=
  ![ZeroPadding.pad B (List.replicate bound true),List.replicate B false,
    ZeroPadding.pad B (List.replicate width true),bd,cd,arity,List.replicate B false]
def blank (B : ℕ):=List.replicate B false
def driver (B n : ℕ):=ZeroPadding.pad B (CompareMachine.word (n+1))
def start (bound width B : ℕ):=bank bound width B (blank B) (blank B) (blank B)
def boundData (bound width B : ℕ):=bank bound width B (driver B bound) (blank B) (blank B)
def countData (bound width B : ℕ):=bank bound width B (driver B bound) (driver B 0) (blank B)
def output (bound width B : ℕ):=bank bound width B (driver B bound) (driver B 0)
  (ZeroPadding.pad B (List.replicate (width*(bound+1)) true))
def boundSlots : Fin 3→Fin 7:=![0,3,6]
def countSlots : Fin 3→Fin 7:=![1,4,6]
def aritySlots : Fin 4→Fin 7:=![2,3,5,6]
noncomputable def first:=RecoveryFocus.machine boundSlots (RepairSource.ProjectionNormalization.DimensionTemplate.machine true)
noncomputable def second:=RecoveryFocus.machine countSlots (RepairSource.ProjectionNormalization.DimensionTemplate.machine true)
noncomputable def last:=RecoveryFocus.machine aritySlots ClockUnaryProduct.machine
noncomputable def machine:=Composition.machine (Composition.machine first second) last
def budget (B : ℕ):=16*(B+2)

theorem bound_ready (bound width B : ℕ) (hB : bound+3≤B) :
    ClockJoin.ReadyRun first (2*bound+8) (start bound width B) (boundData bound width B) := by
  have h:=(CloseoutRecoveryGrammarDriverReady.ready B bound hB).focus boundSlots (by decide)
    (start bound width B) (by intro j;fin_cases j <;> rfl)
  have hi : install boundSlots (start bound width B) (CloseoutRecoveryGrammarDriverReady.output B bound)=
      boundData bound width B := by
    funext i;fin_cases i <;> first
      | exact install_slot boundSlots (by decide) _ _ 0
      | exact install_slot boundSlots (by decide) _ _ 1
      | exact install_slot boundSlots (by decide) _ _ 2
      | exact install_other boundSlots _ _ _ (by decide)
  rw [hi] at h
  exact h

theorem count_ready (bound width B : ℕ) (hB : 3≤B) :
    ClockJoin.ReadyRun second 8 (boundData bound width B) (countData bound width B) := by
  have base:=CloseoutRecoveryGrammarDriverReady.ready B 0 hB
  have hz : ZeroPadding.pad B (List.replicate 0 true)=blank B := by simp [ZeroPadding.pad,blank]
  simp only [CloseoutRecoveryGrammarDriverReady.input,CloseoutRecoveryGrammarDriverReady.output,hz] at base
  have h:=base.focus countSlots (by decide) (boundData bound width B) (by intro j;fin_cases j <;> rfl)
  have hi : install countSlots (boundData bound width B)
      ![blank B,driver B 0,blank B]=countData bound width B := by
    funext i;fin_cases i <;> first
      | exact install_slot countSlots (by decide) _ _ 0
      | exact install_slot countSlots (by decide) _ _ 1
      | exact install_slot countSlots (by decide) _ _ 2
      | exact install_other countSlots _ _ _ (by decide)
  change ClockJoin.ReadyRun second 8 (boundData bound width B)
    (install countSlots (boundData bound width B) ![blank B,driver B 0,blank B]) at h
  rw [hi] at h
  exact h

theorem arity_ready (bound width B : ℕ) (hB : width*(2*(bound+1)+3)+2≤B) :
    ClockJoin.ReadyRun last (RecoveryBoundedColdArity.budget width (bound+1))
      (countData bound width B) (output bound width B) := by
  have h:=(RecoveryBoundedColdArity.ready width (bound+1) B hB).focus aritySlots (by decide)
    (countData bound width B) (by
      intro j;fin_cases j
      · rfl
      · rfl
      · change List.replicate B false=ZeroPadding.pad B [];simp [ZeroPadding.pad]
      · change List.replicate B false=ZeroPadding.pad B [];simp [ZeroPadding.pad])
  have hi : install aritySlots (countData bound width B) (RecoveryBoundedColdArity.output width (bound+1) B)=
      output bound width B := by
    funext i;fin_cases i <;> first
      | exact install_slot aritySlots (by decide) _ _ 0
      | exact install_slot aritySlots (by decide) _ _ 1
      | exact install_slot aritySlots (by decide) _ _ 2
      | exact install_slot aritySlots (by decide) _ _ 3
      | exact install_other aritySlots _ _ _ (by decide)
  rw [hi] at h
  exact h

theorem ready (bound width B : ℕ) (hbound : bound+3≤B)
    (hprod : width*(2*(bound+1)+3)+2≤B) :
    ClockJoin.ReadyRun machine (budget B) (start bound width B) (output bound width B) := by
  have a:=ClockJoin.join first second _ _ _ _ _ (bound_ready bound width B hbound)
    (count_ready bound width B (by omega))
  have h:=ClockJoin.join (Composition.machine first second) last _ _ _ _ _ a
    (arity_ready bound width B hprod)
  exact ClockJoin.enlarge _ _ _ _ _ h (by unfold budget RecoveryBoundedColdArity.budget;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdDrivers
