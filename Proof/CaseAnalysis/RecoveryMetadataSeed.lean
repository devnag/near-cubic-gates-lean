import Proof.CaseAnalysis.RecoveryGrammarBudget
import Proof.Amplification.RecoveryEraseConstant

/-! The cold scalar bank begins with actual retained raw inputs. This
fixed literal printer pays for the single one used by the remaining additions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
open LocalBitMultitape RecoveryRootRound RecoveryBoundedGrammarAdvance
open RecoveryBoundedGrammarScalarAdd (unary)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words (B : ℕ) (v : Fin 33 → ℕ) : Fin 33 → List Bool := fun i => unary B (v i)
def seedSlots : Fin 2 → Fin 37 := ![11,34]
noncomputable def seed := RecoveryFocus.machine seedSlots (RecoveryEraseConstant.resetMachine 1)

theorem one_ready (B : ℕ) (hB : 1 ≤ B) :
    ClockJoin.ReadyRun (RecoveryEraseConstant.resetMachine 1) 4
      (fun _ => List.replicate B false)
      (![unary B 1,List.replicate B false] : Fin 2 → List Bool) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryEraseConstant.constant_ready 1
  obtain ⟨p,hp,pt,ps,_⟩ := ZeroPadding.run_config (RecoveryEraseConstant.resetMachine 1)
    (fun _ => B) _ _ r hr
  have hi : ZeroPadding.config (fun _ : Fin 2 => B)
      (initialConfiguration (RecoveryEraseConstant.resetMachine 1) (fun _ => [])) =
      initialConfiguration (RecoveryEraseConstant.resetMachine 1) (fun _ => List.replicate B false) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; simp [ZeroPadding.config,initialConfiguration,ZeroPadding.pad]
  rw [hi] at hp
  refine ⟨p,hp,?_,?_,ps.le.trans hs.le⟩
  · rw [pt]
    change (fun i => ZeroPadding.pad B (r.final.tapes i)) = _
    rw [ht]
    funext i
    fin_cases i
    · rfl
    · change ZeroPadding.pad B (List.replicate 1 false) = List.replicate B false
      simp only [ZeroPadding.pad,List.length_replicate,← List.replicate_add]
      congr 1
      omega
  · intro i
    rw [pt]
    exact hh i

theorem seed_ready (B : ℕ) (v : Fin 33 → ℕ) (hv : v 11 = 0) (hB : 1 ≤ B) :
    ClockJoin.ReadyRun seed 4 (bank B (words B v))
      (bank B (words B (Function.update v 11 1))) := by
  have h := (one_ready B hB).focus seedSlots (by decide) (bank B (words B v)) (by
    intro j
    fin_cases j
    · change unary B (v 11) = List.replicate B false
      simp [hv,unary,ZeroPadding.pad]
    · rfl)
  have he : install seedSlots (bank B (words B v)) ![unary B 1,List.replicate B false] =
      bank B (words B (Function.update v 11 1)) := by
    apply HierarchyWidth.install_eq seedSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      refine Fin.addCases (m:=33) (n:=4) (motive:=fun i => (∀ j,seedSlots j ≠ i) →
        (bank B (words B (Function.update v 11 1))) i = (bank B (words B v)) i)
        (fun j hjoutside => ?_) (fun _ _ => by simp only [bank,Fin.addCases_right]) i hi
      · have hj : j ≠ 11 := by
          intro he
          subst j
          exact hjoutside 0 rfl
        simp only [bank,Fin.addCases_left,words,Function.update_of_ne hj]
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
