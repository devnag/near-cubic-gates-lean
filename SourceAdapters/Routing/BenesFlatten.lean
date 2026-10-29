import SourceAdapters.Routing.BenesStages
import SourceAdapters.Routing.SwitchChain

/-! Flatten recursive settings into the exact range/foldl path of the routing interface. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.BenesRecursive

theorem combine_prefix {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) (x : BitVec (k + 2))
    (j : ℕ) (hj : j ≤ switchCount (k + 1)) :
    let p := pairSwitch input (LanePair.split x)
    LanePair.split (SwitchChain.path (stageMap (k + 2) (combine input output lo hi)) (j + 1) x) =
      (if p.2 then SwitchChain.path (stageMap (k + 1) hi) j p.1
        else SwitchChain.path (stageMap (k + 1) lo) j p.1, p.2) := by
  dsimp only
  induction j with
  | zero =>
      rw [SwitchChain.path_succ, SwitchChain.path_zero, combine_first]
      simp only [SwitchChain.path_zero, ite_self]
  | succ j ih =>
      rw [SwitchChain.path_succ, combine_inner input output lo hi j (by omega), ih (by omega)]
      cases (pairSwitch input (LanePair.split x)).2 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, SwitchChain.path_succ]

theorem combine_path {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) (x : BitVec (k + 2)) :
    let p := pairSwitch input (LanePair.split x)
    path (k + 2) (combine input output lo hi) x =
      LanePair.join (pairSwitch output
        (if p.2 then path (k + 1) hi p.1 else path (k + 1) lo p.1, p.2)) := by
  dsimp only
  apply (LanePair.equiv (k + 1)).injective
  change LanePair.split
      (SwitchChain.path (stageMap (k + 2) (combine input output lo hi)) (switchCount (k + 2)) x) =
    LanePair.split (LanePair.join _)
  rw [LanePair.split_join, switchCount_step, SwitchChain.path_succ, combine_last,
    combine_prefix input output lo hi x (switchCount (k + 1)) le_rfl]
  rfl

/-- The actual settings of every recursive configuration. -/
def Config.settings : {k : ℕ} → Config k → Settings k
  | _, .base setting => fun _ _ => setting
  | _, .step input output lo hi => combine input output lo.settings hi.settings

theorem Config.coherent {k : ℕ} (C : Config k) : Coherent k C.settings := by
  induction C with
  | base setting => intro j hj x; rfl
  | step input output lo hi hlo hhi => exact combine_coherent input output _ _ hlo hhi

/-- Flattening preserves the complete permutation, for every input lane. -/
theorem Config.path_eq_perm {k : ℕ} (C : Config k) (x : BitVec k) :
    path k C.settings x = C.perm x := by
  induction C with
  | base setting =>
      change stageMap 1 (fun _ _ => setting) 0 x =
        (LanePair.equiv 0).symm (pairSwitch (fun _ => setting) (LanePair.split x))
      apply (LanePair.equiv 0).injective
      change LanePair.split (stageMap 1 (fun _ _ => setting) 0 x) =
        LanePair.split (LanePair.join (pairSwitch (fun _ => setting) (LanePair.split x)))
      rw [LanePair.split_join]
      exact split_pair_stage _ 0 (fun _ => setting) (dimension_first _) (fun _ => rfl) x
  | @step k input output lo hi hlo hhi =>
      change path (k + 2) (combine input output lo.settings hi.settings) x = _
      rw [combine_path, Config.perm_step_apply]
      apply congrArg LanePair.join
      apply congrArg (pairSwitch output)
      change
        (if (pairSwitch input (LanePair.split x)).2 then
          path (k + 1) hi.settings (pairSwitch input (LanePair.split x)).1
        else path (k + 1) lo.settings (pairSwitch input (LanePair.split x)).1,
          (pairSwitch input (LanePair.split x)).2) =
        ((if (pairSwitch input (LanePair.split x)).2 then hi.perm else lo.perm)
          (pairSwitch input (LanePair.split x)).1, (pairSwitch input (LanePair.split x)).2)
      rw [hlo, hhi]
      cases (pairSwitch input (LanePair.split x)).2 <;> rfl

end NearCubicGates.Adapters.Routing.BenesRecursive
