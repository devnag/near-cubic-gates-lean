import Proof.CaseAnalysis.RowsEstimatorDriverFresh

/-! Routing the original variable-arity unary workers into the driver bank.
Inputs are shared read-only ports; all other worker tapes occupy fresh cells. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPorts
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {N t k : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+t ≤ N)
    (i : Fin t) : Fin N :=
  if h : i.val<k then source ⟨i.val,h⟩ else ⟨base+i.val,by omega⟩
theorem injective {N t k : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+t ≤ N)
    (hinj : Function.Injective source) (hold : ∀ i,(source i).val<base) :
    Function.Injective (slots base source hB) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  by_cases hi : i.val<k
  · by_cases hj : j.val<k
    · simp only [slots,hi,hj,dif_pos] at he
      exact congrArg (fun l : Fin k => l.val) (hinj he)
    · simp only [slots,hi,hj,dif_pos] at hv
      have h := hold ⟨i.val,hi⟩
      dsimp at hv
      omega
  · by_cases hj : j.val<k
    · simp only [slots,hi,hj,dif_pos] at hv
      have h := hold ⟨j.val,hj⟩
      dsimp at hv
      omega
    · simp only [slots,hi,hj] at hv
      dsimp at hv
      omega

theorem run {N t k s : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+t ≤ N)
    (hinj : Function.Injective source) (hold : ∀ i,(source i).val<base)
    (worker : Machine t s) (fuel : ℕ) (A : Fin N → List Bool)
    (localIn localOut : Fin t → List Bool)
    (hr : ClockJoin.ReadyRun worker fuel localIn localOut)
    (hs : ∀ i,if h : i.val<k then A (source ⟨i.val,h⟩)=localIn i else localIn i=[])
    (keep : ∀ i,i.val<k → localOut i=localIn i)
    (hf : ∀ i,base ≤ i.val → A i=[]) :
    ∃ out,ClockJoin.ReadyRun (RecoveryFocus.machine (slots base source hB) worker) fuel A out ∧
      (∀ i,i.val<base → out i=A i) ∧
      (∀ i,base+t ≤ i.val → out i=[]) ∧
      (∀ i,out (slots base source hB i)=localOut i) := by
  have hi := injective base source hB hinj hold
  have h := hr.focus (slots base source hB) hi A (by
    intro i
    have hin := hs i
    unfold slots
    split_ifs with hj
    · simpa only [hj,dif_pos] using hin
    · rw [hf _ (by dsimp;omega)]
      have he : localIn i=[] := by simpa [hj] using hin
      exact he.symm)
  refine ⟨_,h,?_,?_,fun i => install_slot _ hi _ _ i⟩
  · intro i hib
    by_cases hex : ∃ j : Fin t,slots base source hB j=i
    · obtain ⟨j,rfl⟩ := hex
      have hj : j.val<k := by
        by_contra hj
        simp only [slots,hj] at hib
        dsimp at hib
        omega
      rw [install_slot _ hi,keep j hj]
      have hjh := hs j
      simp only [hj,dif_pos] at hjh
      simpa only [slots,hj,dif_pos] using hjh.symm
    · exact install_other _ _ _ _ (by simpa using hex)
  · intro i hib
    rw [install_other _ _ _ _ (by
      intro j he
      have hv := congrArg Fin.val he
      dsimp only [slots] at hv
      split_ifs at hv with hj
      · have h := hold ⟨j.val,hj⟩
        omega
      · have h := j.isLt
        dsimp at hv
        omega)]
    exact hf i (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPorts
