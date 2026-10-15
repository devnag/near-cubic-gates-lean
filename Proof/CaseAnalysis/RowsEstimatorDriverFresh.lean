import Proof.CaseAnalysis.RowsEstimatorDriverPower

/-! One ordinary arithmetic call into a fresh suffix of the driver bank.
Only its already owned input ports are shared. This routing lemma composes
the actual sum/product/power workers without copying unchanged scalars. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverFresh
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {N k m : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+(k+m) ≤ N)
    (i : Fin (k+m)) : Fin N :=
  if h:i.val<k then source ⟨i.val,h⟩ else ⟨base+i.val,by omega⟩
theorem source_slot {N k m : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+(k+m) ≤ N)
    (i : Fin k) : slots base source hB (i.castAdd m)=source i := by
  simp [slots,i.isLt]
theorem fresh_slot {N k m : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+(k+m) ≤ N)
    (i : Fin m) : (slots base source hB (i.natAdd k)).val=base+k+i.val := by
  simp [slots];omega

theorem injective {N k m : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+(k+m) ≤ N)
    (hinj : Function.Injective source) (hold : ∀ i,(source i).val<base) :
    Function.Injective (slots base source hB) := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  by_cases hi : i.val<k
  · by_cases hj : j.val<k
    · simp only [slots,hi,hj,dif_pos] at he
      exact congrArg (fun l : Fin k=>l.val) (hinj he)
    · simp only [slots,hi,hj,dif_pos] at hv
      have h:=hold ⟨i.val,hi⟩
      dsimp at hv
      omega
  · by_cases hj : j.val<k
    · simp only [slots,hi,hj,dif_pos] at hv
      have h:=hold ⟨j.val,hj⟩
      dsimp at hv
      omega
    · simp only [slots,hi,hj] at hv
      dsimp at hv
      omega

theorem run {N k m s : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+(k+m) ≤ N)
    (hinj : Function.Injective source) (hold : ∀ i,(source i).val<base)
    (worker : Machine (k+m) s) (fuel : ℕ) (A : Fin N → List Bool)
    (data : Fin k → List Bool) (localOut : Fin (k+m) → List Bool)
    (hr : ClockJoin.ReadyRun worker fuel
      (Fin.addCases (m:=k) (n:=m) (motive:=fun _=>List Bool) data (fun _=>[])) localOut)
    (keep : ∀ i,localOut (i.castAdd m)=data i)
    (hs : ∀ i,A (source i)=data i) (hf : ∀ i,base ≤ i.val → A i=[]) :
    ∃ out,ClockJoin.ReadyRun (RecoveryFocus.machine (slots base source hB) worker) fuel A out ∧
      (∀ i,i.val<base → out i=A i) ∧
      (∀ i,base+(k+m) ≤ i.val → out i=[]) ∧
      (∀ i : Fin m,out (slots base source hB (i.natAdd k))=localOut (i.natAdd k)) := by
  have hi:=injective base source hB hinj hold
  have h:=hr.focus (slots base source hB) hi A (by
    intro i
    refine Fin.addCases (m:=k) (n:=m) (fun j=>?_) (fun j=>?_) i
    · rw [source_slot]
      simpa only [Fin.addCases_left] using hs j
    · simp only [Fin.addCases_right]
      exact hf _ (by rw [fresh_slot];omega))
  refine ⟨_,h,?_,?_,?_⟩
  · intro i hib
    by_cases hex : ∃ j : Fin k,source j=i
    · obtain ⟨j,rfl⟩:=hex
      rw [←source_slot base source hB j,install_slot _ hi,keep]
      rw [source_slot]
      exact (hs j).symm
    · rw [install_other _ _ _ _ (by
        intro j he
        have hv:=congrArg Fin.val he
        dsimp only [slots] at he hv
        split_ifs at he hv with hj
        · exact hex ⟨⟨j.val,hj⟩,he⟩
        · dsimp at hv
          omega)]
  · intro i hib
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      dsimp only [slots] at hv
      split_ifs at hv with hj
      · have h:=hold ⟨j.val,hj⟩
        omega
      · have h:=j.isLt
        dsimp at hv
        omega)]
    exact hf i (by omega)
  · intro i
    exact install_slot _ hi _ _ _

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverFresh
