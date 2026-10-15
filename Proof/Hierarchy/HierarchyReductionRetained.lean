import Proof.PCP.ProjectionDimensionsFromInputBounds

/-! The existing hierarchy reduction already retains its physical length
driver and bound field. This parent exposes those endpoint facts for framing. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_retained (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3 ≤ Cpad)
    (ambient : Fin (tapes k) → List Bool) (hf : Fields k C x ambient)
    (hn : ambient (extra k 9)=List.replicate (length k C Cpad code x) true)
    (hc : ambient (extra k 11)=frame code) (hblank : HierarchyBound.Fresh ambient (base k+13)) :
    ∃ middle,ClockJoin.ReadyRun (headerProgram k) (2*length k C Cpad code x+4) ambient middle ∧
      middle (extra k 13)=HierarchyPadding.rawInput k C Cpad code x ∧
      Fields k C x middle ∧ middle (extra k 9)=List.replicate (length k C Cpad code x) true := by
  let b := binary (HierarchyBinary.width C (k+2) x.length) (HierarchyBinary.bound C (k+2) x.length)
  have hfit : (HierarchyHeader.header code x b).length ≤ length k C Cpad code x :=
    (HierarchyPadding.prefix_fits k C Cpad code x hpad).le
  obtain ⟨r,hr,_,h1,h2,h3,h4,_,hh,hs⟩ := HierarchyHeader.header_run (length k C Cpad code x) code x b hfit
  have h := (show ClockJoin.ReadyRun _ _ _ r.final.tapes from ⟨r,hr,rfl,hh,hs.le⟩).focus
    (headerSlots k) (header_injective k) ambient
    (by intro j; fin_cases j
        · exact hc
        · exact hf.1
        · exact hf.2
        · exact hn
        · exact hblank _ (by simp [headerSlots,extra])
        · exact hblank _ (by simp [headerSlots,extra]))
  exact ⟨_,h,(install_slot _ (header_injective k) _ _ 4).trans h4,
    ⟨(install_slot _ (header_injective k) _ _ 1).trans h1,
      (install_slot _ (header_injective k) _ _ 2).trans h2⟩,
    (install_slot _ (header_injective k) _ _ 3).trans h3⟩

theorem retained_run (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ out,ClockJoin.ReadyRun (machine k C Cpad code) (ordinaryBudget k C Cpad code x) (input k x) out ∧
      out (extra k 13)=HierarchyPadding.rawInput k C Cpad code x ∧
      Fields k C x out ∧ out (extra k 9)=List.replicate (length k C Cpad code x) true := by
  obtain ⟨a,ha,haf,hab⟩ := bound_ready k C x
  obtain ⟨b,hb,hbf,hba,hbb⟩ := allocation_ready k C Cpad code x a haf hab
  obtain ⟨c,hc,hcf,hcn,hcb⟩ := slice_ready k C Cpad code x b hbf hba hbb
  obtain ⟨d,hd,hdf,hdn,hdc,hdb⟩ := code_ready k C Cpad code x c hcf hcn hcb
  obtain ⟨e,he,heo,hef,hen⟩ := header_retained k C Cpad code x hpad d hdf hdn hdc hdb
  have h1 := ClockJoin.join _ _ _ _ _ _ _ ha hb
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 hc
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 hd
  have h4 := ClockJoin.join _ _ _ _ _ _ _ h3 he
  exact ⟨e,ClockJoin.enlarge _ _ _ _ _ h4 (budget_bound k C Cpad code x),heo,hef,hen⟩

end NearCubicWires.RepairOrdinary.HierarchyReduction
