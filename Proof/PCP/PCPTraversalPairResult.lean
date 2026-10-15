import Proof.PCP.PCPTraversalState

/-! Whole clear/pair/clear/copy blocks, with the actual common capacity and
work-tape invariant retained for the next subtree call. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def paired (cap log : ℕ) (ambient : Fin 128 → List Bool)
    (localOut : Fin 38 → List Bool) := install pairSlots (cleared bank cap log ambient) localOut
noncomputable def pairResult (cap log : ℕ) (bits : List Bool) (ambient : Fin 128 → List Bool)
    (localOut : Fin 38 → List Bool) :=
  copiedResult cap (max log (cap+1)) bits (paired cap log ambient localOut)

theorem paired_driver (cap log : ℕ) (ambient : Fin 128 → List Bool)
    (localOut : Fin 38 → List Bool) : paired cap log ambient localOut 28=List.replicate cap true := by
  exact (install_other pairSlots _ _ 28 (fun j => pair_ne j 28 (by decide) (by decide) (by decide))).trans
    (cleared_driver bank bank_injective (fun j => (clear_preserves_drivers j).1)
      (fun j => (clear_preserves_drivers j).2) cap log ambient)
theorem paired_log (cap log : ℕ) (ambient : Fin 128 → List Bool)
    (localOut : Fin 38 → List Bool) :
    paired cap log ambient localOut 127=List.replicate (max log (cap+1)) false := by
  exact (install_other pairSlots _ _ 127 (fun j => pair_ne j 127 (by decide) (by decide) (by decide))).trans
    (cleared_log bank bank_injective (fun j => (clear_preserves_drivers j).1)
      (fun j => (clear_preserves_drivers j).2) cap log ambient)

theorem WorkBound.paired {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (localOut : Fin 38 → List Bool)
    (hout : ∀ i,(localOut i).length≤cap) : WorkBound cap (paired cap log ambient localOut) :=
  (hb.clear bank bank_injective (fun j => (clear_preserves_drivers j).1)
    (fun j => (clear_preserves_drivers j).2)).install pairSlots localOut (fun j _ _ => hout j)

theorem WorkBound.copiedResult {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (bits : List Bool) (hbits : 2*bits.length+1≤cap) :
    WorkBound cap (copiedResult cap log bits ambient) := by
  apply (hb.clear resultSlots resultSlots_injective (by decide) (by decide)).install resultCopySlots
  intro j _ _
  fin_cases j
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl hbits
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl hbits
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

theorem pair_result_calls (j k l m n : Fin 39)
    (hj : call j=clear bank) (hk : call k=focused pairSlots PCPPairCanonical.machine)
    (hl : call l=clear resultSlots) (hm : call m=copyField 65 77 91)
    (hjk : ∀ q scanned,next j q scanned=some k)
    (hkl : ∀ q scanned,next k q scanned=some l)
    (hlm : ∀ q scanned,next l q scanned=some m)
    (hmn : ∀ q scanned,next m q scanned=some n)
    (cap log : ℕ) (left right : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hpos : 0<Nat.pair (value left) (value right))
    (hcap : PCPPairCanonical.budget left right+1≤cap)
    (hb : WorkBound cap ambient)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hleft : ambient 83=ZeroPadding.pad cap (frame left))
    (hright : ambient 84=ZeroPadding.pad cap (frame right))
    (hhbank : ∀ i,heads (bank i)=0) (hhpair : ∀ i,heads (pairSlots i)=0)
    (hhresult : ∀ i,heads (resultCopySlots i)=0)
    (hhd : heads 28=0) (hhl : heads 127=0) :
    ∃ localOut : Fin 38 → List Bool,
      Path j n (7*cap+16) heads ambient heads
        (pairResult cap log (Nat.pair (value left) (value right)).bits ambient localOut) ∧
      localOut 26=ZeroPadding.pad cap (frame (Nat.pair (value left) (value right)).bits) ∧
      (∀ i,(localOut i).length≤cap) ∧
      WorkBound cap (pairResult cap log (Nat.pair (value left) (value right)).bits ambient localOut) := by
  obtain ⟨localOut,hpair,hfield,hsize⟩ := pair_clear_calls j k l hj hk hjk hkl cap log left right
    heads ambient hpos hcap
    (fun i => hb (bank i) (by simp only [bank]; omega) (fun h => (clear_preserves_drivers i).2 h))
    hdriver hlog hleft hright hhbank hhpair hhd hhl
  have hframe : 2*(Nat.pair (value left) (value right)).bits.length+1≤cap := by
    have h := hsize 26
    rw [hfield,ZeroPadding.pad_length,frame_length] at h
    omega
  have hpbound := hb.paired localOut hsize (log:=log)
  have hcopy := result_clear_calls l m n hl hm hlm hmn cap (max log (cap+1))
    (Nat.pair (value left) (value right)).bits heads (paired cap log ambient localOut) hframe
    (by intro i; fin_cases i; exact hpbound 77 (by decide) (by decide); exact hpbound 91 (by decide) (by decide))
    (paired_driver cap log ambient localOut) (paired_log cap log ambient localOut)
    ((install_slot pairSlots pair_injective (cleared bank cap log ambient) localOut 26).trans hfield)
    hhresult hhd hhl
  have hpath := hpair.trans hcopy
  refine ⟨localOut,hpath.mono ?_,hfield,hsize,hpbound.copiedResult _ hframe⟩
  omega

theorem pair_leaf_result_path (cap log : ℕ) (left right : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hpos : 0<Nat.pair (value left) (value right))
    (hcap : PCPPairCanonical.budget left right+1≤cap)
    (hb : WorkBound cap ambient)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hleft : ambient 83=ZeroPadding.pad cap (frame left))
    (hright : ambient 84=ZeroPadding.pad cap (frame right))
    (hhbank : ∀ i,heads (bank i)=0) (hhpair : ∀ i,heads (pairSlots i)=0)
    (hhresult : ∀ i,heads (resultCopySlots i)=0)
    (hhd : heads 28=0) (hhl : heads 127=0) :
    ∃ localOut : Fin 38 → List Bool,
      Path 5 9 (7*cap+16) heads ambient heads
        (pairResult cap log (Nat.pair (value left) (value right)).bits ambient localOut) ∧
      localOut 26=ZeroPadding.pad cap (frame (Nat.pair (value left) (value right)).bits) ∧
      (∀ i,(localOut i).length≤cap) ∧
      WorkBound cap (pairResult cap log (Nat.pair (value left) (value right)).bits ambient localOut) :=
  pair_result_calls 5 6 7 8 9 rfl rfl rfl rfl (by intro q scanned; simp [next])
    (by intro q scanned; simp [next]) (by intro q scanned; simp [next])
    (by intro q scanned; simp [next]) cap log left right heads ambient hpos hcap hb hdriver hlog
    hleft hright hhbank hhpair hhresult hhd hhl

end NearCubicWires.RepairOrdinary.PCPTraversal
