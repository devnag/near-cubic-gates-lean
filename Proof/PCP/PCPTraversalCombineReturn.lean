import Proof.PCP.PCPTraversalCombine

/-! The whole right-child return and canonical combine, stopping at node9
with the caller's continuation restored and both child codes combined. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rightReturned (continuation : List Bool) (z : ℕ) (ambient : Fin 128 → List Bool) :=
  install ![81] ambient (fun _ => continuation++List.replicate (z+2) false)
noncomputable def combineReturnHeads (pre continuation : List Bool) (heads : Fin 128 → ℕ) :=
  installedHeads leftPopSlots (installedHeads ![81] heads (fun _ => continuation.length)) ![pre.length,0,0]

theorem combine_return_path (left right pre continuation : List Bool) (cap leftZeros continuationZeros log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 5≤cap) (hl : 2*left.length+2≤cap) (hr : 2*right.length+1≤cap)
    (hpos : 0<Nat.pair (value left) (value right))
    (hpair : PCPPairCanonical.budget left right+1≤cap)
    (htag : PCPPairCanonical.budget (2 : ℕ).bits (Nat.pair (value left) (value right)).bits+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hstack : ambient 82=pre++(frame left).reverse++List.replicate leftZeros false)
    (hstackHead : heads 82=pre.length+2*left.length+1)
    (hright : ambient 77=ZeroPadding.pad cap (frame right))
    (hcont : ambient 81=continuation++true::true::List.replicate continuationZeros false)
    (hhcont : heads 81=continuation.length+2) (hhd : heads 28=0) :
    ∃ first second : Fin 38 → List Bool,
      Path 9 9 (24*cap+77) heads ambient (combineReturnHeads pre continuation heads)
        (combinedOutput left right pre cap leftZeros log (rightReturned continuation continuationZeros ambient) first second) ∧
      WorkBound cap (combinedOutput left right pre cap leftZeros log
        (rightReturned continuation continuationZeros ambient) first second) ∧
      WorkingHeads (combineReturnHeads pre continuation heads) := by
  let returned := rightReturned continuation continuationZeros ambient
  let moved := installedHeads ![81] heads (fun _ => continuation.length)
  have returned_bound : WorkBound cap returned := by
    apply hb.install ![81]
    intro i _ _
    have h := hb 81 (by decide) (by decide)
    rw [hcont] at h
    simp only [List.length_append,List.length_cons,List.length_replicate] at h ⊢
    omega
  have moved_heads : WorkingHeads moved := by
    apply hh.install ![81]
    intro i _ _ h81 _
    fin_cases i
    exact False.elim (h81 rfl)
  have returned_driver : returned 28=List.replicate cap true :=
    (install_other ![81] ambient (fun _ => continuation++List.replicate (continuationZeros+2) false)
      28 (by decide)).trans hdriver
  have returned_log : returned 127=List.replicate log false :=
    (install_other ![81] ambient (fun _ => continuation++List.replicate (continuationZeros+2) false)
      127 (by decide)).trans hlog
  have returned_result : returned 77=ZeroPadding.pad cap (frame right) :=
    (install_other ![81] ambient (fun _ => continuation++List.replicate (continuationZeros+2) false)
      77 (by decide)).trans hright
  have returned_stack : returned 82=pre++(frame left).reverse++List.replicate leftZeros false :=
    (install_other ![81] ambient (fun _ => continuation++List.replicate (continuationZeros+2) false)
      82 (by decide)).trans hstack
  have moved_stack : moved 82=pre.length+2*left.length+1 :=
    (installedHeads_other ![81] heads (fun _ => continuation.length) 82 (by decide)).trans hstackHead
  have moved_driver : moved 28=0 :=
    (installedHeads_other ![81] heads (fun _ => continuation.length) 28 (by decide)).trans hhd
  have hreturn := return_right_path continuation continuationZeros heads ambient hcont hhcont
  obtain ⟨first,second,hcombine,hbound,hheads⟩ := combine_path left right pre cap leftZeros log moved returned
    hc hl hr hpos hpair htag returned_bound moved_heads returned_driver returned_log returned_stack moved_stack
    returned_result moved_driver
  exact ⟨first,second,(hreturn.trans hcombine).mono (by omega),hbound,hheads⟩

end NearCubicWires.RepairOrdinary.PCPTraversal
