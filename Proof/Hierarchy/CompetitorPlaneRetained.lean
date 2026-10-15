import Proof.Hierarchy.CompetitorPlaneWidth

/-! Expose the retained erase driver already present in the complete plane
store. This is the additional invariant needed by the next buffer reuse. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneRetained
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneStream CompetitorPlaneSign
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_capacity (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ out,ClockJoin.ReadyRun (CompetitorPlaneEntry.machine sign)
      (CompetitorPlaneEntry.readyBudget w xs.length) (CompetitorPlaneEntry.readyInput b w bits xs) out ∧
      out 21=List.replicate (CompetitorPlane.capacity w) true := by
  obtain ⟨base,store,hr,hs,ht,hstore⟩ := CompetitorPlaneEntry.cold_plane_run sign b w bits xs hb hbits hv
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run (CompetitorPlaneEntry.program sign) _ _ base hr
  have hc : 2*base.steps+2≤CompetitorPlaneEntry.readyBudget w xs.length := by
    unfold CompetitorPlaneEntry.readyBudget
    omega
  have hmore := runFrom_moreFuel (CompetitorPlaneEntry.machine sign) _
    (CompetitorPlaneEntry.readyBudget w xs.length-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,?_⟩
  exact (hrt 21).trans (congrFun ht 21) |>.trans hstore.erase

theorem sign_lift (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (produced : Fin 29 → List Bool)
    (ready : ClockJoin.ReadyRun (CompetitorPlaneEntry.machine sign)
      (CompetitorPlaneEntry.readyBudget w xs.length) (CompetitorPlaneEntry.readyInput b w bits xs) produced) :
    ClockJoin.ReadyRun machine (budget w xs.length) (input sign b w bits xs)
      (install native (input sign b w bits xs) produced) := by
  have focused := CompetitorRationalProducts.bounded_focus native native_injective _ _ _ ready
    (input sign b w bits xs) (by intro j; simp [input,native])
  let node : Fin 3 := if sign then 2 else 1
  let output := install native (input sign b w bits xs) produced
  have selected : ClockJoin.ReadyRun (programs node) (CompetitorPlaneEntry.readyBudget w xs.length)
      (input sign b w bits xs) output := by
    cases sign <;> exact focused
  obtain ⟨child,hchild,hct,hch,hcs⟩ := selected
  let start : Configuration 30 1 := initialConfiguration idle (input sign b w bits xs)
  have hsign : start.scanned 29=sign := by
    simp [start,Configuration.scanned,initialConfiguration,input,Fin.addCases,readTapeBit]
  have hstep := RecoveryCalls.return_step CompetitorPlaneSign.sizes programs 0 next 0 node start (by rfl)
    (by change (if start.scanned 29 then some 2 else some 1)=some node; rw [hsign]; cases sign <;> rfl)
  have hbranch : Timed machine 1 (initialConfiguration machine (input sign b w bits xs))
      (controlConfig (RecoveryCalls.code CompetitorPlaneSign.sizes node) (initialConfiguration (programs node) (input sign b w bits xs))) :=
    Timed.single (by simp [machine,RecoveryCalls.machine,RecoveryCalls.code,initialConfiguration]) hstep
  obtain ⟨time,htime,path⟩ := stop_receipt CompetitorPlaneSign.sizes programs 0 next node
    (CompetitorPlaneEntry.readyBudget w xs.length) _ child hchild (by cases sign <;> rfl)
  obtain ⟨r,hr,hf,hs⟩ := (hbranch.trans path).run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hcost : 1+time≤budget w xs.length := by unfold budget; omega
  have hmore := runFrom_moreFuel machine _ (budget w xs.length-(1+time)) _ r hr
  rw [Nat.add_sub_of_le hcost] at hmore
  refine ⟨r,hmore,?_,?_,by omega⟩
  · rw [hf]
    exact hct
  · intro i
    rw [hf]
    exact hch i

theorem capacity_preserved (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits)
    (out : Fin 30 → List Bool)
    (ready : ClockJoin.ReadyRun machine (budget w xs.length) (input sign b w bits xs) out) :
    out 21=List.replicate (CompetitorPlane.capacity w) true := by
  obtain ⟨produced,child,h21⟩ := entry_capacity sign b w bits xs hb hbits hv
  obtain ⟨r,hr,ht,_,_⟩ := sign_lift sign b w bits xs produced child
  obtain ⟨r',hr',ht',_,_⟩ := ready
  rw [hr] at hr'
  have he : r=r' := Option.some.inj hr'
  subst r'
  have hout : out=install native (input sign b w bits xs) produced := ht'.symm.trans ht
  rw [hout]
  exact (install_slot native native_injective _ _ 21).trans h21

end NearCubicWires.RepairOrdinary.CompetitorPlaneRetained
