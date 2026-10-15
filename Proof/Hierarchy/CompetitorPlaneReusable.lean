import Proof.Hierarchy.CompetitorPlanePaddedEntry
import Proof.Hierarchy.CompetitorPlaneRetained

/-! Repeated signed-plane calls reuse their whole finite buffers. One erase
per plane clears the output bank and scratch, while count, old P/N, factor,
sign and dimension tapes remain in place. All clearing is actual execution. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneReusable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 30) : Fin 32 := i.castAdd 2
def retained (i : Fin 32) : Prop := i=0 ∨ i=9 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=27 ∨ i=29
def workSlot : Fin 22 → Fin 32 := ![1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,17,22,23,24,25,26,28]
def eraseSlot : Fin 24 → Fin 32 := Fin.addCases (m := 22) (n := 2) workSlot ![30,31]
def eraseInput (D : ℕ) (backing : Fin 22 → List Bool) : Fin 24 → List Bool :=
  CompetitorPlaneWorkspace.eraseInput D backing
noncomputable def clearProgram := RecoveryFocus.machine eraseSlot (RecoveryScratchErase.resetMachine 22)
noncomputable def callProgram := RecoveryFocus.machine native CompetitorPlaneSign.machine
noncomputable def machine := Composition.machine clearProgram callProgram
def capacity := CompetitorPlanePaddedEntry.capacity
def budget (w n : ℕ) := 2*capacity w n+5+CompetitorPlaneSign.budget w n
def input := CompetitorPlanePaddedEntry.input
structure Compatible (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (ambient : Fin 32 → List Bool) : Prop where
  retained : ∀ i,retained (native i) → ambient (native i)=input sign b w bits xs i
  support : ∀ j,(ambient (workSlot j)).length≤capacity w xs.length
  driver : ambient 30=List.replicate (capacity w xs.length) true
  reset : ambient 31=List.replicate (capacity w xs.length+1) false

theorem erase_injective : Function.Injective eraseSlot := by decide
theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 32 => a.val) h)
theorem erase_avoids : ∀ (i : Fin 30),retained (native i) → ∀ j,eraseSlot j≠native i := by unfold retained; decide
theorem work_covers : ∀ (i : Fin 30),¬retained (native i) → ∃ j,workSlot j=native i := by unfold retained; decide
theorem native_other (i : Fin 30) : native i≠30 ∧ native i≠31 := by
  constructor
  · intro h
    have hv:=congrArg (fun a : Fin 32 => a.val) h
    change i.val=30 at hv
    omega
  · intro h
    have hv:=congrArg (fun a : Fin 32 => a.val) h
    change i.val=31 at hv
    omega

theorem input_work (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell) (i : Fin 30)
    (hi : ¬retained (native i)) : input sign b w bits xs i=List.replicate (capacity w xs.length) false := by
  fin_cases i <;>
    simp_all [retained,native,input,CompetitorPlanePaddedEntry.input,CompetitorPlaneSign.input,
      CompetitorPlaneEntry.readyInput,CompetitorPlaneEntry.input,CompetitorPlaneEntry.extendTapes,
      coldInput,Fin.addCases,ZeroPadding.pad,capacity]

theorem padded_capacity (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits)
    (out : Fin 30 → List Bool)
    (ready : ClockJoin.ReadyRun CompetitorPlaneSign.machine (CompetitorPlaneSign.budget w xs.length)
      (input sign b w bits xs) out) : out 21=input sign b w bits xs 21 := by
  obtain ⟨produced,child,_⟩ := CompetitorPlaneSign.run_plane sign b w bits xs hb hbits hv
  have h21 := CompetitorPlaneRetained.capacity_preserved sign b w bits xs hb hbits hv produced child
  obtain ⟨base,hr,ht,_,_⟩ := child
  obtain ⟨r,hrun,hf,_,_⟩ := ZeroPadding.run_config CompetitorPlaneSign.machine
    (fun _ => capacity w xs.length) _ _ base hr
  obtain ⟨r',hr',ht',_,_⟩ := ready
  change run CompetitorPlaneSign.machine (CompetitorPlaneSign.budget w xs.length)
    (input sign b w bits xs)=some r at hrun
  rw [hrun] at hr'
  have he : r=r' := Option.some.inj hr'
  subst r'
  rw [← ht',hf]
  simp [ZeroPadding.config,ht,h21,input,CompetitorPlanePaddedEntry.input,
    CompetitorPlaneSign.input,CompetitorPlaneEntry.readyInput,CompetitorPlaneEntry.input,
    CompetitorPlaneEntry.extendTapes,coldInput,Fin.addCases,capacity]

theorem clear_ready (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (ambient : Fin 32 → List Bool) (h : Compatible sign b w bits xs ambient) :
    ∃ out,ClockJoin.ReadyRun clearProgram (2*capacity w xs.length+4) ambient out ∧
      (∀ i,out (native i)=input sign b w bits xs i) ∧ out 30=ambient 30 ∧ out 31=ambient 31 := by
  let D := capacity w xs.length
  have child : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 22) (2*D+4)
      (eraseInput D (fun j => ambient (workSlot j))) (eraseInput D (fun _ => List.replicate D false)) := by
    obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready D (D+1) (fun j => ambient (workSlot j)) h.support
    exact ⟨r,hr,by simpa only [eraseInput,CompetitorPlaneWorkspace.eraseInput,max_self] using ht,hh,hs.le⟩
  have hin : ∀ j,ambient (eraseSlot j)=eraseInput D (fun a => ambient (workSlot a)) j := by
    intro j
    refine Fin.addCases (m := 22) (n := 2) ?_ ?_ j
    · intro a
      fin_cases a <;> rfl
    · intro a
      fin_cases a <;> simp [eraseSlot,eraseInput,CompetitorPlaneWorkspace.eraseInput,Fin.addCases,h.driver,h.reset,D]
  have focused := CompetitorRationalProducts.bounded_focus eraseSlot erase_injective _ _ _ child ambient hin
  let out := install eraseSlot ambient (eraseInput D (fun _ => List.replicate D false))
  refine ⟨out,focused,?_,?_,?_⟩
  · intro i
    by_cases hi : retained (native i)
    · exact (install_other eraseSlot _ _ _ (erase_avoids i hi)).trans (h.retained i hi)
    · obtain ⟨j,hj⟩ := work_covers i hi
      rw [input_work sign b w bits xs i hi]
      have he := install_slot eraseSlot erase_injective ambient
        (eraseInput D (fun _ => List.replicate D false)) (j.castAdd 2)
      simpa [eraseSlot,eraseInput,CompetitorPlaneWorkspace.eraseInput,Fin.addCases,hj,out,D,show j.val<23 by omega,j.isLt] using he
  · have he := install_slot eraseSlot erase_injective ambient
        (eraseInput D (fun _ => List.replicate D false)) ((0 : Fin 2).natAdd 22)
    simpa [eraseSlot,eraseInput,CompetitorPlaneWorkspace.eraseInput,Fin.addCases,h.driver,out,D] using he
  · have he := install_slot eraseSlot erase_injective ambient
        (eraseInput D (fun _ => List.replicate D false)) ((1 : Fin 2).natAdd 22)
    simpa [eraseSlot,eraseInput,CompetitorPlaneWorkspace.eraseInput,Fin.addCases,h.reset,out,D] using he

theorem reusable_plane_run (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (ambient : Fin 32 → List Bool) (h : Compatible sign b w bits xs ambient)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ out,ClockJoin.ReadyRun machine (budget w xs.length) ambient out ∧
      out 17=ZeroPadding.pad (capacity w xs.length) (newWords sign w bits xs) ∧
      (∀ i,retained (native i) → out (native i)=ambient (native i)) ∧
      (∀ i,(out (native i)).length=capacity w xs.length) ∧
      out 30=ambient 30 ∧ out 31=ambient 31 := by
  obtain ⟨clean,hclear,hclean,h30,h31⟩ := clear_ready sign b w bits xs ambient h
  obtain ⟨produced,child,h17,hkeep,hsupport⟩ := CompetitorPlanePaddedEntry.padded_plane_run sign b w bits xs hb hbits hv
  have h21 := padded_capacity sign b w bits xs hb hbits hv produced child
  have focused := CompetitorRationalProducts.bounded_focus native native_injective _ _ _ child clean hclean
  let out := install native clean produced
  have joined := ClockJoin.join clearProgram callProgram _ _ _ _ _ hclear focused
  refine ⟨out,?_,?_,?_,?_,?_,?_⟩
  · have hcost : (2*capacity w xs.length+4)+1+CompetitorPlaneSign.budget w xs.length=budget w xs.length := by
      unfold budget
      omega
    rw [hcost] at joined
    exact joined
  · exact (install_slot native native_injective _ _ 17).trans h17
  · intro i hi
    have he : produced i=input sign b w bits xs i := by
      fin_cases i <;> simp [retained,native] at hi
      all_goals first | exact h21 | apply hkeep; simp
    exact (install_slot native native_injective _ _ i).trans (he.trans (h.retained i hi).symm)
  · intro i
    change (install native clean produced (native i)).length=capacity w xs.length
    rw [install_slot native native_injective _ _ i]
    exact hsupport i
  · exact (install_other native _ _ 30 (fun i => (native_other i).1)).trans h30
  · exact (install_other native _ _ 31 (fun i => (native_other i).2)).trans h31

end NearCubicWires.RepairOrdinary.CompetitorPlaneReusable
