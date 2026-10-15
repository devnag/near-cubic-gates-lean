import Proof.PCP.PCPPNativeNodeCalls

/-! The concrete entry of one native-node substitution. Live source/cache,
actual base/position/capacity counters and output are separated from parser
scratch and from the already reusable scalar-field workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initialData (source queries : List Bool) (base position C : ℕ) (out : List Bool) (i : Fin 119) : List Bool :=
  if i=0 then source else if i=1 then queries else if i=2 then List.replicate base true
  else if i=3 then List.replicate position true else if i=4 then List.replicate C true
  else if i=5 then out else if i=12 then List.replicate (C+1) false
  else if 100 ≤ i.val then List.replicate C false else []
def initialHeads (pos : ℕ) (out : List Bool) (i : Fin 119) : ℕ :=
  if i=0 then pos else if i=5 then out.length else 0
noncomputable def entry (source queries : List Bool) (pos base position C : ℕ) (out : List Bool) :=
  boundary 0 (initialHeads pos out) (initialData source queries base position C out)

theorem read_input (source queries : List Bool) (pos base position C : ℕ) (out : List Bool) (i : Fin 31) :
    initialHeads pos out (readSlots i)=(PCPPNativeNodeClassify.entry source pos).heads i ∧
      initialData source queries base position C out (readSlots i)=(PCPPNativeNodeClassify.entry source pos).tapes i := by
  fin_cases i <;> simp [initialHeads,initialData,readSlots,PCPPNativeNodeClassify.entry,
    PCPPNativeNodeRead.entry,Composition.leftConfig]

theorem reader_run (pre tail queries : List Bool) (tag : Fin 5) (a b base position C : ℕ) (out : List Bool) :
    ∃ r,runFrom (programs 0) (PCPPNativeNodeClassify.budget tag a b)
      (RecoveryCalls.restarted (programs 0) (initialHeads pre.length out)
        (initialData (PCPPNativeNodeRead.source pre tail tag.val a b) queries base position C out))=some r ∧
      r.steps ≤ PCPPNativeNodeClassify.budget tag a b ∧
      r.final.control.val=PCPPNativeNodeClassify.readerStates+(tag.val+5) ∧
      r.final.tapes 0=PCPPNativeNodeRead.source pre tail tag.val a b ∧
      r.final.heads 0=pre.length+(natWord tag.val).length+(natWord a).length+(natWord b).length ∧
      r.final.tapes 6=UnaryTemplate.tape tag.val ∧ r.final.heads 6=tag.val+1 ∧
      r.final.tapes 7=UnaryTemplate.tape a ∧ r.final.heads 7=1 ∧
      r.final.tapes 8=UnaryTemplate.tape b ∧ r.final.heads 8=1 ∧
      (∀ i,(∀ j,readSlots j≠i) →
        r.final.heads i=initialHeads pre.length out i ∧
        r.final.tapes i=initialData (PCPPNativeNodeRead.source pre tail tag.val a b) queries base position C out i) := by
  obtain ⟨raw,hr,rs,rc,r0,rh0,r6,rh6,r7,rh7,r8,rh8⟩ := PCPPNativeNodeClassify.classify_run pre tail tag a b
  obtain ⟨r,hrun,hctrl,steps,hh,ht,keep⟩ := RecoveryFocus.dock readSlots read_injective
    PCPPNativeNodeClassify.machine _ (initialHeads pre.length out)
    (initialData (PCPPNativeNodeRead.source pre tail tag.val a b) queries base position C out)
    (PCPPNativeNodeClassify.entry (PCPPNativeNodeRead.source pre tail tag.val a b) pre.length)
    (fun i => (read_input _ queries pre.length base position C out i).1)
    (fun i => (read_input _ queries pre.length base position C out i).2) raw hr
  refine ⟨r,hrun,by omega,?_,(ht 0).trans r0,(hh 0).trans rh0,
    (ht 10).trans r6,(hh 10).trans rh6,(ht 20).trans r7,(hh 20).trans rh7,
    (ht 30).trans r8,(hh 30).trans rh8,keep⟩
  rw [hctrl]
  exact rc

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
