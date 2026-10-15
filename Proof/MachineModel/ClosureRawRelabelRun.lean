import Proof.MachineModel.ClosureRawRelabelOffset
import Proof.MachineModel.ClosureRawRelabelShape
import Proof.MachineModel.Layout
import Proof.Amplification.RecoveryScratchErase

/-! Reusable physical C10 raw-row construction from the actual lowered stream.
Runtime N and yi are retained unary counters. Offset scratch starts and ends
all zero; source and every control head return to zero. The output append is
the only changing state, and the exact indexRow consumer is proved below. -/
namespace NearCubicWires.P1Closure.RawRelabelRun
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch RecoveryRootRound
open ExtIncidence
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

def heads (out : List Bool) (cursor : ℕ) : Fin 8→ℕ := ![0,0,0,cursor,out.length,0,0,0]
def data (N yi R L : ℕ) (source offset out : List Bool) : Fin 8→List Bool :=
  ![source,List.replicate N true,false::List.replicate yi true,offset,out,List.replicate L false,
    List.replicate R true,List.replicate (R+1) false]
def input (N yi R L : ℕ) (source out : List Bool) := data N yi R L source (List.replicate R false) out
def shifted (N yi R : ℕ) := ZeroPadding.pad R (false::List.replicate (N*yi+1) true)
def offsetSlots : Fin 4→Fin 8 := ![1,2,3,5]
def scanSlots : Fin 4→Fin 8 := ![0,3,4,5]
def eraseSlots : Fin 3→Fin 8 := ![3,6,7]
noncomputable def offsetMachine:=RecoveryFocus.machine offsetSlots RawRelabelOffset.machine
noncomputable def scanMachine:=RecoveryFocus.machine scanSlots
  (MaskedReset.machine RawRelabelMachine.machine (fun i=>decide (i=0)))
noncomputable def eraseMachine:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def move (up : Bool) : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=3 then (if up then .right else .left) else .stay⟩ else none
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine offsetMachine (move true)) scanMachine) (move false))
  eraseMachine
def budget (N yi R : ℕ) (P : List (List ℕ)):=
  RawRelabelOffset.budget N yi+2*RawRelabelMachine.budget (N*yi+1) P+2*R+12

theorem move_run (up : Bool) (out : List Bool) (A : Fin 8→List Bool) :
    Step (move up) 1 (heads out (if up then 0 else 1)) A
      (heads out (if up then 1 else 0)) A := by
  have h:step (move up) (⟨(move up).start,heads out (if up then 0 else 1),A⟩ : Configuration 8 2)=
      some ⟨1,heads out (if up then 1 else 0),A⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> cases up <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) h).run rfl
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem offset_run (N yi R L : ℕ) (source out : List Bool)
    (hL : RawRelabelOffset.rawBudget N yi≤L) :
    Step offsetMachine (RawRelabelOffset.budget N yi) (heads out 0) (input N yi R L source out)
      (heads out 0) (data N yi R L source (shifted N yi R) out) := by
  have localRun:=(RawRelabelOffset.run N yi L hL).pad (![0,0,R,0] : Fin 4→ℕ)
  have h:=localRun.dock offsetSlots (by decide) (heads out 0) (input N yi R L source out)
    (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j <;> simp [offsetSlots,input,data,RawRelabelOffset.input,ZeroPadding.pad])
  refine h.congr ?_ ?_
  · exact dockH_existing _ _ _ (by intro j;fin_cases j <;> rfl)
  · apply HierarchyAllocation.install_eq offsetSlots (by decide)
    · intro j;fin_cases j <;> simp [offsetSlots,data,shifted,RawRelabelOffset.output,ZeroPadding.pad_zero]
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact False.elim (hi 0 rfl)
        | exact False.elim (hi 1 rfl)
        | exact False.elim (hi 2 rfl)

theorem scan_run (N yi R L : ℕ) (P : List (List ℕ)) (tail out : List Bool)
    (hL : RawRelabelMachine.budget (N*yi+1) P≤L) :
    let result:=out++stream (P.map (List.map ((N*yi+1)+·)))
    Step scanMachine (2*RawRelabelMachine.budget (N*yi+1) P+2)
      (heads out 1) (data N yi R L (stream P++tail) (shifted N yi R) out)
      (heads result 1) (data N yi R L (stream P++tail) (shifted N yi R) result) := by
  dsimp only
  obtain ⟨r,hr,hf,_⟩:=(RawRelabelMachine.stream_run P [] tail out (N*yi+1)).run (by rfl)
  have base:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have padded:=base.pad (![0,R,0] : Fin 3→ℕ)
  have reset:=padded.mask (fun i=>decide (i=0)) (by intro i hi;have e:i=0:=of_decide_eq_true hi;subst i;rfl) hL
  have h:=reset.dock scanSlots (by decide) (heads out 1)
    (data N yi R L (stream P++tail) (shifted N yi R) out)
    (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j <;> simp [scanSlots,data,shifted,Fin.addCases])
  refine h.congr ?_ ?_
  · funext i
    fin_cases i <;> first
      | exact dockH_slot scanSlots (by decide) _ _ 0
      | exact dockH_slot scanSlots (by decide) _ _ 1
      | exact dockH_slot scanSlots (by decide) _ _ 2
      | exact dockH_slot scanSlots (by decide) _ _ 3
      | exact dockH_other scanSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq scanSlots (by decide)
    · intro j;fin_cases j <;> simp [scanSlots,data,shifted,RawRelabelMachine.cfg,Fin.addCases]
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact False.elim (hi 0 rfl)
        | exact False.elim (hi 1 rfl)
        | exact False.elim (hi 2 rfl)

theorem erase_run (N yi R L : ℕ) (source out : List Bool) (hR : N*yi+2≤R) :
    Step eraseMachine (2*R+4) (heads out 0) (data N yi R L source (shifted N yi R) out)
      (heads out 0) (input N yi R L source out) := by
  have len:(shifted N yi R).length≤R:=by
    simp only [shifted,ZeroPadding.pad,List.length_append,List.length_cons,List.length_replicate]
    omega
  have localRun:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+1)
    (fun _ : Fin 1=>shifted N yi R) (fun _=>len))
  have h:=localRun.dock eraseSlots (by decide) (heads out 0) (data N yi R L source (shifted N yi R) out)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  refine h.congr ?_ ?_
  · exact dockH_existing _ _ _ (by intro j;fin_cases j <;> rfl)
  · apply HierarchyAllocation.install_eq eraseSlots (by decide)
    · intro j;fin_cases j <;> simp [eraseSlots,input,data,Fin.addCases]
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact False.elim (hi 0 rfl)

theorem run (N yi R L : ℕ) (P : List (List ℕ)) (tail out : List Bool)
    (hR : N*yi+2≤R) (hOffset : RawRelabelOffset.rawBudget N yi≤L)
    (hScan : RawRelabelMachine.budget (N*yi+1) P≤L) :
    let result:=out++stream (P.map (List.map (fun c=>N*yi+c+1)))
    Step machine (budget N yi R P) (heads out 0) (input N yi R L (stream P++tail) out)
      (heads result 0) (input N yi R L (stream P++tail) result) := by
  dsimp only
  have first:=offset_run N yi R L (stream P++tail) out hOffset
  have second:=move_run true out (data N yi R L (stream P++tail) (shifted N yi R) out)
  have third:=scan_run N yi R L P tail out hScan
  have fourth:=move_run false (out++stream (P.map (List.map ((N*yi+1)+·))))
    (data N yi R L (stream P++tail) (shifted N yi R) (out++stream (P.map (List.map ((N*yi+1)+·)))))
  have last:=erase_run N yi R L (stream P++tail) (out++stream (P.map (List.map ((N*yi+1)+·)))) hR
  have joined:=(((first.seq second).seq third).seq fourth).seq last
  have cost:RawRelabelOffset.budget N yi+1+1+1+(2*RawRelabelMachine.budget (N*yi+1) P+2)+1+1+1+(2*R+4)=
      budget N yi R P:=by unfold budget;omega
  have index:(fun c=>(N*yi+1)+c)=(fun c=>N*yi+c+1):=by funext c;omega
  simpa only [machine,cost,index] using joined

open CanonicalFourfoldRowProgram RepairRepresentation SupplierPipeline
open RepairSource.CloseoutFinal

theorem actual_run {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : ℕ) (harity : (s+1)/2+s/2=liveᶜ.card)
    (P : StructuralGF2Polynomial) (yi : Fin (C10SupplierRowInput.ps a live occ s harity P).length)
    (R L : ℕ) (tail out : List Bool)
    (hR : (C10SupplierRowInput.childList a live occ).length*yi.val+2≤R)
    (hOffset : RawRelabelOffset.rawBudget (C10SupplierRowInput.childList a live occ).length yi.val≤L)
    (hScan : RawRelabelMachine.budget ((C10SupplierRowInput.childList a live occ).length*yi.val+1)
      (RepairSource.CloseoutRowsUniversal.lower a live occ P)≤L) :
    let N:=(C10SupplierRowInput.childList a live occ).length
    let source:=stream (RepairSource.CloseoutRowsUniversal.lower a live occ P)++tail
    let result:=out++NativeFamily.rawWord ((C10SupplierRowInput.ps a live occ s harity P).get yi)
    Step machine (budget N yi.val R (RepairSource.CloseoutRowsUniversal.lower a live occ P))
      (heads out 0) (input N yi.val R L source out)
      (heads result 0) (input N yi.val R L source result) := by
  dsimp only
  let j : Fin (C10SupplierRowInput.liveList live).length:=
    ⟨yi.val,by simpa only [C10SupplierRowInput.ps,List.length_ofFn] using yi.isLt⟩
  have word:=RawRelabelShape.raw_index_row a live occ s harity P j
  have get:(C10SupplierRowInput.ps a live occ s harity P).get yi=
      C10SupplierRowInput.indexRow a live occ s harity P j:=by
    simp [C10SupplierRowInput.ps,j]
  rw [get,word]
  exact run _ yi.val R L (RepairSource.CloseoutRowsUniversal.lower a live occ P) tail out hR hOffset hScan

end
end NearCubicWires.P1Closure.RawRelabelRun
