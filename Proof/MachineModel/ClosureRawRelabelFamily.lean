import Proof.MachineModel.ClosureRawRelabelUniform
import Proof.Amplification.RecoveryEraseWidth
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsFamilyLoop

/-! A.12's complete raw-index family, constructed from the retained lowered
stream by a fixed physical loop. Each iteration calls the checked relabeler
and increments its actual unary assignment index. No row callback is assumed.
The repeat driver and input-derived capacities are explicit retained inputs. -/
namespace NearCubicWires.P1Closure.RawRelabelFamily
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch RecoveryRootRound
open ExtIncidence RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def incSlots : Fin 1→Fin 8:=fun _=>2
noncomputable def inc:=RecoveryFocus.machine incSlots RecoveryEraseWidth.incrementMachine

def move (up : Bool) : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=2 then (if up then .right else .left) else .stay⟩ else none

def heads (out : List Bool) (counter : ℕ) : Fin 8→ℕ:=![0,0,counter,0,out.length,0,0,0]
noncomputable def increment:=Composition.machine (Composition.machine (move true) inc) (move false)
noncomputable def body:=Composition.machine RawRelabelRun.machine increment
noncomputable def machine:=CloseoutRowsDegreeLoop.machine body

def bodyBudget (N Y S : ℕ):=RawRelabelUniform.budget N Y S+2*Y+7
def budget (N Y S : ℕ):=Y*(bodyBudget N Y S+3)+3

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

theorem inc_run (N j R L : ℕ) (source out : List Bool) :
    Step inc (2*j+2) (heads out 1) (RawRelabelRun.input N j R L source out)
      (heads out 1) (RawRelabelRun.input N (j+1) R L source out) := by
  obtain ⟨r,hr,hf,_⟩:=RecoveryEraseWidth.increment_run j
  have localRun:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have h:=localRun.dock incSlots (by decide) (heads out 1) (RawRelabelRun.input N j R L source out)
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
  refine h.congr (dockH_existing _ _ _ (by intro i;fin_cases i;rfl)) ?_
  apply HierarchyAllocation.install_eq incSlots (by decide)
  · intro i;fin_cases i;rfl
  · intro i hi
    fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)

theorem increment_run (N j R L : ℕ) (source out : List Bool) :
    Step increment (2*j+6) (RawRelabelRun.heads out 0) (RawRelabelRun.input N j R L source out)
      (RawRelabelRun.heads out 0) (RawRelabelRun.input N (j+1) R L source out) := by
  have first:=move_run true out (RawRelabelRun.input N j R L source out)
  have middle:=inc_run N j R L source out
  have last:=move_run false out (RawRelabelRun.input N (j+1) R L source out)
  have h:=(first.seq middle).seq last
  have eq:heads out 0=RawRelabelRun.heads out 0:=by funext i;fin_cases i <;> rfl
  simpa [increment,eq,show 1+1+(2*j+2)+1+1=2*j+6 by omega] using h

def emit (N : ℕ) (P : List (List ℕ)) (j : ℕ):=stream (P.map (List.map (fun c=>N*j+c+1)))
noncomputable def entry (N Y S : ℕ) (P : List (List ℕ)) (tail : List Bool) (j : ℕ) (out : List Bool) :=
  (⟨body.start,RawRelabelRun.heads out 0,
    RawRelabelRun.input N j (RawRelabelUniform.capacity N Y) (RawRelabelUniform.logCapacity N Y S)
      (stream P++tail) out⟩ : Configuration 8 _)

theorem body_run (N Y S j : ℕ) (P : List (List ℕ)) (tail out : List Bool)
    (hj : j≤Y) (hS : (stream P).length≤S) :
    Step body (bodyBudget N Y S) (entry N Y S P tail j out).heads (entry N Y S P tail j out).tapes
      (entry N Y S P tail (j+1) (out++emit N P j)).heads
      (entry N Y S P tail (j+1) (out++emit N P j)).tapes := by
  have first:=RawRelabelUniform.run N j Y S P tail out hj hS
  have last:=increment_run N j (RawRelabelUniform.capacity N Y) (RawRelabelUniform.logCapacity N Y S)
    (stream P++tail) (out++emit N P j)
  exact (first.seq last).enlarge (by unfold bodyBudget;omega)

def familyHeads (out : List Bool) : Fin 9→ℕ:=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>ℕ) (RawRelabelRun.heads out 0) (fun _=>1)
def familyData (N Y S j : ℕ) (P : List (List ℕ)) (tail out : List Bool) : Fin 9→List Bool:=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (RawRelabelRun.input N j (RawRelabelUniform.capacity N Y) (RawRelabelUniform.logCapacity N Y S)
      (stream P++tail) out) (fun _=>CompareMachine.word Y)

theorem run (N Y S : ℕ) (P : List (List ℕ)) (tail out : List Bool)
    (hS : (stream P).length≤S) :
    let result:=out++(List.range Y).flatMap (emit N P)
    Step machine (budget N Y S) (familyHeads out) (familyData N Y S 0 P tail out)
      (familyHeads result) (familyData N Y S Y P tail result) := by
  dsimp only
  obtain ⟨r,hr,hf,_⟩:=CloseoutRowsDegreeLoop.loop_run body (entry N Y S P tail) (emit N P)
    (bodyBudget N Y S) Y (by intros;rfl)
    (by intro j hj acc;exact body_run N Y S j P tail acc hj.le hS) out
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

open CanonicalFourfoldRowProgram RepairRepresentation SupplierPipeline
open RepairSource.CloseoutFinal

theorem actual_word {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : ℕ) (harity : (s+1)/2+s/2=liveᶜ.card)
    (P : StructuralGF2Polynomial) :
    (List.range (2^live.card)).flatMap
      (emit (C10SupplierRowInput.childList a live occ).length (RepairSource.CloseoutRowsUniversal.lower a live occ P))=
      (C10SupplierRowInput.ps a live occ s harity P).flatMap NativeFamily.rawWord := by
  let ps:=C10SupplierRowInput.ps a live occ s harity P
  have len:ps.length=2^live.card:=by
    simp only [ps,C10SupplierRowInput.ps,List.length_ofFn,C10SupplierRowInput.liveList_length]
  rw [←len,←CloseoutRowsFamilyLoop.flatMap_index ps [] NativeFamily.rawWord]
  change (List.map _ (List.range ps.length)).flatten=(List.map _ (List.range ps.length)).flatten
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj':j<ps.length:=List.mem_range.mp hj
  let yi : Fin (C10SupplierRowInput.liveList live).length:=
    ⟨j,by simpa only [ps,C10SupplierRowInput.ps,List.length_ofFn] using hj'⟩
  have word:=RawRelabelShape.raw_index_row a live occ s harity P yi
  rw [List.getD_eq_getElem ps [] hj']
  have get:ps[j]=C10SupplierRowInput.indexRow a live occ s harity P yi:=by
    simp [ps,C10SupplierRowInput.ps,yi]
  rw [get,word]
  rfl

theorem actual_run {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : ℕ) (harity : (s+1)/2+s/2=liveᶜ.card)
    (P : StructuralGF2Polynomial) (S : ℕ) (tail out : List Bool)
    (hS : (stream (RepairSource.CloseoutRowsUniversal.lower a live occ P)).length≤S) :
    let N:=(C10SupplierRowInput.childList a live occ).length
    let lower:=RepairSource.CloseoutRowsUniversal.lower a live occ P
    let result:=out++(C10SupplierRowInput.ps a live occ s harity P).flatMap NativeFamily.rawWord
    Step machine (budget N (2^live.card) S) (familyHeads out) (familyData N (2^live.card) S 0 lower tail out)
      (familyHeads result) (familyData N (2^live.card) S (2^live.card) lower tail result) := by
  dsimp only
  have h:=run (C10SupplierRowInput.childList a live occ).length (2^live.card) S
    (RepairSource.CloseoutRowsUniversal.lower a live occ P) tail out hS
  rw [actual_word a live occ s harity P] at h
  exact h

end
end NearCubicWires.P1Closure.RawRelabelFamily
