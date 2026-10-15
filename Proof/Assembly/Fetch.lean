import Proof.CaseAnalysis.RowsTupleSeek
import Proof.CaseAnalysis.RowsTupleSeekTyped
import Proof.Assembly.LoaderRecipe
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource.VerifierDecoding RecoveryRootRound
namespace IndexFetchProgram
open CloseoutRowsTupleSeek

/-- Actual finite program chosen for the enclosing loader. Four unary indices,
count, append output. States0–11 process indices;12 returns the count head;
13 enters that return after four factors;14 halts. -/
def indexMachine : Machine 6 15 where
 descriptionBits := 0
 start := 0
 halted := fun st => st.val == 14
 rule := fun st scan =>
  if h : st.val < 12 then
   let slot : Fin 6 := ⟨st.val/3,by omega⟩
   if st.val % 3 = 0 then
    some (if scan 4 then
     ⟨⟨st.val+1,by omega⟩,fun i=>if i=5 then some true else none,
       fun i=>if i=5 then .right else .stay⟩
    else ⟨12,fun _=>none,fun i=>if i=4 then .left else .stay⟩)
   else if st.val % 3 = 1 then
    some (if scan slot then
     ⟨st,fun i=>if i=5 then some true else none,
       fun i=>if i=slot ∨ i=5 then .right else .stay⟩
    else
     ⟨⟨st.val+1,by omega⟩,fun i=>if i=5 then some false else none,
       fun i=>if i=slot then .left else if i=5 then .right else .stay⟩)
   else
    some (if scan slot then
     ⟨st,fun _=>none,fun i=>if i=slot then .left else .stay⟩
    else
     ⟨(if st.val=11 then 13 else ⟨st.val+1,by omega⟩),fun _=>none,
       fun i=>if i=slot ∨ i=4 then .right else .stay⟩)
  else if st.val=12 then
   some (if scan 4 then
    ⟨12,fun _=>none,fun i=>if i=4 then .left else .stay⟩
   else ⟨14,fun _=>none,fun i=>if i=4 then .right else .stay⟩)
  else if st.val=13 then
   some ⟨12,fun _=>none,fun i=>if i=4 then .left else .stay⟩
  else none

def indexSlots : Fin 6 → Fin 31 := ![27,28,29,30,26,25]
def rewindSlots : Fin 3 → Fin 31 := ![25,21,22]
noncomputable def machine := Composition.machine
 (RecoveryFocus.machine indexSlots indexMachine)
 (Composition.machine (RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine)
   (TapeEmbedding.machine 4 coldMachine))

def digits {n : Nat} (js : List (Fin n)) (i : Fin 4) : Nat :=
 (js.map Fin.val).getD i.val 0
def ordinalWords {n : Nat} (js : List (Fin n)) : Fin 4 → List Bool :=
 fun i=>CompareMachine.word (digits js i)
def indexCost {n : Nat} (js : List (Fin n)) := 2*(js.map Fin.val).sum+4*js.length+2
def cost (ts : List TermSlices) (js : List (Fin ts.length)) (C D : Nat) :=
 indexCost js+1+(2*C+2+1+(6*D+9+tupleBudget C D ts.length 4))
def entryH (pos : Fin 3 → Nat) : Fin 31 → Nat :=
 Fin.addCases (m:=27) (n:=4) (motive:=fun _=>Nat) (tupleHeads pos (fun _=>[]) 0) (fun _ : Fin 4=>1)
def entryT (ts : List TermSlices) (js : List (Fin ts.length)) (C D : Nat) : Fin 31 → List Bool :=
 Fin.addCases (m:=27) (n:=4) (motive:=fun _=>List Bool) (tupleData C D (familyWords ts) (fun _=>[]) [] js.length) (ordinalWords js)
def exitH (ts : List TermSlices) (js : List (Fin ts.length)) : Fin 31 → Nat :=
 Fin.addCases (m:=27) (n:=4) (motive:=fun _=>Nat) (tupleHeads (fun _=>0) (tupleOutput ts js (fun _=>[])) (tupleWord js).length)
  (fun _ : Fin 4=>1)
def exitT (ts : List TermSlices) (js : List (Fin ts.length)) (C D : Nat) : Fin 31 → List Bool :=
 Fin.addCases (m:=27) (n:=4) (motive:=fun _=>List Bool) (tupleData C D (familyWords ts) (tupleOutput ts js (fun _=>[])) (tupleWord js) js.length)
  (ordinalWords js)

/-- Substantial concrete helper: real index production, rewind and cold fetch.
Every source, unary ordinal and driver remains an actual required input. -/
noncomputable abbrev Correct : Prop :=
 ∀ (ts : List TermSlices) (js : List (Fin ts.length)) (C D : Nat),
 (∀ t∈ts,t.cost+1≤C) → (∀ i,(familyWords ts i).length≤D) →
 js.length≤4 → (tupleWord js).length≤C →
 ∀ pos : Fin 3 → Nat, (∀ i,pos i≤D) →
 Step machine (cost ts js C D) (entryH pos) (entryT ts js C D)
  (exitH ts js) (exitT ts js C D)

open RepairRepresentation SourceInterfaces RepairSource.CloseoutFinal CanonicalWitnessCodec
open SupplierPipeline CloseoutWitness CloseoutRowsCircuitCanonicalFields
/-- Native/support/count bytes of the actual semantic factor. Coefficient bytes
are deliberately excluded from the matching condition below. -/
noncomputable def atomWords {q : Nat} {circuit : BooleanCircuit q}
 {pcpp : PointwisePCPP circuit} (mode : Bool) (atom : C10TotalDecode.Atom pcpp) : Fin 4 → List Bool :=
 if mode then
  let c := C10NaturalModeAtoms.nativeSymmetricAtom atom
  (typedSlices (List.ofFn c.top) (List.ofFn c.bottom) 0 (0 : Rat)).words
 else
  let c := C10NaturalModeAtoms.nativeThresholdAtom atom
  (typedSlices (CloseoutRowsCircuitThresholdRun.top c.top)
   (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))) 0 (0 : Rat)).words
end IndexFetchProgram
