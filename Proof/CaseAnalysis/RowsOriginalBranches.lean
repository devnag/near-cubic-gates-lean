import Proof.CaseAnalysis.RowsOriginalProducerBounds
import Proof.CaseAnalysis.RowsOriginalTemplateSlots
import Proof.CaseAnalysis.RowsOriginalSwitch

/-! Native sign and auxiliary flags select the exact fixed paper template.
All branches execute the same original-term product and metadata pipeline. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBranches
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsOriginalTemplates CloseoutRowsRawAtomSeek
open CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem valid (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (hi : ∀ side,indices side<cs.length) (r : Row) :
    Valid cs (r.factors.map indices) := by
  intro j hj;obtain ⟨side,_,rfl⟩:=List.mem_map.mp hj;exact hi side

def flags (C : ℕ) (bits : Fin 4→Bool) (j : Fin 4):=ZeroPadding.pad C [bits j]
def input (C : ℕ) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (bits : Fin 4→Bool) : Fin 22→List Bool:=
  Fin.addCases (m:=18) (n:=4) (motive:=fun _=>List Bool)
    (CloseoutRowsOriginalProducer.data C indices [] (cacheWord cs) [] (CloseoutRowsOriginalMetadata.data C [] [] [])) (flags C bits)
def outHeads (r : Row) (indices : Fin 2→ℕ) : Fin 22→ℕ:=
  Fin.addCases (m:=18) (n:=4) (motive:=fun _=>ℕ)
    (CloseoutRowsOriginalProducer.heads ((r.factors.map indices).flatMap ExtIncidence.block).length 17 1) (fun _=>0)
def output (r : Row) (C : ℕ) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ)
    (hi : ∀ side,indices side<cs.length) (bits : Fin 4→Bool) : Fin 22→List Bool:=
  Fin.addCases (m:=18) (n:=4) (motive:=fun _=>List Bool)
    (CloseoutRowsOriginalProducer.data C indices (CloseoutRowsOriginalWriter.indicesWord indices r.factors) (cacheWord cs)
      (ExtIncidence.stream (value cs (r.factors.map indices) (valid cs indices hi r) [[]]))
      (CloseoutRowsOriginalMetadata.data C (CloseoutRowsOriginalMetadata.rho r)
        (CloseoutRowsOriginalMetadata.count r) (CloseoutRowsOriginalMetadata.parity r))) (flags C bits)
noncomputable def body (r : Row):=TapeEmbedding.machine 4 (CloseoutRowsOriginalProducer.machine r)
def cost (cs : List (List (List ℕ))) (B W : ℕ):=48*rowC cs B W+16*cs.length+203
noncomputable def penalty (side : Fin 2) (j : Fin 3):=CloseoutRowsOriginalSwitch.machine
  (body (penaltySlot true side j)) (body (penaltySlot false side j)) (Fin.natAdd 18 (Fin.natAdd 2 side))
noncomputable def signedRight (a : Bool) (j : Fin 3):=CloseoutRowsOriginalSwitch.machine
  (body (clauseSlot a true j)) (body (clauseSlot a false j)) 19
noncomputable def clause (j : Fin 3):=CloseoutRowsOriginalSwitch.machine (signedRight true j) (signedRight false j) 18

theorem body_run (r : Row) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (bits : Fin 4→Bool)
    (B W : ℕ) (hB : 1≤B) (count : ∀ p∈cs,p.length≤B) (width : ∀ p∈cs,(ExtIncidence.stream p).length≤W)
    (hi : ∀ side,indices side<cs.length) (hl : r.factors.length≤4) :
    Step (body r) (cost cs B W) (fun _=>0) (input (rowC cs B W) cs indices bits)
      (outHeads r indices) (output r (rowC cs B W) cs indices hi bits) := by
  have raw:=CloseoutRowsOriginalProducer.bounded_run r cs indices B W hB count width (valid cs indices hi r) hi hl
  have lifted:=raw.embed (fun _ : Fin 4=>0) (flags (rowC cs B W) bits)
  exact lifted.congr_in (by funext j;fin_cases j <;>rfl) rfl

theorem flag_read (C : ℕ) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (bits : Fin 4→Bool) (j : Fin 4) :
    readTapeBit (input C cs indices bits (Fin.natAdd 18 j)) 0=bits j := by
  rw [input,Fin.addCases_right,flags,ZeroPadding.read_pad];rfl

theorem penalty_run (side : Fin 2) (j : Fin 3) (aux : Bool)
    (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (bits : Fin 4→Bool)
    (B W : ℕ) (hB : 1≤B) (count : ∀ p∈cs,p.length≤B) (width : ∀ p∈cs,(ExtIncidence.stream p).length≤W)
    (hi : ∀ s,indices s<cs.length) (hb : bits (Fin.natAdd 2 side)=aux) :
    Step (penalty side j) (cost cs B W+2) (fun _=>0) (input (rowC cs B W) cs indices bits)
      (outHeads (penaltySlot aux side j) indices) (output (penaltySlot aux side j) (rowC cs B W) cs indices hi bits) := by
  have scan : readTapeBit (input (rowC cs B W) cs indices bits (Fin.natAdd 18 (Fin.natAdd 2 side))) 0=aux :=
    (flag_read _ _ _ _ (Fin.natAdd 2 side)).trans hb
  have raw:=body_run (penaltySlot aux side j) cs indices bits B W hB count width hi (penalty_slot_legal aux side j).1
  cases aux
  · exact CloseoutRowsOriginalSwitch.false_run _ _ _ raw scan
  · exact CloseoutRowsOriginalSwitch.true_run _ _ _ raw scan

theorem clause_run (j : Fin 3) (a b : Bool)
    (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (bits : Fin 4→Bool)
    (B W : ℕ) (hB : 1≤B) (count : ∀ p∈cs,p.length≤B) (width : ∀ p∈cs,(ExtIncidence.stream p).length≤W)
    (hi : ∀ s,indices s<cs.length) (ha : bits 0=a) (hb : bits 1=b) :
    Step (clause j) (cost cs B W+4) (fun _=>0) (input (rowC cs B W) cs indices bits)
      (outHeads (clauseSlot a b j) indices) (output (clauseSlot a b j) (rowC cs B W) cs indices hi bits) := by
  have scanA : readTapeBit (input (rowC cs B W) cs indices bits 18) 0=a:=(flag_read _ _ _ _ 0).trans ha
  have scanB : readTapeBit (input (rowC cs B W) cs indices bits 19) 0=b:=(flag_read _ _ _ _ 1).trans hb
  have raw:=body_run (clauseSlot a b j) cs indices bits B W hB count width hi (clause_slot_legal a b j).1
  have middle : Step (signedRight a j) (cost cs B W+2) (fun _=>0) (input (rowC cs B W) cs indices bits)
      (outHeads (clauseSlot a b j) indices) (output (clauseSlot a b j) (rowC cs B W) cs indices hi bits) := by
    cases b
    · exact CloseoutRowsOriginalSwitch.false_run _ _ _ raw scanB
    · exact CloseoutRowsOriginalSwitch.true_run _ _ _ raw scanB
  have time : cost cs B W+2+2=cost cs B W+4:=by omega
  cases a
  · simpa only [clause,time] using CloseoutRowsOriginalSwitch.false_run (signedRight true j) (signedRight false j) 18 middle scanA
  · simpa only [clause,time] using CloseoutRowsOriginalSwitch.true_run (signedRight true j) (signedRight false j) 18 middle scanA

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBranches
