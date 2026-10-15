import Proof.SourceAssembly.Compatible
import Proof.SourceAssembly.PoolDonorCompatible

/- The actual paired-pool writer followed immediately by Cold decomposition.
The shared source port aliases the append output. This omits the unused
atom-cache conversion and retains the exact child-count stream for packet input.
All input templates/reserves remain explicit; the caller must produce them. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PoolColdSource.PoolCold
open NearCubicWires LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairSource SupplierPipeline RepairRepresentation VerifierDecoding P1Closure
open scoped BigOperators
attribute [local irreducible] PoolEntryOccurrence.machine Cold.machine

abbrev sourcePort (a : DecompositionAlgorithm) := Cold.port a (str a)
def slots (a : DecompositionAlgorithm) (i : Fin (Cold.tapes a)) :
    Fin (132+Cold.tapes a) :=
  if i=sourcePort a then (61 : Fin 132).castAdd _ else i.natAdd 132

theorem slots_injective (a : DecompositionAlgorithm) : Function.Injective (slots a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv with hi hj hj
  · exact hi.trans hj.symm
  · simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
  · simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
  · apply Fin.ext
    simp only [Fin.val_natAdd] at hv
    omega

noncomputable def machine (a : DecompositionAlgorithm) := Composition.machine
  (TapeEmbedding.machine (Cold.tapes a) PoolEntryLoop.machine)
  (RecoveryFocus.machine (slots a) (Cold.machine a))

noncomputable def start {q : Nat} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w : Nat) (top : List Bool) :=
  RepeatMachine.cfg 0
    (PoolEntryLoop.cfg live occ B w 0 (natWord (2*occ.length)++RepairOrdinary.frame top)) occ.length 1

noncomputable def finish {q : Nat} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w : Nat) (top : List Bool) :=
  RepeatMachine.cfg 3
    (PoolEntryLoop.cfg live occ B w occ.length (segment (CloseoutRowsUniversal.pool live occ) top))
    occ.length 1

def coldHeads (a : DecompositionAlgorithm) := Cold.heads a 0
def coldData (a : DecompositionAlgorithm) (P q : Nat) := Cold.data a P q []

theorem source_heads (a : DecompositionAlgorithm) (pos : Nat) :
    Cold.heads a pos (sourcePort a)=pos := by
  simp [Cold.heads,sourcePort,Cold.port,
    Cold.old,Cold.port,Cold.old,Cold.heads,str,live,ex]

theorem source_data (a : DecompositionAlgorithm) (P q : Nat) (word : List Bool) :
    Cold.data a P q word (sourcePort a)=word := by
  simp [Cold.data,sourcePort,Cold.port,
    Cold.old,Cold.port,Cold.old,Cold.data,str,live,ex]

theorem sourcePort_val (a : DecompositionAlgorithm) : (sourcePort a).val=SB a := by
  simp [sourcePort,Cold.port,Cold.old,str,live,ex]

theorem cold_heads_other (a : DecompositionAlgorithm) (pos : Nat)
    (i : Fin (Cold.tapes a)) (hi : i≠sourcePort a) :
    coldHeads a i=Cold.heads a pos i := by
  have hn : i.val≠SB a := by
    intro h
    apply hi
    exact Fin.ext (h.trans (sourcePort_val a).symm)
  simp only [coldHeads,Cold.heads,if_neg hn]

theorem cold_data_other (a : DecompositionAlgorithm) (P q : Nat) (word : List Bool)
    (i : Fin (Cold.tapes a)) (hi : i≠sourcePort a) :
    coldData a P q i=Cold.data a P q word i := by
  have hn : i.val≠SB a := by
    intro h
    apply hi
    exact Fin.ext (h.trans (sourcePort_val a).symm)
  simp only [coldData,Cold.data,if_neg hn]

theorem run {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ H O, Step (machine a)
      (PoolEntryLoop.budget occ.length B q w+1+
        Cold.runtimeCoefficient a*(P+2)^Cold.runtimeDegree a)
      (Fin.addCases (start live occ B w top).heads (coldHeads a))
      (Fin.addCases (start live occ B w top).tapes (coldData a P q))
      (dockH (slots a) (Fin.addCases (finish live occ B w top).heads (coldHeads a)) H)
      (install (slots a) (Fin.addCases (finish live occ B w top).tapes (coldData a P q)) O) ∧
      O (Cold.port a (cch a))=exactListWord (GS a (CloseoutRowsUniversal.pool live occ)) ∧
      H (Cold.port a (cch a))=0 ∧
      O (Cold.port a (cnt a))=countWord a (CloseoutRowsUniversal.pool live occ) ∧
      H (Cold.port a (cnt a))=(countWord a (CloseoutRowsUniversal.pool live occ)).length ∧
      O (sourcePort a)=segment (CloseoutRowsUniversal.pool live occ) top ∧
      H (sourcePort a)=(segment (CloseoutRowsUniversal.pool live occ) top).length ∧
      O (Cold.port a (tot a))=UnaryTemplate.tape (ExtDecompositionBatch.B a (CloseoutRowsUniversal.pool live occ)) ∧
      H (Cold.port a (tot a))=1 ∧
      O (Cold.port a (dom a))=UnaryTemplate.tape q ∧ H (Cold.port a (dom a))=1 ∧
      O (Cold.port a (scr a))=List.replicate (ExtDecompositionBatch.B a (CloseoutRowsUniversal.pool live occ)) false ∧
      H (Cold.port a (scr a))=0 ∧
      O (Cold.port a (drv a))=List.replicate (SourceEnvelope.capacity a P) true ∧
      H (Cold.port a (drv a))=0 ∧
      O (Cold.port a (wsp a))=List.replicate (SourceEnvelope.capacity a P+1) false ∧
      H (Cold.port a (wsp a))=0 := by
  obtain ⟨r,hr,hfinal,_hs⟩ := PoolEntryLoop.segment_run live occ B w top hw hqw hb hm
  have writer : Step PoolEntryLoop.machine (PoolEntryLoop.budget occ.length B q w)
      (start live occ B w top).heads (start live occ B w top).tapes
      (finish live occ B w top).heads (finish live occ B w top).tapes :=
    Step.of_run hr (congrArg Configuration.heads hfinal) (congrArg Configuration.tapes hfinal)
  obtain ⟨H,O,source,fields⟩ := Cold.cold_run a P (CloseoutRowsUniversal.pool live occ) top hqP hi
  have paid := source.enlarge (Cold.budget_bound a P (CloseoutRowsUniversal.pool live occ) top hqP hi)
  have middle := writer.embed (coldHeads a) (coldData a P q)
  have last := paid.dock (slots a) (slots_injective a)
    (Fin.addCases (finish live occ B w top).heads (coldHeads a))
    (Fin.addCases (finish live occ B w top).tapes (coldData a P q))
    (by
      intro j
      by_cases hj : j=sourcePort a
      · subst j
        rw [slots,if_pos rfl,Fin.addCases_left,source_heads]
        rfl
      · rw [slots,if_neg hj,Fin.addCases_right]
        exact cold_heads_other a _ j hj)
    (by
      intro j
      by_cases hj : j=sourcePort a
      · subst j
        rw [slots,if_pos rfl,Fin.addCases_left,source_data]
        change ZeroPadding.pad 0 (PoolEntryBaseline.bank live B w _ _ 61)=_
        rw [ZeroPadding.pad_zero,PoolEntryBaseline.bank_output]
      · rw [slots,if_neg hj,Fin.addCases_right]
        exact cold_data_other a P q _ j hj)
  exact ⟨H,O,middle.seq last,fields⟩

end PoolColdSource.PoolCold
