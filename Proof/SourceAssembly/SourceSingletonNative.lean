import Proof.SourceAssembly.SourceCircuitFrame

/- Singleton THR request writer. Only L and target enter the finite code;
q and the circuit payload are physically read from the two retained frames. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySingletonNative
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity
noncomputable section

def strokes (bits : List Bool) : List (Glyph.Stroke 1):=bits.map (fun b=>fun _=>some (fun _=>b))
def literal (bits : List Bool):=Glyph.machine (strokes bits)
theorem literal_word (bits : List Bool) (b : Bool) (i : Fin 1) : Glyph.word (strokes bits) b i=bits := by
  induction bits with
  | nil=>rfl
  | cons x xs ih=>simp only [strokes,List.map_cons,Glyph.word,List.flatMap_cons,Glyph.emitted,Glyph.byte,Option.map_some,Option.toList_some];exact congrArg (List.cons x) ih

def H (pos : Nat) (out : List Bool) (i : Fin 4):=if i=1 then pos else if i=2 then out.length else 0
def A (q : Nat) (circuit out log : List Bool) (i : Fin 4):=
  if i=0 then frame (natWord q) else if i=1 then frame circuit else if i=2 then out else log
def literalSlots : Fin 2→Fin 4:=![0,2]
def rawSlots : Fin 3→Fin 4:=![0,2,3]
def frameSlots : Fin 2→Fin 4:=![1,2]
def emit (bits : List Bool):=RecoveryFocus.machine literalSlots (literal bits)
def raw:=RecoveryFocus.machine rawSlots CompetitorRawScalarEmit.machine
def copy:=RecoveryFocus.machine frameSlots (CloseoutRowsTupleSeek.frameMachine true)
def tail (L target : Nat):=natWord L++natWord target++natWord 1
def prefixWord (q L target : Nat):=natWord 1++natWord q++tail L target
def native (q L target : Nat) (circuit : List Bool):=prefixWord q L target++frame circuit
def machine (L target : Nat):=Composition.machine (emit (natWord 1))
  (Composition.machine raw (Composition.machine (emit (tail L target)) copy))
def budget (q L target : Nat) (circuit : List Bool):=
  2*(natWord 1).length+1+(4*(natWord q).length+3+1+(2*(tail L target).length+1+(2*circuit.length+1)))

theorem emit_run (bits : List Bool) (q : Nat) (circuit out log : List Bool) :
    Step (emit bits) (2*bits.length) (H 0 out) (A q circuit out log)
      (H 0 (out++bits)) (A q circuit (out++bits) log) := by
  have h:=Glyph.word_run (strokes bits) (readTapeBit (frame (natWord q)) 0)
    (frame (natWord q)) 0 (fun _ : Fin 1=>out) rfl
  simp only [literal_word] at h
  have hl : (strokes bits).length=bits.length:=List.length_map _
  rw [hl] at h
  have hd:=h.dock literalSlots (by decide) (H 0 out) (A q circuit out log)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply hd.congr ?_ ?_
  · funext i;fin_cases i
    · exact dockH_slot literalSlots (by decide) _ _ 0
    · exact dockH_other literalSlots _ _ 1 (by decide)
    · exact dockH_slot literalSlots (by decide) _ _ 1
    · exact dockH_other literalSlots _ _ 3 (by decide)
  · funext i;fin_cases i
    · exact install_slot literalSlots (by decide) _ _ 0
    · exact install_other literalSlots _ _ 1 (by decide)
    · exact install_slot literalSlots (by decide) _ _ 1
    · exact install_other literalSlots _ _ 3 (by decide)

theorem raw_run (q : Nat) (circuit out : List Bool) :
    Step raw (4*(natWord q).length+3) (H 0 out) (A q circuit out [])
      (H 0 (out++natWord q)) (A q circuit (out++natWord q) (List.replicate (2*(natWord q).length+1) false)) := by
  obtain ⟨r,hr,rf,_⟩:=CompetitorRawScalarEmit.append_run (natWord q) [] out
  simp only [List.append_nil] at hr rf
  have h:Step CompetitorRawScalarEmit.machine (4*(natWord q).length+3)
      (![0,out.length,0]) (![frame (natWord q),out,[]])
      (![0,(out++natWord q).length,0]) (![frame (natWord q),out++natWord q,List.replicate (2*(natWord q).length+1) false]):=
    Step.of_run hr (by rw [rf];rfl) (by rw [rf];rfl)
  have hd:=h.dock rawSlots (by decide) (H 0 out) (A q circuit out [])
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply hd.congr ?_ ?_
  · funext i;fin_cases i
    · exact dockH_slot rawSlots (by decide) _ _ 0
    · exact dockH_other rawSlots _ _ 1 (by decide)
    · exact dockH_slot rawSlots (by decide) _ _ 1
    · exact dockH_slot rawSlots (by decide) _ _ 2
  · funext i;fin_cases i
    · exact install_slot rawSlots (by decide) _ _ 0
    · exact install_other rawSlots _ _ 1 (by decide)
    · exact install_slot rawSlots (by decide) _ _ 1
    · exact install_slot rawSlots (by decide) _ _ 2

theorem copy_run (q : Nat) (circuit out log : List Bool) :
    Step copy (2*circuit.length+1) (H 0 out) (A q circuit out log)
      (H (frame circuit).length (out++frame circuit)) (A q circuit (out++frame circuit) log) := by
  have h:=CloseoutRowsTupleSeek.frame_run true [] circuit [] out
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,CloseoutRowsTupleSeek.selected,if_true] at h
  have hd:=h.dock frameSlots (by decide) (H 0 out) (A q circuit out log)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply hd.congr ?_ ?_
  · funext i;fin_cases i
    · exact dockH_other frameSlots _ _ 0 (by decide)
    · exact dockH_slot frameSlots (by decide) _ _ 0
    · exact dockH_slot frameSlots (by decide) _ _ 1
    · exact dockH_other frameSlots _ _ 3 (by decide)
  · funext i;fin_cases i
    · exact install_other frameSlots _ _ 0 (by decide)
    · exact install_slot frameSlots (by decide) _ _ 0
    · exact install_slot frameSlots (by decide) _ _ 1
    · exact install_other frameSlots _ _ 3 (by decide)

theorem run (q L target : Nat) (circuit : List Bool) :
    Step (machine L target) (budget q L target circuit) (fun _=>0) (A q circuit [] [])
      (H (frame circuit).length (native q L target circuit))
      (A q circuit (native q L target circuit) (List.replicate (2*(natWord q).length+1) false)) := by
  have first:=emit_run (natWord 1) q circuit [] []
  simp only [List.nil_append] at first
  have second:=raw_run q circuit (natWord 1)
  have third:=emit_run (tail L target) q circuit (natWord 1++natWord q) (List.replicate (2*(natWord q).length+1) false)
  have last:=copy_run q circuit (prefixWord q L target) (List.replicate (2*(natWord q).length+1) false)
  exact (first.seq (second.seq (third.seq last))).congr_in (by funext i;fin_cases i <;>rfl) rfl

end
end SourceAssemblySingletonNative
