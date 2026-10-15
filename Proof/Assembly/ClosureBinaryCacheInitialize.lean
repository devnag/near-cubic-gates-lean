import Proof.Assembly.ClosureBinaryCacheFanout

/-! Actual one-pass construction of all repeated assignment working/master
words followed by the complete binary enumeration. The finite nine-word
metadata palette is the explicit input to the preceding arithmetic stage. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdInitialize
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound ExtIncidence
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding SignedSortKey BinaryCacheColdPalette
open scoped BigOperators

def dest : Fin 220→Fin 224 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,99,100,101,102,103,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222]
def slots : Fin 231→Fin 235 :=
  fun i=>Fin.addCases
    (fun j=>Fin.addCases (fun k : Fin 9=>(k.castAdd 2).natAdd 224)
      (fun k=>Fin.addCases (fun d : Fin 220=>(dest d).castAdd 11) (fun _ : Fin 1=>233) k) j)
    (fun _ : Fin 1=>234) i
theorem slots_injective : Function.Injective slots := by decide
theorem dest_private : ∀ j,dest j≠34 ∧ dest j≠98 ∧ dest j≠104 ∧ dest j≠223 := by decide
theorem dest_complete : ∀ i,(∀ j,dest j≠i) → i=34 ∨ i=98 ∨ i=104 ∨ i=223 := by decide
def choice (j : Fin 220) := select (dest j)
noncomputable def prepare := RecoveryFocus.machine slots (NativeFanout.machine choice)
noncomputable def machine := Composition.machine prepare (TapeEmbedding.machine 11 HardwireAssignments.machine)

variable {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (B w : Nat)
def oldInput (out : List Bool) (i : Fin 224) : List Bool :=
  if i=34 then out else if i=98 then exactListWord gs
  else if i=104 then RepairOrdinary.frame (binary live.card 0)
  else if i=223 then CompareMachine.word (2^live.card-1) else []
noncomputable def input (out : List Bool) : Fin 235→List Bool :=
  fun i=>Fin.addCases (oldInput live gs out)
    (fun j=>Fin.addCases (words live gs B w)
      (![List.replicate (U live gs B w) true,[]] : Fin 2→List Bool) j) i
noncomputable def extra : Fin 11→List Bool :=
  fun j=>Fin.addCases (words live gs B w)
    (![List.replicate (U live gs B w) true,List.replicate (U live gs B w+1) false] : Fin 2→List Bool) j
noncomputable def output (j : Nat) (out : List Bool) : Fin 235→List Bool :=
  fun i=>Fin.addCases (BinaryCacheColdFanout.request live gs B w j out) (extra live gs B w) i
def heads (out : List Bool) : Fin 235→Nat :=
  fun i=>Fin.addCases (BinaryCacheColdFanout.heads out) (fun _ : Fin 11=>0) i

theorem input_private (out : List Bool) (j : Fin 220) : oldInput live gs out (dest j)=[] := by
  simp only [oldInput,(dest_private j).1,(dest_private j).2.1,(dest_private j).2.2.1,
    (dest_private j).2.2.2,↓reduceIte]
theorem output_private (j : Fin 220) (out : List Bool) :
    BinaryCacheColdFanout.request live gs B w 0 out (dest j)=
      ZeroPadding.pad (U live gs B w) (NativeFanout.word choice (words live gs B w) j) := by
  simp only [BinaryCacheColdFanout.request,(dest_private j).1,(dest_private j).2.1,
    (dest_private j).2.2.1,(dest_private j).2.2.2,↓reduceIte]
  rfl

theorem prepare_run (out : List Bool) :
    Step prepare (2*U live gs B w+4) (heads out) (input live gs B w out)
      (heads out) (output live gs B w 0 out) := by
  have hh : ∀ j,heads out (slots j)=0 := by
    intro j
    refine Fin.addCases (m:=230) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=9) (n:=221) (fun j=>?_) (fun j=>?_) j
      · simp only [heads,slots,Fin.addCases_left,Fin.addCases_right]
      · refine Fin.addCases (m:=220) (n:=1) (fun j=>?_) (fun j=>?_) j
        · simp only [heads,slots,Fin.addCases_left,Fin.addCases_right,BinaryCacheColdFanout.heads,
            (dest_private j).1,(dest_private j).2.2.2,↓reduceIte]
        · fin_cases j;rfl
    · fin_cases j;rfl
  have hi : ∀ j,input live gs B w out (slots j)=NativeFanout.input (m:=220) (words live gs B w) (U live gs B w) j := by
    intro j
    refine Fin.addCases (m:=230) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=9) (n:=221) (fun j=>?_) (fun j=>?_) j
      · simp only [input,slots,NativeFanout.input,Fin.addCases_left,Fin.addCases_right]
      · refine Fin.addCases (m:=220) (n:=1) (fun j=>?_) (fun j=>?_) j
        · simpa only [input,slots,NativeFanout.input,Fin.addCases_left,Fin.addCases_right] using
            input_private live gs out j
        · fin_cases j;rfl
    · fin_cases j;rfl
  have ho : install slots (input live gs B w out)
      (NativeFanout.output choice (words live gs B w) (U live gs B w))=output live gs B w 0 out := by
    apply HierarchyAllocation.install_eq slots slots_injective
    · intro j
      refine Fin.addCases (m:=230) (n:=1) (fun j=>?_) (fun j=>?_) j
      · refine Fin.addCases (m:=9) (n:=221) (fun j=>?_) (fun j=>?_) j
        · simp only [output,extra,slots,NativeFanout.output,Fin.addCases_left,Fin.addCases_right]
        · refine Fin.addCases (m:=220) (n:=1) (fun j=>?_) (fun j=>?_) j
          · simpa only [output,slots,NativeFanout.output,Fin.addCases_left,Fin.addCases_right] using
              output_private live gs B w j out
          · fin_cases j;rfl
      · fin_cases j;rfl
    · intro i hi
      have outside : ∀ i,(∀ j,slots j≠i) → i=34 ∨ i=98 ∨ i=104 ∨ i=223 := by decide
      rcases outside i hi with rfl|rfl|rfl|rfl <;>rfl
  have actual := (Step.of_ready (NativeFanout.ready choice (words live gs B w) (U live gs B w)
    (BinaryCacheColdFanout.words_fit live gs B w))).focus slots slots_injective (heads out) (input live gs B w out)
  exact (actual.congr_in (dockH_existing _ _ _ hh) (install_existing _ _ _ hi)).congr
    (dockH_existing _ _ _ hh) ho

def budget := 2*U live gs B w+5+HardwireAssignments.budget live gs B w (2*live.card)
theorem run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (out : List Bool) :
    Step machine (budget live gs B w) (heads out) (input live gs B w out)
      (heads (out++HardwireAssignments.emitted live gs))
      (output live gs B w (2^live.card-1) (out++HardwireAssignments.emitted live gs)) := by
  have final := (BinaryCacheColdFanout.run live gs B w hbytes hw hm out).embed
    (fun _ : Fin 11=>0) (extra live gs B w)
  exact (prepare_run live gs B w out).seq final

end NearCubicWires.P1Closure.BinaryCacheColdInitialize
