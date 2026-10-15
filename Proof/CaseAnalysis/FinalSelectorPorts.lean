import Proof.CaseAnalysis.FinalSelectorState
import Proof.CaseAnalysis.RowsTouchingCoordinateMaskPorts

/-! A.4 cold start, part 2: the PORT CHART of the selector's entry
configuration.

`Selector.loop_run` is entered at `RepeatMachine.cfg 0 (Selector.entry ...) q 1`.
Unfolding that configuration gives one closed-form word per physical tape.
Each of the 35 equalities below is the exact obligation a cold loader has
to discharge; nothing here assumes any of them is already on a tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open CloseoutRowsTouching CloseoutRowsGateSupport
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coldEntry {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (tail : List Bool):=Selector.entry support K w P C D E (coldState q K) tail 0 []

variable {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ) (tail : List Bool)

theorem port00:(coldEntry support K w P C D E tail).tapes 0=GateFoldReady.supportWord support++tail:=rfl

theorem port01:(coldEntry support K w P C D E tail).tapes 1=List.replicate q false:=by
  change Selector.data support K w P C D E 0 (coldState q K) tail 1=_
  rw [Selector.data_mask]
  have he:(fun i : Fin q=>decide (i∈(∅ : Finset (Fin q))))=(fun _ : Fin q=>false):=by
    funext i;simp
  change gateMembers (∅ : Finset (Fin q))=_
  simp only [gateMembers,he,List.ofFn_const]

theorem port02:(coldEntry support K w P C D E tail).tapes 2=List.ofFn (fun i : Fin q=>decide (i.val=0)):=by
  change SupportScan.masks (Coordinate.supportCells (MaskShift.cells (∅ : Finset (Fin q)) 0)) 1=_
  rw [Coordinate.support_masks]
  change (MaskShift.cells (∅ : Finset (Fin q)) 0).map MaskShift.current=_
  simp only [MaskShift.cells,List.map_ofFn,Function.comp_def,MaskShift.current]

theorem port03:(coldEntry support K w P C D E tail).tapes 3=List.ofFn (fun i : Fin q=>decide (0 < i.val)):=by
  change SupportScan.masks (Coordinate.supportCells (MaskShift.cells (∅ : Finset (Fin q)) 0)) 2=_
  rw [Coordinate.support_masks]
  change (MaskShift.cells (∅ : Finset (Fin q)) 0).map MaskShift.remaining=_
  simp only [MaskShift.cells,List.map_ofFn,Function.comp_def,MaskShift.remaining]

theorem port04:(coldEntry support K w P C D E tail).tapes 4=[]:=rfl
theorem port05:(coldEntry support K w P C D E tail).tapes 5=[]:=rfl
theorem port06:(coldEntry support K w P C D E tail).tapes 6=[]:=rfl
theorem port07:(coldEntry support K w P C D E tail).tapes 7=List.replicate C false:=rfl
theorem port08:(coldEntry support K w P C D E tail).tapes 8=List.replicate P true:=rfl
theorem port09:(coldEntry support K w P C D E tail).tapes 9=PascalTable.table q:=rfl
theorem port10:(coldEntry support K w P C D E tail).tapes 10=UnaryTemplate.tape (PascalReady.width q):=rfl
theorem port11:(coldEntry support K w P C D E tail).tapes 11=ZeroPadding.pad P (CompareMachine.word K):=rfl
theorem port12:(coldEntry support K w P C D E tail).tapes 12=[]:=rfl
theorem port13:(coldEntry support K w P C D E tail).tapes 13=List.replicate (PascalReady.width q) false:=rfl
theorem port14:(coldEntry support K w P C D E tail).tapes 14=[]:=rfl
theorem port15:(coldEntry support K w P C D E tail).tapes 15=[]:=rfl
theorem port16:(coldEntry support K w P C D E tail).tapes 16=CompareMachine.word w:=rfl
theorem port17:(coldEntry support K w P C D E tail).tapes 17=List.replicate (2*w+1) true:=rfl
theorem port18:(coldEntry support K w P C D E tail).tapes 18=frame (binary w 0):=rfl
theorem port19:(coldEntry support K w P C D E tail).tapes 19=frame (binary w 0):=rfl
theorem port20:(coldEntry support K w P C D E tail).tapes 20=[]:=rfl
theorem port21:(coldEntry support K w P C D E tail).tapes 21=List.replicate (4*w+3) false:=rfl
theorem port22:(coldEntry support K w P C D E tail).tapes 22=List.replicate (2*w+1) false:=rfl
theorem port23:(coldEntry support K w P C D E tail).tapes 23=ZeroPadding.pad P (CompareMachine.word (K-1)):=rfl
theorem port24:(coldEntry support K w P C D E tail).tapes 24=CompareMachine.word G:=rfl
theorem port25:(coldEntry support K w P C D E tail).tapes 25=List.replicate D false:=rfl
theorem port26:(coldEntry support K w P C D E tail).tapes 26=ZeroPadding.pad P (CompareMachine.word (q-K)):=rfl
theorem port27:(coldEntry support K w P C D E tail).tapes 27=[]:=rfl
theorem port28:(coldEntry support K w P C D E tail).tapes 28=[]:=rfl
theorem port29:(coldEntry support K w P C D E tail).tapes 29=[false]:=rfl
theorem port30:(coldEntry support K w P C D E tail).tapes 30=frame (binary w 0):=rfl
theorem port31:(coldEntry support K w P C D E tail).tapes 31=CompareMachine.word q:=rfl
theorem port32:(coldEntry support K w P C D E tail).tapes 32=[false]:=rfl
theorem port33:(coldEntry support K w P C D E tail).tapes 33=List.replicate E false:=rfl
theorem port34:(coldEntry support K w P C D E tail).tapes 34=ZeroPadding.pad P (CompareMachine.word K):=rfl

/-- Only the retained gate driver and the original q counter start off cell 0. -/
theorem cold_heads:(coldEntry support K w P C D E tail).heads=
    (fun i : Fin 35=>if i.val=24∨i.val=31 then 1 else 0):=by
  funext i
  change Coordinate.heads i=_
  fin_cases i <;> rfl

/-- The two closed forms a physical marker writer has to produce. -/
theorem head_marker (n : ℕ) (hn:0<n):
    List.ofFn (fun i : Fin n=>decide (i.val=0))=true::List.replicate (n-1) false:=by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_cons,List.length_replicate]
    omega
  · intro m h1 h2
    simp only [List.getElem_ofFn]
    cases m with
    | zero=>simp
    | succ j=>simp

theorem tail_marker (n : ℕ) (hn:0<n):
    List.ofFn (fun i : Fin n=>decide (0 < i.val))=false::List.replicate (n-1) true:=by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_cons,List.length_replicate]
    omega
  · intro m h1 h2
    simp only [List.getElem_ofFn]
    cases m with
    | zero=>simp
    | succ j=>simp

theorem binary_zero (p : ℕ):binary p 0=List.replicate p false:=by
  induction p with
  | zero=>rfl
  | succ m ih=>simp [binary,ih,List.replicate_succ]

/-- Port 2 is the width-`n` binary one, a word the accepted binary emitters write. -/
theorem head_marker_binary (n : ℕ) (hn:0<n):
    List.ofFn (fun i : Fin n=>decide (i.val=0))=binary n 1:=by
  rw [head_marker n hn]
  obtain ⟨m,rfl⟩:∃ m,n=m+1:=⟨n-1,by omega⟩
  rw [binary,binary_zero]
  simp

/-- Port 3 is literally a unary counter word, which many accepted machines write. -/
theorem tail_marker_word (n : ℕ) (hn:0<n):
    List.ofFn (fun i : Fin n=>decide (0 < i.val))=CompareMachine.word (n-1):=by
  rw [tail_marker n hn]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutFinalSelector
