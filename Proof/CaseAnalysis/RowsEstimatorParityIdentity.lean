import Proof.CaseAnalysis.RowsEstimatorParityRepeat

/-! An identity bottom is printed with its original coordinate, without a one-hot scratch bitmap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Identity
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def strokes (b : Bool) : List (Stroke 2):=
  Bitmap.strokes.map (fun f i=>(f i).map (fun g _=>g b))
def block (b : Bool) : Fin 2→List Bool:=![Fragment.body (bitWeight b),[true,b]]
def repeatBlock (b : Bool) (n : ℕ) (i : Fin 2):=(List.replicate n (block b i)).flatten
def onehot (q j : ℕ):=List.replicate j false++true::List.replicate (q-j-1) false

theorem word_exact (b x : Bool) : (fun i=>word (strokes b) x i)=block b := by
  funext i
  rw [show word (strokes b) x i=word Bitmap.strokes b i by
    simp [word,strokes,List.flatMap_map,emitted,byte,Option.map_map,Function.comp_def]]
  exact congrFun (Bitmap.word_exact b) i

theorem scan_block (b : Bool) (bits : List Bool) :
    (fun i=>bits.flatMap (fun x=>word (strokes b) x i))=repeatBlock b bits.length := by
  funext i
  induction bits with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.flatMap_cons,word_exact,List.length_cons,repeatBlock,List.replicate_succ,List.flatten_cons] at *
    exact congrArg (fun xs=>block b i++xs) ih

theorem identityMask_eq {q : ℕ} (j : Fin q) : identityMask j=onehot q j.val := by
  induction q with
  | zero=>exact Fin.elim0 j
  | succ q ih=>
    refine Fin.cases ?_ (fun k=>?_) j
    · simp [identityMask,List.ofFn_succ,onehot,List.ofFn_const]
    · have h := ih k
      simp only [identityMask,List.ofFn_succ,Fin.succ_inj] at *
      simp only [onehot,Fin.val_succ,List.replicate_succ,List.cons_append,Nat.add_sub_add_right] at *
      exact congrArg (false::·) h

noncomputable def suffix:=Repeat.machine (strokes false)
def swap : Fin 4→Fin 4:=![3,1,2,0]
theorem swap_injective : Function.Injective swap:=by decide
theorem swappedH (ambient local' : Fin 4→ℕ) :
    dockH swap ambient local'=![local' 3,local' 1,local' 2,local' 0] := by
  funext i;fin_cases i
  · exact dockH_slot swap swap_injective _ _ 3
  · exact dockH_slot swap swap_injective _ _ 1
  · exact dockH_slot swap swap_injective _ _ 2
  · exact dockH_slot swap swap_injective _ _ 0
theorem swappedT (ambient local' : Fin 4→List Bool) :
    RecoveryRootRound.install swap ambient local'=![local' 3,local' 1,local' 2,local' 0] := by
  funext i;fin_cases i
  · exact RecoveryRootRound.install_slot swap swap_injective _ _ 3
  · exact RecoveryRootRound.install_slot swap swap_injective _ _ 1
  · exact RecoveryRootRound.install_slot swap swap_injective _ _ 2
  · exact RecoveryRootRound.install_slot swap swap_injective _ _ 0
noncomputable def suffixOn:=RecoveryFocus.machine swap suffix
noncomputable def marked:=Composition.machine (Glyph.machine (strokes true))
  (DecompositionCountPosition.move (Scan.direction 2 .right))
noncomputable def markOn:=TapeEmbedding.machine 1 marked
noncomputable def machine:=Composition.machine (Composition.machine (Scan.machine (strokes false)) markOn) suffixOn

def atHead (qpos : ℕ) (out : Fin 2→List Bool) (jpos : ℕ) : Fin 4→ℕ:=![qpos,(out 0).length,(out 1).length,jpos]
def atData (q j : ℕ) (out : Fin 2→List Bool) : Fin 4→List Bool:=![CompareMachine.word q,out 0,out 1,CompareMachine.word j]

 theorem suffix_run (q j : ℕ) (out : Fin 2→List Bool) (hj:j<q) :
    Step suffixOn ((q-j-1)*(2*(strokes false).length+2)+q+3)
      (atHead (j+2) out 1) (atData q j out)
      (atHead 1 (fun i=>out i++repeatBlock false (q-j-1) i) 1)
      (atData q j (fun i=>out i++repeatBlock false (q-j-1) i)) := by
  obtain ⟨r,hr,rf,_⟩:=Repeat.repeat_run (strokes false)
    (readTapeBit (CompareMachine.word j) 1) (CompareMachine.word j) 1 q (j+1) (q-j-1) out rfl (by omega)
  have run:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have hcopies : Repeat.copies (strokes false) (readTapeBit (CompareMachine.word j) 1) (q-j-1)=repeatBlock false (q-j-1):=by
    funext i
    simp only [Repeat.copies,repeatBlock,word_exact]
  rw [hcopies] at run
  have actual:=run.focus swap swap_injective (atHead (j+2) out 1) (atData q j out)
  simp only [swappedH,swappedT] at actual
  apply actual.congr_in ?_ ?_ |>.congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

def written (bits : List Bool) (i : Fin 2):=bits.flatMap (fun b=>block b i)

theorem write_eq (bits : List Bool) : written bits=![Fragment.body (weights bits),Fragment.body bits] := by
  have h:=Bitmap.cache_exact bits
  simp only [Bitmap.word_exact] at h
  exact h

theorem identity_run (q j : ℕ) (out : Fin 2→List Bool) (hj : j<q) :
    Step machine (40*q+40) (atHead 1 out 1) (atData q j out)
      (atHead 1 (fun i=>out i++written (onehot q j) i) 1)
      (atData q j (fun i=>out i++written (onehot q j) i)) := by
  have hq : [false]++List.replicate j true++List.replicate (q-j) true=CompareMachine.word q := by
    rw [List.append_assoc,←List.replicate_add,Nat.add_sub_of_le (Nat.le_of_lt hj)]
    rfl
  have first:=Scan.scan_run (strokes false) [false] (List.replicate j true)
    (List.replicate (q-j) true) out
  simp only [hq,show ∀ i,(List.replicate j true).flatMap (fun b=>word (strokes false) b i)=repeatBlock false j i from
    fun i=>by simpa only [List.length_replicate] using congrFun (scan_block false (List.replicate j true)) i,List.length_replicate] at first
  let pre : Fin 2→List Bool:=fun i=>out i++repeatBlock false j i
  have first' : Step (Scan.machine (strokes false)) (j*(2*(strokes false).length+5)+3)
      (atHead 1 out 1) (atData q j out) (atHead (j+1) pre 1) (atData q j pre) := by
    apply first.congr_in ?_ ?_ |>.congr ?_ ?_
    all_goals funext i;fin_cases i <;> first | rfl | (change 1+j=j+1;omega)
  have mark:=word_run (strokes true) (readTapeBit (CompareMachine.word q) (j+1))
    (CompareMachine.word q) (j+1) pre rfl
  simp only [show ∀ i,word (strokes true) (readTapeBit (CompareMachine.word q) (j+1)) i=block true i from
    fun i=>congrFun (word_exact true _) i] at mark
  have markedRun:=(mark.seq (Scan.advance (CompareMachine.word q) (j+1) (fun i=>pre i++block true i))).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word j)
  let middle : Fin 2→List Bool:=fun i=>pre i++block true i
  have middleRun : Step markOn (2*(strokes true).length+2)
      (atHead (j+1) pre 1) (atData q j pre) (atHead (j+2) middle 1) (atData q j middle) := by
    apply markedRun.congr_in ?_ ?_ |>.congr ?_ ?_
    all_goals funext i;fin_cases i <;>rfl
  have last:=suffix_run q j middle hj
  have whole:=(first'.seq middleRun).seq last
  have hcost : j*(2*(strokes false).length+5)+3+1+(2*(strokes true).length+2)+1+
      ((q-j-1)*(2*(strokes false).length+2)+q+3)≤40*q+40 := by
    simp only [strokes,List.length_map,Bitmap.strokes,List.length_cons,List.length_nil]
    omega
  have he : (fun i=>middle i++repeatBlock false (q-j-1) i)=(fun i=>out i++written (onehot q j) i) := by
    funext i
    have rep (n : ℕ) : (List.replicate n false).flatMap (fun b=>block b i)=repeatBlock false n i := by
      induction n with
      | zero=>rfl
      | succ n ih=>simp only [List.replicate_succ,List.flatMap_cons,repeatBlock,List.flatten_cons] at *;rw [ih]
    simp only [middle,pre,written,onehot,List.flatMap_append,List.flatMap_cons,rep,List.append_assoc]
  rw [he] at whole
  exact whole.enlarge hcost

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Identity
