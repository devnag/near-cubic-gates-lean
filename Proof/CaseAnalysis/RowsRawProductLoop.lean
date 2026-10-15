import Proof.CaseAnalysis.RowsRawProductBody

/-! The actual two raw polynomial streams determine the full Cartesian
product. The left and right stream loops create every original monomial
occurrence once, including empty inputs, before one final stream marker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsRawProductBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 5 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def finish:=TapeEmbedding.machine 1 (CloseoutRowsRawProductFields.mark false false)
noncomputable def sizes : Fin 3→ℕ:=![1,2+(Fintype.card (RecoveryCalls.Control CloseoutRowsRawProductRow.sizes)+2)+3,2]
noncomputable def programs : (i : Fin 3)→Machine 5 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>CloseoutRowsRawProductBody.machine
  | ⟨2,_⟩=>finish
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 5→Bool) : Option (Fin 3):=
  if i=0 then some (if bits 0 then 1 else 2) else if i=1 then some 0 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 3) (C pos : ℕ) (left right out : List Bool):=
  controlConfig (RecoveryCalls.code sizes i)
    (⟨(programs i).start,heads pos out,data C left right out⟩ : Configuration 5 (sizes i))
noncomputable def final (C pos : ℕ) (left right out : List Bool):=
  RecoveryCalls.stopped sizes (heads pos out) (data C left right out)
def product (left right : List (List ℕ)):=left.flatMap (fun l=>right.map (fun r=>l++r))
def budget (C count : ℕ):=count*(3*C+7)+3

theorem probe (C : ℕ) (pre tail right out : List Bool) (bit : Bool) :
    Timed machine 1 (entry 0 C pre.length (pre++bit::tail) right out)
      (entry (if bit then 1 else 2) C pre.length (pre++bit::tail) right out) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length out,data C (pre++bit::tail) right out⟩ :
        Configuration 5 (sizes 0)).scanned=some (if bit then 1 else 2):=by
    simp [next,Configuration.scanned,heads,data,Streaming.read_append]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next 0 (if bit then 1 else 2) _ (by rfl) hn)

theorem body (C : ℕ) (left : List ℕ) (right : List (List ℕ)) (pre tail out : List Bool)
    (hl : (left.flatMap ExtIncidence.block).length+1≤C)
    (hc : CloseoutRowsRawProductRow.budget left right≤C) :
    ∃ time≤3*C+6,Timed machine time
      (entry 1 C pre.length (pre++ExtIncidence.monomialWord left++tail) (ExtIncidence.stream right) out)
      (entry 0 C (pre.length+(ExtIncidence.monomialWord left).length)
        (pre++ExtIncidence.monomialWord left++tail) (ExtIncidence.stream right)
        (out++CloseoutRowsRawProductRow.word left right)) := by
  obtain ⟨r,hr,rh,rt,_⟩:=CloseoutRowsRawProductBody.body_run C left right pre tail out hl hc
  obtain ⟨time,ht,trace⟩:=call_receipt sizes programs 0 next 1 0 _ _ r hr (by rfl)
  have same:RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes=
      ⟨(programs 0).start,heads (pre.length+(ExtIncidence.monomialWord left).length)
        (out++CloseoutRowsRawProductRow.word left right),
        data C (pre++ExtIncidence.monomialWord left++tail) (ExtIncidence.stream right)
          (out++CloseoutRowsRawProductRow.word left right)⟩:=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [same] at trace
  refine ⟨time,?_,trace⟩
  unfold CloseoutRowsRawProductBody.budget at ht
  omega

theorem stop (C pos : ℕ) (left right out : List Bool) :
    ∃ time≤2,Timed machine time (entry 2 C pos left right out)
      (final C pos left right (out++[false])) := by
  have raw:=(CloseoutRowsRawProductFields.mark_run false false C pos 0 left right out).embed
    (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate C false)
  have run:Step finish 1 (heads pos out) (data C left right out)
      (heads pos (out++[false])) (data C left right (out++[false])):=by
    apply (raw.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rh,rt,_⟩:=run
  obtain ⟨time,ht,trace⟩:=stop_receipt sizes programs 0 next 2 1 _ r hr (by rfl)
  rw [rh,rt] at trace
  exact ⟨time,ht,trace⟩

theorem remaining (C : ℕ) (left right : List (List ℕ)) (pre tail out : List Bool)
    (hl : ∀ l∈left,(l.flatMap ExtIncidence.block).length+1≤C)
    (hc : ∀ l∈left,CloseoutRowsRawProductRow.budget l right≤C) :
    ∃ time≤budget C left.length,Timed machine time
      (entry 0 C pre.length (pre++ExtIncidence.stream left++tail) (ExtIncidence.stream right) out)
      (final C (pre.length+(left.flatMap ExtIncidence.monomialWord).length)
        (pre++ExtIncidence.stream left++tail) (ExtIncidence.stream right)
        (out++ExtIncidence.stream (product left right))) := by
  induction left generalizing pre out with
  | nil=>
    obtain ⟨time,ht,tr⟩:=stop C pre.length (pre++false::tail) (ExtIncidence.stream right) out
    have all:=(probe C pre tail (ExtIncidence.stream right) out false).trans tr
    exact ⟨1+time,by simp [budget];omega,by simpa [ExtIncidence.stream,product] using all⟩
  | cons l left ih=>
    obtain ⟨first,hfirst,tr⟩:=body C l right pre (ExtIncidence.stream left++tail) out
      (hl l (by simp)) (hc l (by simp))
    obtain ⟨rest,hrest,tailTrace⟩:=ih (pre++ExtIncidence.monomialWord l)
      (out++CloseoutRowsRawProductRow.word l right)
      (fun m hm=>hl m (by simp [hm])) (fun m hm=>hc m (by simp [hm]))
    simp only [List.append_assoc,List.length_append] at tr tailTrace
    have start:=probe C pre
      (l.flatMap ExtIncidence.block++false::(ExtIncidence.stream left++tail))
      (ExtIncidence.stream right) out true
    have source:pre++true::(l.flatMap ExtIncidence.block++false::(ExtIncidence.stream left++tail))=
        pre++ExtIncidence.monomialWord l++(ExtIncidence.stream left++tail):=by
      simp [ExtIncidence.monomialWord,List.append_assoc]
    rw [source] at start
    simp only [List.append_assoc] at start
    have all:=start.trans (tr.trans tailTrace)
    refine ⟨1+(first+rest),?_,?_⟩
    · simp only [budget,List.length_cons] at *
      nlinarith
    · simpa only [ExtIncidence.stream_cons,ExtIncidence.stream,product,List.flatMap_cons,
        List.flatMap_append,List.length_append,CloseoutRowsRawProductRow.word,List.append_assoc,
        Nat.add_assoc] using all

theorem product_run (C : ℕ) (left right : List (List ℕ)) (out : List Bool)
    (hl : ∀ l∈left,(l.flatMap ExtIncidence.block).length+1≤C)
    (hc : ∀ l∈left,CloseoutRowsRawProductRow.budget l right≤C) :
    Step machine (budget C left.length) (heads 0 out)
      (data C (ExtIncidence.stream left) (ExtIncidence.stream right) out)
      (heads (left.flatMap ExtIncidence.monomialWord).length (out++ExtIncidence.stream (product left right)))
      (data C (ExtIncidence.stream left) (ExtIncidence.stream right) (out++ExtIncidence.stream (product left right))) := by
  obtain ⟨time,ht,trace⟩:=remaining C left right [] [] out hl hc
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at trace
  obtain ⟨r,hr,rf,_⟩:=trace.run (by simp [machine,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel machine time (budget C left.length-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductLoop
