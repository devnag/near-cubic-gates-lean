import Proof.MachineModel.BankExecution
import Proof.MachineModel.BankFields

/-! Physical raw incidence production, paid cursor return, and the EXISTING
polynomial consumer. All other native fields are explicit caller-produced
inputs. The separate zero-polynomial branch is not supplied here. -/
namespace NearCubicWires.ExtIncidence.BankConsumer
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 116 := i.castAdd 3
theorem old_injective : Function.Injective old := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 116=>k.val) h)
theorem old_ne (i : Fin 113) (k : Fin 116) (hk : 113 ≤ k.val) : old i≠k := by
  intro he
  have hv:=congrArg Fin.val he
  change i.val=k.val at hv
  omega

noncomputable def consumer:=RecoveryFocus.machine old CloseoutRowsBankPolynomial.machine
noncomputable def machine:=Composition.machine BankExecution.machine consumer
def budget (B C Q : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+CloseoutRowsBankPolynomial.budget Q C

theorem count_bound (n p F w B Q M : ℕ) (hM : M ≤ 2^w) :
    M ≤ CloseoutRowsPreparationBounds.capacity n p F w B Q := by
  have hc:=CloseoutRowsPreparationFits.cursor_fits n p F w B Q M 1 hM (by omega)
  unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
    RowMaskLookupReusable.capacity RowMaskLookup.budget at hc
  nlinarith

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (p F Q w : ℕ) (out pre tail : List Bool)
    (hM : 0 < ms.length) (hw : ms.length < 2^w) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (H : Fin 116 → ℕ) (A : Fin 116 → List Bool)
    (hheads : ∀ i,H (old i)=CloseoutRowsBankFields.heads out i)
    (hother : ∀ i,i≠36 → A (old i)=
      (CloseoutRowsBankPolynomial.entry gs p F Q w
        (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) (rawRows ms) out).tapes i)
    (hext : H 113=pre.length ∧ H 114=0 ∧ H 115=0)
    (hsource : A 113=pre++stream (rawIndices ms)++tail)
    (hblank : A 36=List.replicate (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hscratch : A 114=List.replicate (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hcount : A 115=List.replicate (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false) :
    let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom machine (budget gs.length C Q (rawIndices ms)) ⟨machine.start,H,A⟩=some result ∧
      result.steps ≤ budget gs.length C Q (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=ZeroPadding.pad C (List.replicate ms.length true) := by
  dsimp only
  let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  let pos:=pre.length+(stream (rawIndices ms)).length
  let nextH:=BankExecution.changedHeads H pos 0 0
  let nextA:=BankExecution.changedTapes A C (rawRows ms).flatten ms.length
  have hB:gs.length ≤ C:=by
    have hs:=CloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
    unfold CloseoutRowsPreparationBounds.scale at hs
    dsimp only [C]
    omega
  have hh:∀ j,H (BankExecution.slots j)=Padded.heads pre.length 0 0 j:=by
    intro j;fin_cases j
    · exact hext.1
    · exact hheads 38
    · exact hext.2.1
    · exact hheads 36
    · exact hext.2.2
  have ht:∀ j,A (BankExecution.slots j)=Padded.tapes C gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j:=by
    intro j;fin_cases j
    · exact hsource
    · exact (hother 38 (by decide)).trans (BankFields.template gs p F Q w C (rawRows ms) out)
    · exact hscratch
    · change A 36=ZeroPadding.pad C []
      simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hblank
    · change A 115=ZeroPadding.pad C []
      simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hcount
  have first:=BankExecution.raw_run ms C hB pre tail H A hh ht
    (BankFields.table_bound gs p F Q w ms hw.le) (count_bound (l+r) p F w gs.length Q ms.length hw.le)
    (hheads 104) (hheads 105)
    ((hother 104 (by decide)).trans (BankFields.driver gs p F Q w C (rawRows ms) out))
    ((hother 105 (by decide)).trans (BankFields.log gs p F Q w C (rawRows ms) out))
  have length_rows:(rawRows ms).length=ms.length:=by simp only [rawRows,List.length_map]
  have row_length:∀ row∈rawRows ms,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  obtain ⟨base,hbase,bh,bo,bc,bs⟩:=CloseoutRowsBankPolynomial.polynomial_run gs p F Q w (rawRows ms) out
    row_length (by simpa only [length_rows] using hM) (by simpa only [length_rows] using hw) hQp hp hF
  have bankH:∀ i,nextH (old i)=(CloseoutRowsBankPolynomial.entry gs p F Q w C (rawRows ms) out).heads i:=by
    intro i
    rw [BankFields.heads]
    by_cases h36:i=36
    · subst i;simp [nextH,BankExecution.changedHeads,old,CloseoutRowsBankFields.heads,CloseoutRowsBankFields.raised]
    · have n36:old i≠36:=by intro he;exact h36 (Fin.ext (congrArg (fun k : Fin 116=>k.val) he))
      simpa only [nextH,BankExecution.changedHeads,Function.update_of_ne (old_ne i 115 (by decide)),
        Function.update_of_ne n36,Function.update_of_ne (old_ne i 113 (by decide))] using hheads i
  have bankT:∀ i,nextA (old i)=(CloseoutRowsBankPolynomial.entry gs p F Q w C (rawRows ms) out).tapes i:=by
    intro i
    by_cases h36:i=36
    · subst i
      change BankExecution.changedTapes A C (rawRows ms).flatten ms.length 36=_
      rw [BankExecution.changedTapes,Function.update_of_ne (by decide : (36 : Fin 116)≠115),Function.update_self]
      exact (BankFields.table gs p F Q w C (rawRows ms) out).symm
    · have n36:old i≠36:=by intro he;exact h36 (Fin.ext (congrArg (fun k : Fin 116=>k.val) he))
      simpa only [nextA,BankExecution.changedTapes,Function.update_of_ne (old_ne i 115 (by decide)),
        Function.update_of_ne n36] using hother i h36
  obtain ⟨last,hl,_lf,ls,lh,lt,keep⟩:=RecoveryFocus.dock old old_injective
    CloseoutRowsBankPolynomial.machine _ nextH nextA _ bankH bankT base hbase
  obtain ⟨result,hr,rh,rt,rs⟩:=PCPOuter.exact_then first last hl
  refine ⟨result,hr,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rs,ls]
    exact Nat.add_le_add_left bs _
  · intro i;rw [rh,lh,bh]
  · intro i;rw [rt,lt,CloseoutRowsBankPorts.erased_store C _ base.final.tapes bo bc]
  · rw [rh,(keep 113 (fun i=>old_ne i 113 (by decide))).1]
    simp only [nextH,BankExecution.changedHeads,Function.update_of_ne (by decide : (113 : Fin 116)≠115),
      Function.update_of_ne (by decide : (113 : Fin 116)≠36),Function.update_self,pos]
  · rw [rt,(keep 113 (fun i=>old_ne i 113 (by decide))).2]
    simp only [nextA,BankExecution.changedTapes,Function.update_of_ne (by decide : (113 : Fin 116)≠115),
      Function.update_of_ne (by decide : (113 : Fin 116)≠36)]
  · rw [rh,(keep 115 (fun i=>old_ne i 115 (by decide))).1]
    exact Function.update_self _ _ _
  · rw [rt,(keep 115 (fun i=>old_ne i 115 (by decide))).2]
    exact Function.update_self _ _ _

end NearCubicWires.ExtIncidence.BankConsumer
