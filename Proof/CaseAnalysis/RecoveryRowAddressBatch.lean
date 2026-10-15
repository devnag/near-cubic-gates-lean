import Proof.CaseAnalysis.RecoveryRowAddressReady
import Proof.CaseAnalysis.RecoveryRowProjection

/-! Produce the actual normalized query addresses and hand their raw bits
to the original graph consumer. The projector bank stays reusable. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddressBatch
open LocalBitMultitape RepairSource SourceInterfaces RepairSource.ProjectionNormalization
open RecoveryRootRound RecoveryBoundedRowProjection
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (A : Fin 37→List Bool) (out : List Bool) : Fin 38→List Bool:=
  Fin.addCases (m:=37) (n:=1) (motive:=fun _=>List Bool) A (fun _=>out)
theorem data_old (A : Fin 37→List Bool) (out : List Bool) (j : Fin 37) :
    data A out (j.castAdd 1)=A j:=Fin.addCases_left j
def slots : Fin 4→Fin 38:=![31,37,35,36]
noncomputable def first:=ClockJoin.lifted (e:=1) (Equiv.refl (Fin 38)) RecoveryProjectionRowsRewind.machine
noncomputable def last:=RecoveryFocus.machine slots RecoveryBoundedRowAddress.readyMachine
noncomputable def machine:=Composition.machine first last
def budget (R Q : ℕ) (fields : List (List Bool)):=
  RecoveryProjectionRowsRewind.budget R Q+1+RecoveryBoundedRowAddress.readyBudget fields

theorem dock_output (A : Fin 38→List Bool) (source out driver log : List Bool)
    (hs : A 31=source) (hd : A 35=driver) (hl : A 36=log) :
    install slots A ![source,out,driver,log]=Function.update A 37 out := by
  funext i
  by_cases h : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩:=h
    rw [install_slot slots (by decide)]
    fin_cases j
    · change source=Function.update A 37 out 31
      rw [Function.update_of_ne (by decide : (31 : Fin 38)≠37)]
      exact hs.symm
    · exact (Function.update_self 37 out A).symm
    · change driver=Function.update A 37 out 35
      rw [Function.update_of_ne (by decide : (35 : Fin 38)≠37)]
      exact hd.symm
    · change log=Function.update A 37 out 36
      rw [Function.update_of_ne (by decide : (36 : Fin 38)≠37)]
      exact hl.symm
  · rw [install_other _ _ _ _ (by intro j hj;exact h ⟨j,hj⟩)]
    exact (Function.update_of_ne (fun he=>h ⟨1,he.symm⟩) _ _).symm

theorem raw_ready (fields : List (List Bool)) (B : ℕ) (A : Fin 38→List Bool)
    (hB : RecoveryBoundedRowAddress.budget fields+2≤B)
    (hs : A 31=ZeroPadding.pad B (FieldList.stream fields))
    (ho : A 37=List.replicate B false)
    (hd : A 35=VerifierDecoding.CompareMachine.word fields.length)
    (hl : A 36=List.replicate B false) :
    ClockJoin.ReadyRun last (RecoveryBoundedRowAddress.readyBudget fields) A
      (Function.update A 37 (ZeroPadding.pad B fields.flatten)) := by
  let tail:=List.replicate (B-(FieldList.stream fields).length) false
  have base:=RecoveryBoundedRowAddress.address_ready fields tail B hB
  have padded:=PCPPairReusable.padded_ready _ _ _ base (![0,B,0,0] : Fin 4→ℕ)
  have inputEq : (fun i=>ZeroPadding.pad ((![0,B,0,0] : Fin 4→ℕ) i)
      ((Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) (RecoveryBoundedRowAddress.rawInput fields tail) (fun _=>List.replicate B false)) i))=
      (![ZeroPadding.pad B (FieldList.stream fields),List.replicate B false,
        VerifierDecoding.CompareMachine.word fields.length,List.replicate B false] : Fin 4→List Bool) := by
    funext i;fin_cases i
    · change ZeroPadding.pad 0 (FieldList.stream fields++tail)=_
      rw [ZeroPadding.pad_zero]
      rfl
    · change ZeroPadding.pad B []=List.replicate B false
      simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
  have outputEq : (fun i=>ZeroPadding.pad ((![0,B,0,0] : Fin 4→ℕ) i)
      ((Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) (RecoveryBoundedRowAddress.rawOutput fields tail) (fun _=>List.replicate B false)) i))=
      (![ZeroPadding.pad B (FieldList.stream fields),ZeroPadding.pad B fields.flatten,
        VerifierDecoding.CompareMachine.word fields.length,List.replicate B false] : Fin 4→List Bool) := by
    funext i;fin_cases i
    · change ZeroPadding.pad 0 (FieldList.stream fields++tail)=_
      rw [ZeroPadding.pad_zero]
      rfl
    · rfl
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
  rw [inputEq,outputEq] at padded
  have h:=padded.focus slots (by decide) A (by intro i;fin_cases i;exact hs;exact ho;exact hd;exact hl)
  rw [dock_output A _ _ _ _ hs hd hl] at h
  exact h

theorem data_update (A : Fin 37→List Bool) (before after : List Bool) :
    Function.update (data A before) 37 after=data A after := by
  funext i
  refine Fin.addCases (m:=37) (n:=1) (fun j=>?_) (fun j=>?_) i
  · have hn : (j.castAdd 1 : Fin 38)≠37:=by intro h;have hv:=congrArg Fin.val h;have hj:=j.isLt;change j.val=37 at hv;omega
    rw [Function.update_of_ne hn]
    rw [data_old,data_old]
  · fin_cases j
    exact Function.update_self _ _ _

theorem batch_ready (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) (B : ℕ)
    (hp : RecoveryProjectionRowsRewind.batchBudget R Q+2≤B)
    (ha : RecoveryBoundedRowAddress.budget (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)+2≤B) :
    let fields:=RecoveryProjectionRows.addressFields p R Q hr hq x randomness
    ClockJoin.ReadyRun machine (budget R Q fields)
      (data (bank p R Q randomness B) (List.replicate B false))
      (data (Function.update (bank p R Q randomness B) 31 (ZeroPadding.pad B (FieldList.stream fields)))
        (ZeroPadding.pad B fields.flatten)) := by
  let fields:=RecoveryProjectionRows.addressFields p R Q hr hq x randomness
  let middle:=data (Function.update (bank p R Q randomness B) 31 (ZeroPadding.pad B (FieldList.stream fields))) (List.replicate B false)
  have start:=RecoveryBoundedRowProjection.batch_ready p R Q hr hq x randomness B hp
  have a:=ClockJoin.lift (e:=1) (Equiv.refl (Fin 38)) _ _ _ _ (fun _=>List.replicate B false) start
  change ClockJoin.ReadyRun first _ (data (bank p R Q randomness B) (List.replicate B false)) middle at a
  have b:=raw_ready fields B middle ha
    (by change data _ _ ((31 : Fin 37).castAdd 1)=_
        rw [data_old]
        exact Function.update_self _ _ _)
    (by rfl)
    (by change data _ _ ((35 : Fin 37).castAdd 1)=_
        rw [data_old]
        rw [Function.update_of_ne (by decide)]
        change ZeroPadding.pad 0 (VerifierDecoding.CompareMachine.word Q)=_
        rw [ZeroPadding.pad_zero]
        congr 1
        simp only [fields,RecoveryProjectionRows.addressFields,List.length_ofFn])
    (by change data _ _ ((36 : Fin 37).castAdd 1)=_
        rw [data_old]
        rw [Function.update_of_ne (by decide)]
        exact ZeroPadding.pad_zero _)
  have full:=ClockJoin.join first last _ _ _ _ _ a b
  rw [data_update] at full
  exact full

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddressBatch
