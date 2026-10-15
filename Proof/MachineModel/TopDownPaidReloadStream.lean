import Proof.CaseAnalysis.RowsRawLoad
import Proof.MachineModel.Layout

/-! Fixed tape-order loading from a retained physical stream. Every frame is
read by the existing raw-field loader; targets reuse resident false backing. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReloadStream
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound RecoveryExecution

def heads (t pos : Nat) : Fin (t+2)→Nat := Fin.addCases (fun _ : Fin t=>0) ![pos,0]
def bank {t : Nat} (A : Fin t→List Bool) (source : List Bool) (S : Nat) : Fin (t+2)→List Bool :=
  Fin.addCases A ![source,List.replicate S false]
def slots {t : Nat} (i : Fin t) : Fin 3→Fin (t+2) := ![(0 : Fin 2).natAdd t,i.castAdd 2,(1 : Fin 2).natAdd t]
theorem injective {t : Nat} (i : Fin t) : Function.Injective (slots i) := by
  intro j k h
  have hi:=i.isLt
  have hv:=congrArg Fin.val h
  fin_cases j <;> fin_cases k <;> simp [slots] at hv ⊢ <;> omega
noncomputable def field {t : Nat} (i : Fin t) := RecoveryFocus.machine (slots i) CloseoutRowsRawLoad.machine

theorem field_run {t : Nat} (i : Fin t) (A : Fin t→List Bool) (pre word tail : List Bool) (S : Nat)
    (hi : A i=List.replicate S false) (hb : word.length≤S) :
    Step (field i) (3*word.length+2) (heads t pre.length) (bank A (pre++frame word++tail) S)
      (heads t (pre.length+(frame word).length))
      (bank (Function.update A i (ZeroPadding.pad S word)) (pre++frame word++tail) S) := by
  classical
  obtain ⟨r,hr,hf,_hs⟩:=CloseoutRowsRawLoad.field_run pre word tail
  have base : Step CloseoutRowsRawLoad.machine (3*word.length+2)
      ![pre.length,0,0] ![pre++frame word++tail,[],[]]
      ![pre.length+(frame word).length,0,0]
      ![pre++frame word++tail,word,List.replicate word.length false] := by
    apply Step.of_run hr
    · rw [hf]
      simp [CloseoutRowsRawLoad.reset,frame_length,Nat.add_assoc]
    · rw [hf]
      rfl
  have hp:=base.pad (![0,S,S] : Fin 3→Nat)
  have hin : (fun j=>ZeroPadding.pad (![0,S,S] j) (![pre++frame word++tail,[],[]] j))=
      (![pre++frame word++tail,List.replicate S false,List.replicate S false] : Fin 3→List Bool) := by
    funext j;fin_cases j <;> simp [ZeroPadding.pad]
  have hout : (fun j=>ZeroPadding.pad (![0,S,S] j)
      (![pre++frame word++tail,word,List.replicate word.length false] j))=
      (![pre++frame word++tail,ZeroPadding.pad S word,List.replicate S false] : Fin 3→List Bool) := by
    funext j;fin_cases j <;> simp [ZeroPadding.pad,Nat.add_sub_of_le hb]
  have localRun:=(hp.congr_in rfl hin).congr rfl hout
  have h:=localRun.dock (slots i) (injective i) (heads t pre.length)
    (bank A (pre++frame word++tail) S)
    (by intro j;fin_cases j <;> simp [heads,slots])
    (by intro j;fin_cases j <;> simp [bank,slots,hi])
  apply h.congr
  · funext j
    refine Fin.addCases (m:=t) (n:=2) (fun k=>?_) (fun k=>?_) j
    · by_cases hk : k=i
      · subst k
        simpa [slots,heads] using dockH_slot (slots i) (injective i) (heads t pre.length)
          (![pre.length+(frame word).length,0,0] : Fin 3→Nat) 1
      · rw [dockH_other _ _ _ _ (by
          intro z he;have hv:=congrArg Fin.val he;have hi:=k.isLt
          fin_cases z <;> dsimp [slots] at hv
          · omega
          · exact hk (Fin.ext hv.symm)
          · omega)]
        simp [heads]
    · fin_cases k
      · simpa [slots,heads] using dockH_slot (slots i) (injective i) (heads t pre.length)
          (![pre.length+(frame word).length,0,0] : Fin 3→Nat) 0
      · simpa [slots,heads] using dockH_slot (slots i) (injective i) (heads t pre.length)
          (![pre.length+(frame word).length,0,0] : Fin 3→Nat) 2
  · funext j
    refine Fin.addCases (m:=t) (n:=2) (fun k=>?_) (fun k=>?_) j
    · by_cases hk : k=i
      · subst k
        simpa [slots,bank] using install_slot (slots i) (injective i) (bank A (pre++frame word++tail) S)
          (![pre++frame word++tail,ZeroPadding.pad S word,List.replicate S false] : Fin 3→List Bool) 1
      · rw [install_other _ _ _ _ (by
          intro z he;have hv:=congrArg Fin.val he;have hi:=k.isLt
          fin_cases z <;> dsimp [slots] at hv
          · omega
          · exact hk (Fin.ext hv.symm)
          · omega)]
        simp [bank,hk]
    · fin_cases k
      · simpa [slots,bank] using install_slot (slots i) (injective i) (bank A (pre++frame word++tail) S)
          (![pre++frame word++tail,ZeroPadding.pad S word,List.replicate S false] : Fin 3→List Bool) 0
      · simpa [slots,bank] using install_slot (slots i) (injective i) (bank A (pre++frame word++tail) S)
          (![pre++frame word++tail,ZeroPadding.pad S word,List.replicate S false] : Fin 3→List Bool) 2

def states {t : Nat} : List (Fin t)→Nat
  | []=>1
  | _::xs=>4+states xs
def stop (t : Nat) : Machine (t+2) 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def machine {t : Nat} : (xs : List (Fin t))→Machine (t+2) (states xs)
  | []=>stop t
  | i::xs=>Composition.machine (field i) (machine xs)
def stream {t : Nat} (words : Fin t→List Bool) (xs : List (Fin t)) := xs.flatMap (fun i=>frame (words i))
def budget {t : Nat} (words : Fin t→List Bool) : List (Fin t)→Nat
  | []=>0
  | i::xs=>3*(words i).length+2+1+budget words xs
def loaded {t : Nat} (S : Nat) (words A : Fin t→List Bool) (xs : List (Fin t)) :=
  fun i=>if i∈xs then ZeroPadding.pad S (words i) else A i

theorem run {t : Nat} (words : Fin t→List Bool) (xs : List (Fin t)) (hn : xs.Nodup)
    (A : Fin t→List Bool) (pre tail : List Bool) (S : Nat)
    (ha : ∀ i∈xs,A i=List.replicate S false) (hb : ∀ i∈xs,(words i).length≤S) :
    Step (machine xs) (budget words xs) (heads t pre.length)
      (bank A (pre++stream words xs++tail) S)
      (heads t (pre.length+(stream words xs).length))
      (bank (loaded S words A xs) (pre++stream words xs++tail) S) := by
  classical
  induction xs generalizing A pre with
  | nil =>
    obtain ⟨r,hr,hf,hs⟩:=(Timed.refl (stop t)
      (⟨(stop t).start,heads t pre.length,bank A (pre++stream words []++tail) S⟩ : Configuration (t+2) 1)).run (by rfl)
    refine ⟨r,hr,?_,?_,hs.le⟩
    · rw [hf];simp [stream]
    · rw [hf]
      have he : loaded S words A []=A:=by funext i;simp [loaded]
      rw [he]
  | cons i xs ih =>
    have nd:=List.nodup_cons.mp hn
    have first:=field_run i A pre (words i) (stream words xs++tail) S
      (ha i (by simp)) (hb i (by simp))
    have rest:=ih nd.2 (Function.update A i (ZeroPadding.pad S (words i))) (pre++frame (words i))
      (by intro j hj;rw [Function.update_of_ne (by intro he;subst j;exact nd.1 hj)];exact ha j (by simp [hj]))
      (by intro j hj;exact hb j (by simp [hj]))
    have rest' : Step (machine xs) (budget words xs) (heads t (pre.length+(frame (words i)).length))
        (bank (Function.update A i (ZeroPadding.pad S (words i))) (pre++frame (words i)++(stream words xs++tail)) S)
        (heads t ((pre++frame (words i)).length+(stream words xs).length))
        (bank (loaded S words (Function.update A i (ZeroPadding.pad S (words i))) xs)
          ((pre++frame (words i))++stream words xs++tail) S) :=
      rest.congr_in (by simp [List.length_append]) (by simp [List.append_assoc])
    have joined:=first.seq rest'
    have hl : loaded S words (Function.update A i (ZeroPadding.pad S (words i))) xs=
        loaded S words A (i::xs) := by
      funext j
      by_cases hj : j∈xs
      · simp [loaded,hj]
      · by_cases he : j=i <;> simp [loaded,hj,he]
    simpa only [machine,states,budget,stream,List.flatMap_cons,List.length_append,List.append_assoc,
      Nat.add_assoc,hl] using joined

end NearCubicWires.P1TopDownPaidReloadStream
