import Proof.MachineModel.TopDownPaidReloadStream
import Proof.MachineModel.ClosureRawRowState
import Proof.CaseAnalysis.RowsProjectionReset

/-! A complete advancing-stream transaction around the existing row worker.
The fixed tape-order source contains cold entry words, never an answer.
The simultaneous final erase has one linear shared-capacity charge. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace NearCubicWires.P1TopDownPaidReusableBody
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound P1Closure
namespace Loader
open P1TopDownPaidReloadStream
end Loader

def heads (t pos : Nat) (out : List Bool) : Fin (t+1+2+4)→Nat :=
  Fin.addCases (RawRowJoin.heads t out) ![pos,0,0,0]
def bank {t : Nat} (A : Fin t→List Bool) (source : List Bool) (S R B : Nat) (out : List Bool) :
    Fin (t+1+2+4)→List Bool :=
  Fin.addCases (RawRowJoin.bank A R B out)
    ![source,List.replicate S false,List.replicate S true,List.replicate (S+1) false]
def loadSlots (t : Nat) : Fin (t+2)→Fin (t+1+2+4) :=
  Fin.addCases (fun i : Fin t=>(i.castAdd 1).castAdd 2 |>.castAdd 4)
    ![(0 : Fin 4).natAdd (t+1+2),(1 : Fin 4).natAdd (t+1+2)]
def eraseSlots (t : Nat) : Fin (t+1+1)→Fin (t+1+2+4) :=
  Fin.addCases (Fin.addCases (fun i : Fin t=>(i.castAdd 1).castAdd 2 |>.castAdd 4)
    (fun _ : Fin 1=>(2 : Fin 4).natAdd (t+1+2)))
    (fun _ : Fin 1=>(3 : Fin 4).natAdd (t+1+2))

theorem load_injective (t : Nat) : Function.Injective (loadSlots t) := by
  intro i j he
  have hv:=congrArg Fin.val he
  revert hv
  refine Fin.addCases (m:=t) (n:=2) (fun x=>?_) (fun x=>?_) i <;>
    refine Fin.addCases (m:=t) (n:=2) (fun y=>?_) (fun y=>?_) j
  · intro h;simp only [loadSlots,Fin.addCases_left,Fin.val_castAdd] at h;exact Fin.ext h
  · intro h;have hx:=x.isLt;fin_cases y <;> simp [loadSlots] at h <;> omega
  · intro h;have hy:=y.isLt;fin_cases x <;> simp [loadSlots] at h <;> omega
  · intro h;fin_cases x <;> fin_cases y <;> first |rfl |(simp [loadSlots] at h)

theorem erase_injective (t : Nat) : Function.Injective (eraseSlots t) := by
  intro i j he
  have hv:=congrArg Fin.val he
  have eqv (k : Fin (t+1+1)) : (eraseSlots t k).val=if k.val<t then k.val else k.val+5 := by
    refine Fin.addCases (m:=t+1) (n:=1) (fun l=>?_) (fun l=>?_) k
    · refine Fin.addCases (m:=t) (n:=1) (fun l=>?_) (fun l=>?_) l
      · simp [eraseSlots,l.isLt]
      · simp [eraseSlots,Fin.eq_zero l]
    · simp [eraseSlots,Fin.eq_zero l]
  rw [eqv,eqv] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

noncomputable def load (t : Nat) := RecoveryFocus.machine (loadSlots t)
  (P1TopDownPaidReloadStream.machine (List.finRange t))
noncomputable def erase (t : Nat) := RecoveryFocus.machine (eraseSlots t) (RecoveryScratchErase.resetMachine t)
noncomputable def machine {t st : Nat} (worker : Machine (t+1+2) st) :=
  Composition.machine (Composition.machine (load t) (TapeEmbedding.machine 4 worker)) (erase t)
def word {t : Nat} (A : Fin t→List Bool) := P1TopDownPaidReloadStream.stream A (List.finRange t)
def loadBudget {t : Nat} (A : Fin t→List Bool) := P1TopDownPaidReloadStream.budget A (List.finRange t)
def budget {t : Nat} (A : Fin t→List Bool) (n S : Nat) := loadBudget A+1+n+1+(2*S+4)

theorem load_run {t : Nat} (A : Fin t→List Bool) (pre tail out : List Bool) (S R B : Nat)
    (hA : ∀ i,(A i).length≤S) :
    Step (load t) (loadBudget A) (heads t pre.length out)
      (bank (fun _ : Fin t=>List.replicate S false) (pre++word A++tail) S R B out)
      (heads t (pre.length+(word A).length) out)
      (bank (fun i=>ZeroPadding.pad S (A i)) (pre++word A++tail) S R B out) := by
  have h:=P1TopDownPaidReloadStream.run A (List.finRange t) (List.nodup_finRange t)
    (fun _=>List.replicate S false) pre tail S (by intros;rfl) (by intro i _;exact hA i)
  have hl : P1TopDownPaidReloadStream.loaded S A (fun _ : Fin t=>List.replicate S false)
      (List.finRange t)=(fun i=>ZeroPadding.pad S (A i)) := by
    funext i;simp [P1TopDownPaidReloadStream.loaded]
  rw [hl] at h
  have h':=h.dock (loadSlots t) (load_injective t) (heads t pre.length out)
    (bank (fun _ : Fin t=>List.replicate S false) (pre++word A++tail) S R B out)
    (by intro i;refine Fin.addCases (m:=t) (n:=2) (fun j=>?_) (fun j=>?_) i
        · simp [heads,bank,loadSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]
        · fin_cases j <;> simp [heads,bank,loadSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank])
    (by intro i;refine Fin.addCases (m:=t) (n:=2) (fun j=>?_) (fun j=>?_) i
        · simp [heads,bank,loadSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]
        · fin_cases j <;> simp [heads,bank,loadSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank,word])
  apply h'.congr
  · funext i
    by_cases hit : ∃ j,loadSlots t j=i
    · obtain ⟨j,rfl⟩:=hit
      rw [dockH_slot _ (load_injective t)]
      refine Fin.addCases (m:=t) (n:=2) (fun k=>?_) (fun k=>?_) j
      · simp [loadSlots,heads,RawRowJoin.heads,P1TopDownPaidReloadStream.heads]
      · fin_cases k <;> simp [loadSlots,heads,P1TopDownPaidReloadStream.heads,word]
    · rw [dockH_other _ _ _ _ (by simpa only [not_exists] using hit)]
      revert hit
      refine Fin.addCases (m:=t+1+2) (n:=4) (fun j _=>by simp [heads]) (fun j hj=>?_) i
      fin_cases j
      · exact False.elim (hj ⟨(0 : Fin 2).natAdd t,by simp [loadSlots]⟩)
      all_goals simp [heads]
  · funext i
    by_cases hit : ∃ j,loadSlots t j=i
    · obtain ⟨j,rfl⟩:=hit
      rw [install_slot _ (load_injective t)]
      refine Fin.addCases (m:=t) (n:=2) (fun k=>?_) (fun k=>?_) j
      · simp [bank,loadSlots,RawRowJoin.bank,P1TopDownPaidReloadStream.bank]
      · fin_cases k <;> simp [bank,loadSlots,P1TopDownPaidReloadStream.bank,word]
    · rw [install_other _ _ _ _ (by simpa only [not_exists] using hit)]
      revert hit
      refine Fin.addCases (m:=t+1+2) (n:=4) (fun j=>?_) (fun j _=>by simp [bank]) i
      refine Fin.addCases (m:=t+1) (n:=2) (fun j=>?_) (fun j _=>by simp [bank,RawRowJoin.bank]) j
      refine Fin.addCases (m:=t) (n:=1) (fun j hj=>?_) (fun j _=>by simp [bank,RawRowJoin.bank]) j
      exact False.elim (hj ⟨j.castAdd 2,by simp [loadSlots]⟩)

theorem erase_run {t : Nat} (A : Fin t→List Bool) (source out : List Bool) (pos S R B : Nat)
    (hA : ∀ i,(A i).length≤S) :
    Step (erase t) (2*S+4) (heads t pos out) (bank A source S R B out)
      (heads t pos out) (bank (fun _ : Fin t=>List.replicate S false) source S R B out) := by
  have base:=Step.of_ready (RecoveryScratchErase.erase_ready S (S+1) A hA)
  have h:=base.dock (eraseSlots t) (erase_injective t) (heads t pos out) (bank A source S R B out)
    (by intro i;refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) i
        refine Fin.addCases (m:=t) (n:=1) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) j)
    (by intro i;refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) i
        refine Fin.addCases (m:=t) (n:=1) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) j)
  apply h.congr (dockH_existing _ _ _ (by
    intro i;refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) i
    refine Fin.addCases (m:=t) (n:=1) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) (fun j=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) j))
  funext i
  by_cases hit : ∃ j,eraseSlots t j=i
  · obtain ⟨j,rfl⟩:=hit
    rw [install_slot _ (erase_injective t)]
    refine Fin.addCases (m:=t+1) (n:=1) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=t) (n:=1) (fun k=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) (fun k=>by simp [heads,bank,loadSlots,eraseSlots,RawRowJoin.heads,RawRowJoin.bank,P1TopDownPaidReloadStream.heads,P1TopDownPaidReloadStream.bank]) k
    · simp [bank,eraseSlots]
  · rw [install_other _ _ _ _ (by simpa only [not_exists] using hit)]
    revert hit
    refine Fin.addCases (m:=t+1+2) (n:=4) (fun j=>?_) (fun j _=>by simp [bank]) i
    refine Fin.addCases (m:=t+1) (n:=2) (fun j=>?_) (fun j _=>by simp [bank,RawRowJoin.bank]) j
    refine Fin.addCases (m:=t) (n:=1) (fun j hj=>?_) (fun j _=>by simp [bank,RawRowJoin.bank]) j
    exact False.elim (hj ⟨(j.castAdd 1).castAdd 1,by simp [eraseSlots]⟩)

theorem pad_twice (S B : Nat) (w : List Bool) (h : B≤S) :
    ZeroPadding.pad S (ZeroPadding.pad B w)=ZeroPadding.pad S w := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc,←List.replicate_add]
  congr 2
  omega

theorem run {t st : Nat} (worker : Machine (t+1+2) st) (port : Fin t)
    (A Z : Fin t→List Bool) (pre tail out next : List Bool) (n S R B : Nat)
    (hA : ∀ i,(A i).length≤S) (hn : n+1≤S) (hB : B≤S)
    (hw : Step worker n (RawRowJoin.heads t out)
      (RawRowJoin.bank (RawRowJoin.padded port B A) R B out)
      (RawRowJoin.heads t next) (RawRowJoin.bank Z R B next)) :
    Step (machine worker) (budget A n S) (heads t pre.length out)
      (bank (fun _ : Fin t=>List.replicate S false) (pre++word A++tail) S R B out)
      (heads t (pre.length+(word A).length) next)
      (bank (fun _ : Fin t=>List.replicate S false) (pre++word A++tail) S R B next) := by
  have support : ∀ i,(Z i).length≤S := by
    obtain ⟨r,hr,hh,ht,hs⟩:=hw
    intro i
    have h:=CloseoutRowsProjectionReset.scratch_support worker n S _ r hr
      ((i.castAdd 1).castAdd 2) (by simp [RawRowJoin.heads]) (by
        simp only [RawRowJoin.bank,Fin.addCases_left,RawRowJoin.padded]
        rw [ZeroPadding.pad_length]
        exact Nat.max_le.mpr ⟨by unfold RawRowJoin.caps;split_ifs <;> omega,hA i⟩) (by omega)
    rw [ht] at h
    simpa only [RawRowJoin.bank,Fin.addCases_left] using h
  let caps : Fin (t+1+2)→Nat := Fin.addCases (Fin.addCases (fun _ : Fin t=>S) (fun _ : Fin 1=>0)) (fun _ : Fin 2=>0)
  have wp:=hw.pad caps
  have hi : (fun i=>ZeroPadding.pad (caps i) (RawRowJoin.bank (RawRowJoin.padded port B A) R B out i))=
      RawRowJoin.bank (fun i=>ZeroPadding.pad S (A i)) R B out := by
    funext i
    refine Fin.addCases (m:=t+1) (n:=2) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) j
      · simp only [caps,RawRowJoin.bank,Fin.addCases_left,RawRowJoin.padded]
        exact pad_twice S _ _ (by unfold RawRowJoin.caps;split_ifs <;> omega)
      · simp [caps,RawRowJoin.bank]
    · simp [caps,RawRowJoin.bank]
  have hz : (fun i=>ZeroPadding.pad (caps i) (RawRowJoin.bank Z R B next i))=
      RawRowJoin.bank (fun i=>ZeroPadding.pad S (Z i)) R B next := by
    funext i
    refine Fin.addCases (m:=t+1) (n:=2) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) j <;> simp [caps,RawRowJoin.bank]
    · simp [caps,RawRowJoin.bank]
  have middle:=((wp.congr_in rfl hi).congr rfl hz).embed
    (![pre.length+(word A).length,0,0,0] : Fin 4→Nat)
    (![pre++word A++tail,List.replicate S false,List.replicate S true,List.replicate (S+1) false] : Fin 4→List Bool)
  have middle' : Step (TapeEmbedding.machine 4 worker) n
      (heads t (pre.length+(word A).length) out)
      (bank (fun i=>ZeroPadding.pad S (A i)) (pre++word A++tail) S R B out)
      (heads t (pre.length+(word A).length) next)
      (bank (fun i=>ZeroPadding.pad S (Z i)) (pre++word A++tail) S R B next) := middle
  have last:=erase_run (fun i=>ZeroPadding.pad S (Z i)) (pre++word A++tail) next
    (pre.length+(word A).length) S R B (by intro i;rw [ZeroPadding.pad_length];exact Nat.max_le.mpr ⟨le_rfl,support i⟩)
  exact ((load_run A pre tail out S R B hA).seq middle').seq last

theorem budget_le {t : Nat} (A : Fin t→List Bool) (n S : Nat)
    (hA : ∀ i,(A i).length≤S) (hn : n+1≤S) :
    budget A n S≤(3*t+6)*(S+1) := by
  have aux (xs : List (Fin t)) : P1TopDownPaidReloadStream.budget A xs≤3*xs.length*(S+1) := by
    induction xs with
    | nil=>simp [P1TopDownPaidReloadStream.budget]
    | cons i xs ih=>
      simp only [P1TopDownPaidReloadStream.budget,List.length_cons]
      have hi:=hA i
      nlinarith
  have h:=aux (List.finRange t)
  simp only [List.length_finRange] at h
  unfold budget loadBudget
  nlinarith

end NearCubicWires.P1TopDownPaidReusableBody
