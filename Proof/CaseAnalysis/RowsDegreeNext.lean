import Proof.CaseAnalysis.RowsDegreeAdvance
import Proof.Amplification.RecoveryRowLookupTapes
import Proof.Hierarchy.HierarchyAllocation

/-! Between degree calls, physically reset the retained lookup bound and
advance both k templates and j. All native row heads, including the output
append cursor, survive. Only four existing small routines are composed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeNext
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameSlots : Fin 4→Fin 112 := ![39,40,103,105]
def nativeSlots : Fin 1→Fin 112 := fun _=>46
def templateSlots : Fin 1→Fin 112 := fun _=>108
def rawSlots : Fin 2→Fin 112 := ![110,103]
noncomputable def frameProgram := RecoveryFocus.machine frameSlots copyMachine
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlots RecoveryEraseWidth.incrementMachine
noncomputable def templateProgram := RecoveryFocus.machine templateSlots CloseoutRowsDegreeAdvance.templateMachine
noncomputable def rawProgram := RecoveryFocus.machine rawSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def first := Composition.machine frameProgram nativeProgram
noncomputable def second := Composition.machine first templateProgram
noncomputable def machine := Composition.machine second rawProgram

def zeroBound (A : Fin 112→List Bool) (w : ℕ) := Function.update A 40 (frame (SignedSortKey.binary w 0))
def nextNative (A : Fin 112→List Bool) (k : ℕ) := Function.update A 46 (CompareMachine.word (k+1))
def nextTemplate (A : Fin 112→List Bool) (k : ℕ) := Function.update A 108 (CompareMachine.word (k+1))
def nextRaw (A : Fin 112→List Bool) (j : ℕ) := Function.update A 110 (List.replicate (j+1) true)
def output (A : Fin 112→List Bool) (w k j : ℕ) := nextRaw (nextTemplate (nextNative (zeroBound A w) k) k) j
def budget (w k j : ℕ) := 8*w+4*k+2*j+23

theorem bound_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (w b C : ℕ)
    (h0 : A 39=frame (SignedSortKey.binary w 0)) (h1 : A 40=frame (SignedSortKey.binary w b))
    (h2 : A 103=List.replicate C false) (h3 : A 105=List.replicate (C+1) false)
    (hH : ∀ i,H (frameSlots i)=0) (hc : 4*w+3≤C) :
    ∃ r,runFrom frameProgram (8*w+8) ⟨frameProgram.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=zeroBound A w ∧ r.steps=8*w+8 := by
  have hb : (frame (SignedSortKey.binary w b)).length≤2*(SignedSortKey.binary w 0).length+1 := by
    simp only [frame_length,SignedSortKey.binary_length]
    exact le_rfl
  have h := copy_ready (SignedSortKey.binary w 0) (frame (SignedSortKey.binary w b)) C (C+1) hb
  simp only [SignedSortKey.binary_length,max_eq_left (show 2*w+1≤C by omega),
    max_eq_left (show 4*w+3≤C+1 by omega)] at h
  obtain ⟨r,hr,rh,rt,rs⟩ := h.focus_at frameSlots (by decide) H A
    (by intro i; fin_cases i; exact h0; exact h1; exact h2; exact h3) hH
  have he : install frameSlots A
      ![frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w 0),
        List.replicate C false,List.replicate (C+1) false]=zeroBound A w := by
    apply HierarchyAllocation.install_eq frameSlots (by decide)
    · intro i
      fin_cases i <;> simp [zeroBound,frameSlots,h0,h2,h3]
    · intro i hi
      exact Function.update_of_ne (Ne.symm (hi 1)) _ _
  exact ⟨r,hr,rh,rt.trans he,rs⟩

theorem native_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (k : ℕ)
    (hA : A 46=CompareMachine.word k) (hH : H 46=1) :
    ∃ r,runFrom nativeProgram (2*k+2) ⟨nativeProgram.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=nextNative A k ∧ r.steps=2*k+2 := by
  obtain ⟨base,hb,hf,hs⟩ := RecoveryEraseWidth.increment_run k
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩ := RecoveryFocus.dock nativeSlots (by decide)
    RecoveryEraseWidth.incrementMachine _ H A _ (by intro i; exact hH) (by intro i; exact hA) base hb
  refine ⟨r,hr,?_,?_,rs.trans hs⟩
  · funext i
    by_cases hi : i=46
    · subst i
      change r.final.heads (nativeSlots 0)=H 46
      rw [rh,hf,hH]
      rfl
    · exact (keep i (by intro j; exact Ne.symm hi)).1
  · funext i
    by_cases hi : i=46
    · subst i
      change r.final.tapes (nativeSlots 0)=_
      rw [rt,hf]
      simp only [nextNative,Function.update_self]
      rfl
    · rw [(keep i (by intro j; exact Ne.symm hi)).2]
      exact (Function.update_of_ne hi _ _).symm

theorem template_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (k : ℕ)
    (hA : A 108=CompareMachine.word k) (hH : H 108=0) :
    ∃ r,runFrom templateProgram (2*k+6) ⟨templateProgram.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=nextTemplate A k ∧ r.steps=2*k+6 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := (CloseoutRowsDegreeAdvance.template_ready k).focus_at
    templateSlots (by decide) H A (by intro i; exact hA) (by intro i; exact hH)
  have he : install templateSlots A (fun _=>CompareMachine.word (k+1))=nextTemplate A k := by
    apply HierarchyAllocation.install_eq templateSlots (by decide)
    · intro i
      exact Function.update_self _ _ _
    · intro i hi
      exact Function.update_of_ne (Ne.symm (hi 0)) _ _
  exact ⟨r,hr,rh,rt.trans he,rs⟩

theorem raw_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (j C : ℕ)
    (hA : A 110=List.replicate j true) (hl : A 103=List.replicate C false)
    (hH : H 110=0) (hL : H 103=0) (hc : j+1≤C) :
    ∃ r,runFrom rawProgram (2*j+4) ⟨rawProgram.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=nextRaw A j ∧ r.steps=2*j+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := (RepairSource.RecoveryTseitinRawIncrement.increment_ready j C hc).focus_at
    rawSlots (by decide) H A (by intro i; fin_cases i; exact hA; exact hl)
    (by intro i; fin_cases i; exact hH; exact hL)
  have he : install rawSlots A ![List.replicate (j+1) true,List.replicate C false]=nextRaw A j := by
    apply HierarchyAllocation.install_eq rawSlots (by decide)
    · intro i
      fin_cases i <;> simp [nextRaw,rawSlots,hl]
    · intro i hi
      exact Function.update_of_ne (Ne.symm (hi 0)) _ _
  exact ⟨r,hr,rh,rt.trans he,rs⟩

theorem next_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (w b k j C : ℕ)
    (h0 : A 39=frame (SignedSortKey.binary w 0)) (h1 : A 40=frame (SignedSortKey.binary w b))
    (hn : A 46=CompareMachine.word k) (ht : A 108=CompareMachine.word k)
    (hj : A 110=List.replicate j true)
    (h2 : A 103=List.replicate C false) (h3 : A 105=List.replicate (C+1) false)
    (hH : ∀ i,H (frameSlots i)=0) (hN : H 46=1) (hT : H 108=0) (hJ : H 110=0)
    (hc : 4*w+3≤C) (hC : j+1≤C) :
    ∃ actual,runFrom machine (budget w k j) ⟨machine.start,H,A⟩=some actual ∧
      actual.final.heads=H ∧ actual.final.tapes=output A w k j ∧
      actual.steps≤budget w k j := by
  obtain ⟨a,ha,ah,atape,_⟩ := bound_run A H w b C h0 h1 h2 h3 hH hc
  obtain ⟨n,hnode,nh,nt,_⟩ := native_run (zeroBound A w) H k (by simpa [zeroBound] using hn) hN
  have hi : (⟨nativeProgram.start,H,zeroBound A w⟩ : Configuration 112 3)=
      Composition.restart a.final nativeProgram.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atape.symm
  rw [hi] at hnode
  have an := Composition.run_join frameProgram nativeProgram _ _ _ a n ha hnode
  obtain ⟨t,htnode,th,tt,_⟩ := template_run (nextNative (zeroBound A w) k) H k
    (by simpa [nextNative,zeroBound] using ht) hT
  have hit : (⟨templateProgram.start,H,nextNative (zeroBound A w) k⟩ : Configuration 112 7)=
      Composition.restart (Composition.joinedReceipt a n).final templateProgram.start := by
    apply configuration_ext
    · rfl
    · exact nh.symm
    · exact nt.symm
  rw [hit] at htnode
  have ant := Composition.run_join first templateProgram _ _ _ (Composition.joinedReceipt a n) t an htnode
  obtain ⟨last,hlast,lh,lt,_⟩ := raw_run (nextTemplate (nextNative (zeroBound A w) k) k) H j C
    (by simpa [nextTemplate,nextNative,zeroBound] using hj)
    (by simpa [nextTemplate,nextNative,zeroBound] using h2) hJ (hH 2) hC
  have hil : (⟨rawProgram.start,H,nextTemplate (nextNative (zeroBound A w) k) k⟩ : Configuration 112 4)=
      Composition.restart (Composition.joinedReceipt (Composition.joinedReceipt a n) t).final rawProgram.start := by
    apply configuration_ext
    · rfl
    · exact th.symm
    · exact tt.symm
  rw [hil] at hlast
  have whole := Composition.run_join second rawProgram _ _ _
    (Composition.joinedReceipt (Composition.joinedReceipt a n) t) last ant hlast
  have he : ((8*w+8)+1+(2*k+2))+1+(2*k+6)+1+(2*j+4)=budget w k j := by unfold budget; omega
  rw [he] at whole
  exact ⟨_,whole,lh,lt,runFrom_steps_le machine _ _ _ whole⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeNext
