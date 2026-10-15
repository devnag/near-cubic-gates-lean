import Proof.CaseAnalysis.RowsCircuitPrefixSupport

/-! Three actual small resource counters are copied into the already
allocated arithmetic workspace. The native output, policy caps and all
source counters remain unchanged; each bounded copy is charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources : Fin 3 → Fin 1703 := ![1689,622,1690]
def targets : Fin 3 → Fin 1703 := ![639,640,660]
def slots (j : Fin 3) : Fin 4 → Fin 1703 := ![sources j,targets j,1694,1695]
noncomputable def copy (j : Fin 3):=RecoveryFocus.machine (slots j) RecoveryBoundedTapeCopy.machine
noncomputable def first:=Composition.machine (copy 0) (copy 1)
noncomputable def machine:=Composition.machine first (copy 2)
def bank (C : ℕ) (values : Fin 3 → ℕ) (A : Fin 1703 → List Bool) (done : ℕ) (i : Fin 1703):=
  if i=639 ∧ 0<done then ZeroPadding.pad C (List.replicate (values 0) true)
  else if i=640 ∧ 1<done then ZeroPadding.pad C (List.replicate (values 1) true)
  else if i=660 ∧ 2<done then ZeroPadding.pad C (List.replicate (values 2) true) else A i

theorem bank_zero (C : ℕ) (values : Fin 3 → ℕ) (A : Fin 1703 → List Bool) : bank C values A 0=A:=by
  funext i;simp [bank]

theorem bank_next (C : ℕ) (values : Fin 3 → ℕ) (A : Fin 1703 → List Bool) (j : Fin 3) :
    bank C values A (j.val+1)=Function.update (bank C values A j.val) (targets j)
      (ZeroPadding.pad C (List.replicate (values j) true)):=by
  fin_cases j <;> funext i
  all_goals by_cases h0:i=639 <;> by_cases h1:i=640 <;> by_cases h2:i=660
  all_goals simp_all [bank,targets]

theorem copy_run (C : ℕ) (values : Fin 3 → ℕ) (A : Fin 1703 → List Bool) (H : Fin 1703 → ℕ)
    (j : Fin 3) (hb : values j ≤ C)
    (hh : ∀ i,H (slots j i)=0)
    (hs : ∀ i,A (sources i)=List.replicate (values i) true)
    (ht : ∀ i,A (targets i)=List.replicate C false)
    (hd : A 1694=List.replicate C true) (hl : A 1695=List.replicate (C+1) false) :
    PCPOuter.Exact (copy j) (2*C+4) H (bank C values A j.val) H (bank C values A (j.val+1)):=by
  have inj:Function.Injective (slots j):=by fin_cases j <;> decide
  obtain ⟨r,hr,rh,rt,rs⟩:=CloseoutRowsCircuitCopy.copy_focus (slots j) inj C
    (List.replicate (values j) true) (by simpa only [List.length_replicate] using hb)
    H (bank C values A j.val) hh (by
      intro i
      fin_cases j <;> fin_cases i
      all_goals simp [bank,slots,sources,targets,CloseoutRowsMetadataCopy.input]
      all_goals first | exact hs 0 | exact hs 1 | exact hs 2 | exact ht 0 | exact ht 1 | exact ht 2 | exact hd | exact hl)

  exact ⟨r,hr,rh,rt.trans (bank_next C values A j).symm,rs⟩

theorem copies_run (C : ℕ) (values : Fin 3 → ℕ) (A : Fin 1703 → List Bool) (H : Fin 1703 → ℕ)
    (hb : ∀ j,values j ≤ C) (hh : ∀ j i,H (slots j i)=0)
    (hs : ∀ i,A (sources i)=List.replicate (values i) true)
    (ht : ∀ i,A (targets i)=List.replicate C false)
    (hd : A 1694=List.replicate C true) (hl : A 1695=List.replicate (C+1) false) :
    PCPOuter.Exact machine (6*C+14) H A H (bank C values A 3):=by
  have h0:=copy_run C values A H 0 (hb 0) (hh 0) hs ht hd hl
  have h1:=copy_run C values A H 1 (hb 1) (hh 1) hs ht hd hl
  have h2:=copy_run C values A H 2 (hb 2) (hh 2) hs ht hd hl
  have all:=PCPOuter.exact_join (PCPOuter.exact_join h0 h1) h2
  change PCPOuter.Exact machine (((2*C+4)+1+(2*C+4))+1+(2*C+4))
    H (bank C values A 0) H (bank C values A 3) at all
  rw [bank_zero] at all
  have time:((2*C+4)+1+(2*C+4))+1+(2*C+4)=6*C+14:=by omega
  rw [time] at all
  exact all

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies
