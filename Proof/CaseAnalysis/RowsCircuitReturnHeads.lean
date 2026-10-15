import Proof.CaseAnalysis.RowsCircuitCapCompare
import Proof.CaseAnalysis.RowsCircuitCounterReturn

/-! Return the five private traversal/resource cursors using the same
paid C driver. Native output and the actual source-domain cursor stay at
their documented positions; the reusable C+1 log is unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1703) : Fin 3 → Fin 1703 := ![i,1694,1695]
noncomputable def worker (i : Fin 1703):=RecoveryFocus.machine (slots i) CompetitorRecordRewind.machine
noncomputable def first:=Composition.machine (worker 1689) (worker 1690)
noncomputable def second:=Composition.machine first (worker 297)
noncomputable def third:=Composition.machine second (worker 1692)
noncomputable def machine:=Composition.machine third (worker 624)
def h1 (H : Fin 1703 → ℕ):=Function.update H 1689 0
def h2 (H : Fin 1703 → ℕ):=Function.update (h1 H) 1690 0
def h3 (H : Fin 1703 → ℕ):=Function.update (h2 H) 297 0
def h4 (H : Fin 1703 → ℕ):=Function.update (h3 H) 1692 0
def output (H : Fin 1703 → ℕ):=Function.update (h4 H) 624 0

theorem one_run (i : Fin 1703) (hi : i≠1694 ∧ i≠1695) (C : ℕ)
    (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool) (hp : H i ≤ C)
    (hdh : H 1694=0) (hlh : H 1695=0)
    (hd : A 1694=List.replicate C true) (hl : A 1695=List.replicate (C+1) false) :
    PCPOuter.Exact (worker i) (2*C+2) H A (Function.update H i 0) A:=by
  have inj:Function.Injective (slots i):=by
    intro j k h;fin_cases j <;> fin_cases k <;> simp_all [slots]
  obtain ⟨base,hb,bh,bt,bs⟩:=CloseoutRowsCircuitCounterReturn.return_run C (H i) (A i) hp
  have heads:∀ j,H (slots i j)=(![H i,0,0] : Fin 3 → ℕ) j:=by
    intro j;fin_cases j
    · rfl
    · exact hdh
    · exact hlh
  have tapes:∀ j,A (slots i j)=CloseoutRowsCircuitCounterReturn.input C (A i) j:=by
    intro j;fin_cases j
    · rfl
    · exact hd
    · exact hl
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock (slots i) inj CompetitorRecordRewind.machine
    _ H A _ heads tapes base hb
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · apply Function.eq_update_iff.mpr
    refine ⟨(rh 0).trans (congrFun bh 0),?_⟩
    intro j hj
    by_cases hs:∃ k,slots i k=j
    · obtain ⟨k,rfl⟩:=hs
      rw [rh,bh,heads]
      fin_cases k
      · exact False.elim (hj rfl)
      · rfl
      · rfl
    · exact (keep j (by simpa only [not_exists] using hs)).1
  · funext j
    by_cases hs:∃ k,slots i k=j
    · obtain ⟨k,rfl⟩:=hs
      rw [rt,bt]
      exact (tapes k).symm
    · exact (keep j (by simpa only [not_exists] using hs)).2

theorem return_run (C : ℕ) (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hp : H 1689 ≤ C ∧ H 1690 ≤ C ∧ H 297 ≤ C ∧ H 1692 ≤ C ∧ H 624 ≤ C)
    (hdh : H 1694=0) (hlh : H 1695=0)
    (hd : A 1694=List.replicate C true) (hl : A 1695=List.replicate (C+1) false) :
    PCPOuter.Exact machine (10*C+14) H A (output H) A:=by
  have r0:=one_run 1689 (by decide) C H A hp.1 hdh hlh hd hl
  have r1:=one_run 1690 (by decide) C (h1 H) A
    (by simpa only [h1,Function.update_of_ne (by decide : (1690 : Fin 1703)≠1689)] using hp.2.1)
    (by simpa only [h1,Function.update_of_ne (by decide : (1694 : Fin 1703)≠1689)] using hdh)
    (by simpa only [h1,Function.update_of_ne (by decide : (1695 : Fin 1703)≠1689)] using hlh) hd hl
  have r2:=one_run 297 (by decide) C (h2 H) A
    (by simpa [h2,h1] using hp.2.2.1) (by simpa [h2,h1] using hdh) (by simpa [h2,h1] using hlh) hd hl
  have r3:=one_run 1692 (by decide) C (h3 H) A
    (by simpa [h3,h2,h1] using hp.2.2.2.1) (by simpa [h3,h2,h1] using hdh) (by simpa [h3,h2,h1] using hlh) hd hl
  have r4:=one_run 624 (by decide) C (h4 H) A
    (by simpa [h4,h3,h2,h1] using hp.2.2.2.2) (by simpa [h4,h3,h2,h1] using hdh)
    (by simpa [h4,h3,h2,h1] using hlh) hd hl
  have all:=PCPOuter.exact_join (PCPOuter.exact_join (PCPOuter.exact_join (PCPOuter.exact_join r0 r1) r2) r3) r4
  have time:((((2*C+2)+1+(2*C+2))+1+(2*C+2))+1+(2*C+2))+1+(2*C+2)=10*C+14:=by omega
  rw [time] at all
  exact all

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads
