import Proof.Hierarchy.CompetitorRawRecordEmit

/-! Two actual normalizers widen the produced positive and negative
numerators for the scalar-stream consumer. Their paid zero counter is
retained for subsequent framed appending. -/
namespace NearCubicWires.RepairOrdinary.CompetitorNumeratorWiden
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 2) : Fin 5 → Fin 9 := if j.val=0 then ![0,1,3,4,5] else ![0,2,6,7,8]
def input (b w p n : ℕ) : Fin 9 → List Bool :=
  ![List.replicate w true,frame (binary b p),frame (binary b n),[],[],[],[],[],[]]
noncomputable def partProgram (j : Fin 2) := RecoveryFocus.machine (slots j) ClockNormalize.machine
noncomputable def machine := Composition.machine (partProgram 0) (partProgram 1)

theorem widen_run (b w p n : ℕ) (hb : b≤w) (hp : p<2^b) (hn : n<2^b) :
    ∃ out,ClockJoin.ReadyRun machine (8*w+9) (input b w p n) out ∧
      out 0=List.replicate w true ∧ out 3=frame (binary w p) ∧ out 6=frame (binary w n) ∧
      out 5=List.replicate (2*w+1) false := by
  obtain ⟨pos,hpRun,hp0,_,hp2,_,hp4,hph,hps⟩ := ClockScalarFields.scalar_run w (binary b p) (by simpa using hb)
  have posReady : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4)
      (ClockNormalize.input w (binary b p)) pos.final.tapes := ⟨pos,hpRun,rfl,hph,hps.le⟩
  let first := install (slots 0) (input b w p n) pos.final.tapes
  have hfirst := bounded_focus (slots 0) (by decide) _ _ _ posReady (input b w p n)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨neg,hnRun,hn0,_,hn2,_,_,hnh,hns⟩ := ClockScalarFields.scalar_run w (binary b n) (by simpa using hb)
  have negReady : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4)
      (ClockNormalize.input w (binary b n)) neg.final.tapes := ⟨neg,hnRun,rfl,hnh,hns.le⟩
  have hi : ∀ i,first (slots 1 i)=ClockNormalize.input w (binary b n) i := by
    intro i
    fin_cases i
    · exact (install_slot (slots 0) (by decide) _ _ 0).trans hp0
    · exact install_other (slots 0) _ _ 2 (by decide)
    · exact install_other (slots 0) _ _ 6 (by decide)
    · exact install_other (slots 0) _ _ 7 (by decide)
    · exact install_other (slots 0) _ _ 8 (by decide)
  let out := install (slots 1) first neg.final.tapes
  have hlast := bounded_focus (slots 1) (by decide) _ _ _ negReady first hi
  have hall := ClockJoin.join (partProgram 0) (partProgram 1) _ _ _ _ _ hfirst hlast
  have hc : (4*w+4)+1+(4*w+4)=8*w+9 := by omega
  rw [hc] at hall
  refine ⟨out,hall,?_,?_,?_,?_⟩
  · exact (install_slot (slots 1) (by decide) _ _ 0).trans hn0
  · simpa only [binary_value b p hp] using (install_other (slots 1) _ _ 3 (by decide)).trans
      ((install_slot (slots 0) (by decide) _ _ 2).trans hp2)
  · change install (slots 1) first neg.final.tapes (slots 1 2)=frame (binary w n)
    simpa only [binary_value b n hn] using (install_slot (slots 1) (by decide) first neg.final.tapes 2).trans hn2
  · exact (install_other (slots 1) _ _ 5 (by decide)).trans
      ((install_slot (slots 0) (by decide) _ _ 4).trans hp4)

end NearCubicWires.RepairOrdinary.CompetitorNumeratorWiden
