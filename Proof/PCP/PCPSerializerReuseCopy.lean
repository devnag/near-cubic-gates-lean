import Proof.PCP.PCPSerializerReuseReset
import Proof.PCP.ProjectionNormalizationCursorRestore
import Proof.PCP.ProjectionNormalizationField

/-! Append the serializer's framed result before erasing its reusable bank.
The result cursor is physically restored; the growing output cursor stays
live, and the shared reset log retains its paid finite zero backing. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copyMachine : Machine 3 5 := CursorRestore.machine Field.machine 0
def copyCaps (capacity : ℕ) : Fin 3 → ℕ := ![0,0,capacity]
def copyEntry (pre bits suffix out : List Bool) (capacity : ℕ) : Configuration 3 5 :=
  ⟨copyMachine.start,![pre.length,out.length,0],
    ![pre++frame bits++suffix,out,List.replicate capacity false]⟩

theorem field_forward : CursorRestore.NoLeft Field.machine 0 := by
  intro q bits a ha
  simp only [Field.machine] at ha
  split at ha
  · cases ha; simp
  · split at ha
    · cases ha; simp
    · contradiction

theorem copy_run (pre bits suffix out : List Bool) (capacity : ℕ)
    (hcap : 2*bits.length+1 ≤ capacity) :
    ∃ r,runFrom copyMachine (4*bits.length+4)
      (copyEntry pre bits suffix out capacity)=some r ∧
      r.final.heads=![pre.length,(out++frame bits).length,0] ∧
      r.final.tapes=![pre++frame bits++suffix,out++frame bits,List.replicate capacity false] ∧
      r.steps ≤ 4*bits.length+4 := by
  obtain ⟨source,hr,hf,hs⟩ := Field.copy_run pre bits suffix out
  obtain ⟨base,delta,hb,hd,hbs,hbf⟩ :=
    CursorRestore.restore_run Field.machine 0 field_forward _ _ source hr
  have he : 2*source.steps+2=4*bits.length+4 := by omega
  rw [he] at hb
  obtain ⟨r,hrun,hrt,hrs,_⟩ := ZeroPadding.run_config copyMachine
    (copyCaps capacity) _ _ base hb
  have hi : ZeroPadding.config (copyCaps capacity)
      (Rewind.recording (Field.cfg 0 (pre++frame bits++suffix) pre.length out) 0)=
      copyEntry pre bits suffix out capacity := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i
      · change ZeroPadding.pad 0 (pre++frame bits++suffix)=_
        exact ZeroPadding.pad_zero _
      · change ZeroPadding.pad 0 out=out
        exact ZeroPadding.pad_zero _
      · change ZeroPadding.pad capacity []=List.replicate capacity false
        simp [ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,?_⟩
  · rw [hrt,hbf,hf]
    funext i
    fin_cases i <;> rfl
  · rw [hrt,hbf,hf]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad capacity (Fin.addCases
        (Field.cfg 2 (pre++frame bits++suffix) (pre.length+2*bits.length+1)
          (out++frame bits)).tapes
        (fun _ : Fin 1 => List.replicate delta false) ((0 : Fin 1).natAdd 2))=_
      rw [Fin.addCases_right]
      exact pad_zeros capacity delta (by omega)
  · omega

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
