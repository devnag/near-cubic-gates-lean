import Proof.Assembly.RowsPoolSignedFields
import Proof.Hierarchy.HierarchyFixedWord

/-! Total P/N scalar to the exact original native magnitude. Zero takes one
fixed literal branch; positive values reuse the existing trim/native worker.
The same signed normalization flag is retained for the final integer append. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolSigned
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positiveSlots : Fin 8→Fin 15:=![3,6,7,8,9,10,11,12]
def literalSlots : Fin 2→Fin 15:=![9,13]
theorem positive_injective : Function.Injective positiveSlots:=by decide
theorem literal_injective : Function.Injective literalSlots:=by decide
noncomputable def positive:=RecoveryFocus.machine positiveSlots CloseoutRowsStrictMagnitude.positiveMachine
noncomputable def zero:=RecoveryFocus.machine literalSlots
  (HierarchyFixedWord.machine (RepairRepresentation.natWord 0))
noncomputable def calls : Fin 3→Σ s,Machine 15 s
  | ⟨0,_⟩=>⟨_,prefixMachine⟩
  | ⟨1,_⟩=>⟨_,positive⟩
  | ⟨2,_⟩=>⟨_,zero⟩
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def sizes (j : Fin 3):=(calls j).1
noncomputable def programs (j : Fin 3) : Machine 15 (sizes j):=(calls j).2
def next (j : Fin 3) (_ : Fin (sizes j)) (bs : Fin 15→Bool) : Option (Fin 3):=
  if j=0 then some (if bs 2 && bs 5 then 2 else 1) else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
def selected (p n : ℕ) : Fin 3:=if p=n then 2 else 1
def budget (w : ℕ):=32*w+48

theorem positive_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) (he : p≠n) : ∃ out,
    ClockJoin.ReadyRun positive (20*w+31) (compared w p n cap) out ∧
      out 9=RepairRepresentation.natWord (RowCoefficientNormalize.magnitude p n) ∧
      out 2=[decide (n≤p)]:=by
  obtain ⟨out,ho,hword⟩:=CloseoutRowsStrictMagnitude.positive_native_run w
    (RowCoefficientNormalize.magnitude p n) (magnitude_positive p n he) (magnitude_fit w p n hp hn)
  have h:=ho.focus positiveSlots positive_injective (compared w p n cap)
    (by intro i;fin_cases i <;> rfl)
  refine ⟨_,h,?_,?_⟩
  · exact (install_slot positiveSlots positive_injective _ _ 4).trans hword
  · exact install_other positiveSlots _ _ 2 (by decide)

theorem zero_run (w p n cap : ℕ) (he : p=n) : ∃ out,
    ClockJoin.ReadyRun zero 8 (compared w p n cap) out ∧
      out 9=RepairRepresentation.natWord (RowCoefficientNormalize.magnitude p n) ∧
      out 2=[decide (n≤p)]:=by
  obtain ⟨r,hr,rt,rh,rs⟩:=HierarchyFixedWord.word_ready (RepairRepresentation.natWord 0)
  have h:ClockJoin.ReadyRun (HierarchyFixedWord.machine (RepairRepresentation.natWord 0)) 8
      (fun _=>[]) ![RepairRepresentation.natWord 0,List.replicate 3 false]:=⟨r,hr,rt,rh,rs.le⟩
  have actual:=h.focus literalSlots literal_injective (compared w p n cap)
    (by intro i;fin_cases i <;> rfl)
  refine ⟨_,actual,?_,?_⟩
  · have hm:RowCoefficientNormalize.magnitude p n=0:=by
      subst n;simp [RowCoefficientNormalize.magnitude]
    rw [hm]
    exact install_slot literalSlots literal_injective _ _ 0
  · exact install_other literalSlots _ _ 2 (by decide)

theorem arm_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) : ∃ out,
    ClockJoin.ReadyRun (programs (selected p n)) (20*w+31) (compared w p n cap) out ∧
      out 9=RepairRepresentation.natWord (RowCoefficientNormalize.magnitude p n) ∧
      out 2=[decide (n≤p)]:=by
  by_cases he:p=n
  · rw [selected,if_pos he]
    obtain ⟨out,ho,h9,h2⟩:=zero_run w p n cap he
    exact ⟨out,ClockJoin.enlarge _ _ _ _ _ ho (by omega),h9,h2⟩
  · rw [selected,if_neg he]
    exact positive_run w p n cap hp hn he

theorem native_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) : ∃ out,
    ClockJoin.ReadyRun machine (budget w) (input w p n cap) out ∧
      out 9=RepairRepresentation.natWord (RowCoefficientNormalize.magnitude p n) ∧
      out 2=[decide (n≤p)]:=by
  obtain ⟨first,hf,ft,fh,_⟩:=prefix_run w p n cap hp hn
  have nextFirst:next 0 first.final.control first.final.scanned=some (selected p n):=by
    change some (if first.final.scanned 2 && first.final.scanned 5 then (2 : Fin 3) else 1)=_
    simp only [Configuration.scanned,ft,fh,compared_zero]
    by_cases he:p=n <;> simp [selected,he]
  obtain ⟨a,ha,firstCall⟩:=call_receipt sizes programs 0 next 0 (selected p n) (12*w+15)
    (initialConfiguration prefixMachine (input w p n cap)) first hf nextFirst
  have hi:RecoveryCalls.restarted (programs (selected p n)) first.final.heads first.final.tapes=
      initialConfiguration (programs (selected p n)) (compared w p n cap):=by
    apply configuration_ext
    · rfl
    · exact funext fh
    · exact ft
  rw [hi] at firstCall
  obtain ⟨out,⟨last,hl,lt,lh,_⟩,h9,h2⟩:=arm_run w p n cap hp hn
  obtain ⟨b,hb,lastCall⟩:=stop_receipt sizes programs 0 next (selected p n) (20*w+31)
    (initialConfiguration (programs (selected p n)) (compared w p n cap)) last hl (by
      have hs:selected p n≠0:=by unfold selected;split <;> decide
      simp [next,hs])
  obtain ⟨r,hr,rf,rs⟩:=(firstCall.trans lastCall).run
    (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hbudget:a+b≤budget w:=by unfold budget;omega
  have more:=runFrom_moreFuel machine (a+b) (budget w-(a+b)) _ r hr
  rw [Nat.add_sub_of_le hbudget] at more
  refine ⟨out,⟨r,more,?_,?_,rs.le.trans hbudget⟩,h9,h2⟩
  · rw [rf];exact lt
  · intro i;rw [rf];exact lh i

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolSigned
