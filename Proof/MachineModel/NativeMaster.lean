import Proof.MachineModel.NativeShort

/-! All fifteen distinct source words for native initialization are outputs
of one fixed ordinary run over the same measured cache. -/
namespace NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 135) : Fin 149:=i.castAdd 14
def slots : Fin 17→Fin 149:=![3,88,36,135,136,137,138,139,140,141,142,143,144,145,146,147,148]
theorem slots_injective : Function.Injective slots:=by decide
def fields : Fin 15→Fin 149:=![0,15,27,3,31,57,86,135,4,146,139,143,88,53,141]
theorem fields_injective : Function.Injective fields:=by decide
def words {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) : Fin 15→List Bool:=
  ![exactListWord gs,List.replicate (RowCachedCoordinateBounds.width gs) true,
    List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true,
    UnaryTemplate.tape n,
    List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true,
    CompareMachine.word (NativeWidth.width gs Q+1),List.replicate (NativeAllocation.capacity gs Q) true,
    CompareMachine.word (n+1),UnaryTemplate.tape gs.length,frame (SignedSortKey.binary w 0),
    CompareMachine.word w,CompareMachine.word 1,List.replicate w true,
    List.replicate (NativeWidth.width gs Q) true,CompareMachine.word Q]
noncomputable def first:=TapeEmbedding.machine 14 NativeMeasured.machine
noncomputable def last:=RecoveryFocus.machine slots NativeShort.machine
noncomputable def machine:=Composition.machine first last
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 149→ℕ:=
  Fin.addCases (m:=135) (n:=14) (motive:=fun _=>ℕ) (NativeMeasured.heads gs) (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) : Fin 149→List Bool:=
  Fin.addCases (m:=135) (n:=14) (motive:=fun _=>List Bool) (NativeMeasured.input gs Q w) (fun _=>[])
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=
  NativeMeasured.budget gs Q w+1+NativeShort.budget n w Q

theorem master_run {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) : ∃ H O,
    Step machine (budget gs Q w) (heads gs) (input gs Q w) H O ∧
      (∀ j,H (fields j)=0) ∧ (∀ j,O (fields j)=words gs Q w j) ∧
      H 133=0 ∧ O 133=List.replicate (NativeMeasured.capacity gs Q w) true:=by
  obtain ⟨H,A,run,cache,ch,arity,ah,inner,ih,outer,oh,dh,dt,wh,wt,allocated,fh,ph,pt,cap,capH⟩:=
    NativeMeasured.measured_run gs Q w
  have start:=run.embed (fun _ : Fin 14=>0) (fun _=>[])
  let H' : Fin 149→ℕ:=Fin.addCases (m:=135) (n:=14) (motive:=fun _=>ℕ) H (fun _=>0)
  let A' : Fin 149→List Bool:=Fin.addCases (m:=135) (n:=14) (motive:=fun _=>List Bool) A (fun _=>[])
  have hh : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact ah
    · exact ph 3
    · exact dh 2
    all_goals rfl
  have ha : ∀ j,A' (slots j)=NativeShort.input n w Q j:=by
    intro j;fin_cases j
    · exact arity
    · exact pt 3
    · exact dt 2
    all_goals rfl
  obtain ⟨short,ready,keep,zero⟩:=NativeShort.short_run n w Q
  obtain ⟨r,hr,rh,rt,_rs⟩:=ready.focus_at slots slots_injective H' A' ha hh
  have whole:=start.seq (Step.of_run hr rh rt)
  let O:=install slots A' short
  have field (j : Fin 17) : O (slots j)=short j:=install_slot slots slots_injective A' short j
  have preserved (i : Fin 135) (h3 : i≠3) (h36 : i≠36) (h88 : i≠88) : O (old i)=A i:=by
    rw [←show A' (old i)=A i by simp only [A',old,Fin.addCases_left]]
    apply install_other slots A' short (old i)
    intro j he
    have hv:=congrArg (fun x : Fin 149=>x.val) he
    have hi:=i.isLt
    have n3 : i.val≠3:=fun h=>h3 (Fin.ext h)
    have n36 : i.val≠36:=fun h=>h36 (Fin.ext h)
    have n88 : i.val≠88:=fun h=>h88 (Fin.ext h)
    fin_cases j <;> simp [slots,old] at hv <;> omega
  refine ⟨H',O,whole,?_,?_,capH,(preserved 133 (by decide) (by decide) (by decide)).trans cap⟩
  · intro j;fin_cases j
    · exact ch
    · exact dh 0
    · exact ih
    · exact ah
    · exact oh
    · exact wh 8
    · exact fh
    · exact hh 3
    · exact dh 1
    · exact hh 14
    · exact hh 7
    · exact hh 11
    · exact ph 3
    · exact wh 4
    · exact hh 9
  · intro j;fin_cases j
    · exact (preserved 0 (by decide) (by decide) (by decide)).trans cache
    · exact (preserved 15 (by decide) (by decide) (by decide)).trans (dt 0)
    · exact (preserved 27 (by decide) (by decide) (by decide)).trans inner
    · exact (field 0).trans (keep 0)
    · exact (preserved 31 (by decide) (by decide) (by decide)).trans outer
    · exact (preserved 57 (by decide) (by decide) (by decide)).trans (wt 8)
    · exact (preserved 86 (by decide) (by decide) (by decide)).trans allocated
    · exact (field 3).trans (keep 3)
    · exact (preserved 4 (by decide) (by decide) (by decide)).trans (dt 1)
    · exact (field 14).trans zero
    · exact (field 7).trans (keep 7)
    · exact (field 11).trans (keep 11)
    · exact (field 1).trans (keep 1)
    · exact (preserved 53 (by decide) (by decide) (by decide)).trans (wt 4)
    · exact (field 9).trans (keep 9)

end NearCubicWires.ExtIncidence.NativeMaster

