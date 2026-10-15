import Proof.Supplier.RowIndexField

/-! Reuse the existing row capacity driver to erase the consumed occurrence
index. Only that index and its erase log are touched; the next stream cursor
and the two growing coefficient tapes remain live. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 24 := ![19,21,22]
theorem injective : Function.Injective slots := by decide
def heads (h : Fin 24 → ℕ) := Function.update h 19 0
def output (D : ℕ) : Fin 3 → List Bool :=
  ![List.replicate D false,List.replicate D true,List.replicate (D+1) false]
noncomputable def tapes (D : ℕ) (a : Fin 24 → List Bool) := install slots a (output D)
def advance : Machine 24 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some
    ⟨1,fun _=>none,fun i=>if i=19 then .left else .stay⟩ else none
noncomputable def erase := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine advance erase

theorem advance_run (h : Fin 24 → ℕ) (a : Fin 24 → List Bool) (hh : h 19=1) :
    ∃ r,runFrom advance 1 ⟨advance.start,h,a⟩=some r ∧
      r.final.heads=heads h ∧ r.final.tapes=a ∧ r.steps=1 := by
  have hs : step advance ⟨advance.start,h,a⟩=some ⟨1,heads h,a⟩ := by
    simp [step,advance]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=19
      · subst i; simp [applyAction,heads,hh,HeadMove.apply]
      · simp [applyAction,heads,hi,HeadMove.apply]
    · rfl
  obtain ⟨r,hr,rf,rs⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads rf,congrArg Configuration.tapes rf,rs⟩

theorem clear_run (D : ℕ) (h : Fin 24 → ℕ) (a : Fin 24 → List Bool)
    (hi : h 19=1) (hd : h 21=0) (hl : h 22=0)
    (hb : (a 19).length≤D) (ht : a 21=List.replicate D true)
    (hz : a 22=List.replicate (D+1) false) :
    ∃ r,runFrom machine (2*D+6) ⟨machine.start,h,a⟩=some r ∧
      r.final.heads=heads h ∧ r.final.tapes=tapes D a ∧ r.steps=2*D+6 := by
  obtain ⟨move,hm,mh,mt,ms⟩ := advance_run h a hi
  have ready := RecoveryScratchErase.erase_ready D (D+1) (fun _ : Fin 1=>a 19)
    (by intro k; exact hb)
  simp only [max_self] at ready
  have hh : ∀ k,move.final.heads (slots k)=0 := by
    intro k
    rw [mh]
    fin_cases k <;> simp [heads,slots,hd,hl]
  have ha : ∀ k,move.final.tapes (slots k)=
      Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
          (fun _ : Fin 1=>a 19) (fun _=>List.replicate D true))
        (fun _=>List.replicate (D+1) false) k := by
    intro k
    rw [mt]
    fin_cases k <;> simp [slots,Fin.addCases,ht,hz]
  obtain ⟨clear,hc,ch,ct,cs⟩ := ready.focus_at slots injective move.final.heads move.final.tapes ha hh
  have whole := Composition.run_join advance erase _ _ _ move clear hm hc
  have time : 1+1+(2*D+4)=2*D+6 := by omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt move clear,whole,?_,?_,?_⟩
  · change clear.final.heads=_
    exact ch.trans mh
  · change clear.final.tapes=_
    rw [ct,mt]
    apply congrArg (install slots a)
    funext k
    fin_cases k <;> simp [output,Fin.addCases]
  · change move.steps+1+clear.steps=_
    rw [ms,cs,time]

end NearCubicWires.RepairOrdinary.RowOccurrenceClear
