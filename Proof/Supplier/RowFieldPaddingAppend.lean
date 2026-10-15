import Proof.Supplier.RowFieldPadding

/-! Append the physically widened field to the live cut stream. The source,
width and copy workspace retain their heads; only the output cursor moves. -/
namespace NearCubicWires.RepairOrdinary.RowFieldPaddingAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padSlots : Fin 4→Fin 5 := fun i=>i.castAdd 1
def copySlots : Fin 3→Fin 5 := ![1,4,3]
theorem pad_injective : Function.Injective padSlots := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 5=>k.val) h)
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def first := RecoveryFocus.machine padSlots RecoveryColdPaddedCopy.machine
noncomputable def last := RecoveryFocus.machine copySlots PCPSerializerReuse.copyMachine
noncomputable def machine := Composition.machine first last
def heads (out : List Bool) : Fin 5→ℕ := ![0,0,0,0,out.length]
def extend (a : Fin 4→List Bool) (out : List Bool) : Fin 5→List Bool :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool) a (fun _=>out)
def input (w p F : ℕ) (z : ℤ) (out : List Bool) := extend (RowFieldPadding.input w p F z) out
def output (w p F : ℕ) (z : ℤ) (out : List Bool) := extend (RowFieldPadding.output w p F z) out

theorem pick (i : Fin 5) : RecoveryFocus.pick copySlots i=
    (if i=1 then some 0 else if i=4 then some 1 else if i=3 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot copySlots copy_injective 0
    | exact RecoveryFocus.pick_slot copySlots copy_injective 1
    | exact RecoveryFocus.pick_slot copySlots copy_injective 2
    | decide

theorem append_run (w p F : ℕ) (z : ℤ) (out : List Bool) (hF : 2*p+5 ≤ F) :
    ∃ r,runFrom last (4*p+8) ⟨last.start,heads out,output w p F z out⟩=some r ∧
      r.final.heads=heads (out++frame (signMagnitude p z)) ∧
      r.final.tapes=output w p F z (out++frame (signMagnitude p z)) ∧ r.steps ≤ 4*p+8 := by
  let bits := signMagnitude p z
  let tail := List.replicate (F-(frame bits).length) false
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPSerializerReuse.copy_run [] bits tail out F
    (by simp [bits,signMagnitude]; omega)
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config copySlots copy_injective PCPSerializerReuse.copyMachine
    (heads out) (output w p F z out) _ _ base hb
  have hi : RecoveryFocus.config copySlots (heads out) (output w p F z out)
      (PCPSerializerReuse.copyEntry [] bits tail out F)=
      (⟨last.start,heads out,output w p F z out⟩ : Configuration 5 5) := by
    apply WilliamsSourceCrop.focus_same copySlots (⟨last.start,heads out,output w p F z out⟩ : Configuration 5 5)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · simp [output,extend,RowFieldPadding.output,Fin.addCases,ZeroPadding.pad,bits,tail,
          copySlots,PCPSerializerReuse.copyEntry]
      · rfl
      · rfl
  rw [hi] at hr
  have ht : 4*bits.length+4=4*p+8 := by simp [bits,signMagnitude]; omega
  rw [ht] at hr
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh]
    funext i; fin_cases i <;> simp [pick,heads,bits]
  · rw [rf]
    change install copySlots (output w p F z out) base.final.tapes=_
    rw [bt]
    funext i
    fin_cases i <;> simp [install,pick,output,extend,RowFieldPadding.output,Fin.addCases,
      ZeroPadding.pad,bits,tail]
  · rw [rs]
    exact bs.trans ht.le

theorem field_run (w p F : ℕ) (z : ℤ) (out : List Bool) (hw : w ≤ p)
    (hz : z.natAbs<2^w) (hF : 2*p+5 ≤ F) :
    ∃ r,runFrom machine (8*p+21) ⟨machine.start,heads out,input w p F z out⟩=some r ∧
      r.final.heads=heads (out++frame (signMagnitude p z)) ∧
      r.final.tapes=output w p F z (out++frame (signMagnitude p z)) ∧ r.steps ≤ 8*p+21 := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := (RowFieldPadding.padding_ready w p F z hw hz hF).focus_at
    padSlots pad_injective (heads out) (input w p F z out)
    (by intro i; simp [input,extend,padSlots]) (by intro i; fin_cases i <;> rfl)
  have haout : a.final.tapes=output w p F z out := by
    rw [atapes]
    funext i
    refine Fin.addCases (m:=4) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simpa only [output,extend,Fin.addCases_left,padSlots] using
        install_slot padSlots pad_injective (input w p F z out) (RowFieldPadding.output w p F z) j
    · simpa only [input,output,extend,Fin.addCases_right] using
        install_other padSlots (input w p F z out) (RowFieldPadding.output w p F z) (j.natAdd 4) (by
        intro k
        have hk := k.isLt
        simp only [padSlots,Fin.ne_iff_vne,Fin.val_castAdd,Fin.val_natAdd]
        omega)
  obtain ⟨b,hb,bh,bt,bs⟩ := append_run w p F z out hF
  have he : (⟨last.start,heads out,output w p F z out⟩ : Configuration 5 5)=
      Composition.restart a.final last.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact haout.symm
  rw [he] at hb
  have h := Composition.run_join first last _ _ _ a b ha hb
  have ht : (4*p+12)+1+(4*p+8)=8*p+21 := by omega
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,bh,bt,?_⟩
  change a.steps+1+b.steps ≤ _
  rw [asteps]
  omega

end NearCubicWires.RepairOrdinary.RowFieldPaddingAppend
