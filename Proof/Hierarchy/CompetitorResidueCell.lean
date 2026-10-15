import Proof.Hierarchy.CompetitorResidueReset

/-! One physical count-table cell: subtract signed score parts, crop modulo
2^Q and append the raw Q-bit natural count. The output cursor streams while
all local heads return to zero, and local support is independent of the
length of the global table prefix. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueCell
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 8) : Fin 9 := i.castAdd 1
def heads (out : List Bool) : Fin 9 → ℕ := fun i => if i.val=8 then out.length else 0
def input (w q a b : ℕ) (out : List Bool) : Fin 9 → List Bool :=
  Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool) (CompetitorSignedResidue.input w q a b) (fun _ => out)
noncomputable def residueProgram := RecoveryFocus.machine native CompetitorSignedResidue.machine
noncomputable def emitProgram := CompetitorRawScalarFieldEmit.program (5 : Fin 9) 8 3
noncomputable def machine := Composition.machine residueProgram emitProgram
def budget (w q : ℕ) := 4*w+8*q+13

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 9 => a.val) h)
theorem native_other (j : Fin 8) : native j≠8 := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=8 at hv
  omega

theorem residue_cell_run (w q a b : ℕ) (pre : List Bool) (ha : a<2^w) (hb : b<2^w) (hq : q≤w) :
    ∃ r out,runFrom machine (budget w q)
        (RecoveryCalls.restarted machine (heads pre) (input w q a b pre))=some r ∧
      r.steps≤budget w q ∧ r.final.heads=heads (pre++binary q (CompetitorSignedResidue.residue w q a b)) ∧
      r.final.tapes=out ∧ out 8=pre++binary q (CompetitorSignedResidue.residue w q a b) ∧
      out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧ out 4=List.replicate q true ∧
      (∀ i : Fin 8,(out (native i)).length≤12*(w+1)) := by
  obtain ⟨produced,hready,h0,h1,h3,h4,h5⟩ := CompetitorSignedResidue.residue_reset_run w q a b ha hb hq
  have hin : ∀ i,input w q a b pre (native i)=CompetitorSignedResidue.input w q a b i := by simp [input,native]
  have hh : ∀ i,heads pre (native i)=0 := by intro i; simp [heads,native,show i.val≠8 by omega]
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorReusableDecision.bounded_focused_run native native_injective _ _ _ hready
    (heads pre) (input w q a b pre) hh hin
  let middle := install native (input w q a b pre) produced
  have hm5 : middle 5=frame (binary q (CompetitorSignedResidue.residue w q a b)) :=
    (install_slot native native_injective _ produced 5).trans h5
  have hm8 : middle 8=pre := install_other native _ _ 8 native_other
  have hm3 : middle 3=List.replicate (2*w+1) false := (install_slot native native_injective _ produced 3).trans h3
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorRawScalarFieldEmit.field_run (5 : Fin 9) 8 3
    (by decide) (by decide) (by decide) (binary q (CompetitorSignedResidue.residue w q a b)) pre
    (2*w+1) (heads pre) middle rfl rfl rfl hm5 hm8 hm3 (by simp; omega)
  have he : Composition.restart first.final emitProgram.start=RecoveryCalls.restarted emitProgram (heads pre) middle := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom emitProgram (4*q+3) (Composition.restart first.final emitProgram.start)=some last := by
    rw [he]
    simpa only [binary_length,emitProgram] using hlast
  have hall := Composition.run_join residueProgram emitProgram _ _ _ first last hfirst hl'
  have htime : (4*w+4*q+9)+1+(4*q+3)=budget w q := by unfold budget; omega
  rw [htime] at hall
  let out := Function.update middle 8 (pre++binary q (CompetitorSignedResidue.residue w q a b))
  have hsupp : ∀ i : Fin 8,(produced i).length≤12*(w+1) := by
    obtain ⟨base,hr,ht,_,hs⟩ := hready
    have hinput : ∀ i,(CompetitorSignedResidue.input w q a b i).length≤12*(w+1) := by
      intro i
      fin_cases i <;> simp [CompetitorSignedResidue.input] <;> omega
    have hbound := RecoveryTapeSupport.run_support CompetitorSignedResidue.machine _ _ base hr (12*(w+1)) 0
      (by intro i; rfl) (by intro i; exact (hinput i).trans (Nat.le_max_left _ _))
    have hend : 0+base.steps+1≤12*(w+1) := by omega
    intro i
    rw [← ht]
    simpa only [max_eq_left hend] using hbound i
  refine ⟨Composition.joinedReceipt first last,out,hall,?_,?_,hlt,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget w q
    simp only [binary_length] at hls
    omega
  · change last.final.heads=heads (pre++binary q (CompetitorSignedResidue.residue w q a b))
    rw [hlh]
    funext i
    by_cases hi : i=8
    · subst i
      simp [heads]
    · have hv : i.val≠8 := fun h => hi (Fin.ext h)
      simp [Function.update_of_ne hi,heads,hv]
  · exact Function.update_self ..
  · exact (Function.update_of_ne (by decide : (0 : Fin 9)≠8) _ _).trans ((install_slot native native_injective _ produced 0).trans h0)
  · exact (Function.update_of_ne (by decide : (1 : Fin 9)≠8) _ _).trans ((install_slot native native_injective _ produced 1).trans h1)
  · exact (Function.update_of_ne (by decide : (4 : Fin 9)≠8) _ _).trans ((install_slot native native_injective _ produced 4).trans h4)
  · intro i
    change (Function.update middle 8 _ (native i)).length≤_
    rw [Function.update_of_ne (native_other i)]
    change (install native (input w q a b pre) produced (native i)).length≤_
    rw [install_slot native native_injective]
    exact hsupp i

theorem count_cell_run (w q a b count : ℕ) (pre : List Bool) (ha : a<2^w) (hb : b<2^w) (hq : q≤w)
    (hcount : count<2^q) (hcongruent : Int.ModEq ((2:ℤ)^q) ((a:ℤ)-b) count) :
    ∃ r out,runFrom machine (budget w q)
        (RecoveryCalls.restarted machine (heads pre) (input w q a b pre))=some r ∧
      r.steps≤budget w q ∧ r.final.heads=heads (pre++binary q count) ∧ r.final.tapes=out ∧
      out 8=pre++binary q count ∧ out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧
      out 4=List.replicate q true ∧ (∀ i : Fin 8,(out (native i)).length≤12*(w+1)) := by
  simpa only [CompetitorSignedResidue.residue_eq_count w q a b count hb hq hcount hcongruent] using residue_cell_run w q a b pre ha hb hq

end NearCubicWires.RepairOrdinary.CompetitorResidueCell
