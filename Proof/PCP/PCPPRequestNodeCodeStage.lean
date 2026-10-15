import Proof.PCP.PCPPRequestNodeCodeLayout

namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputSlot (bank : Fin 3) : Fin 234 := ⟨offset bank+64,by have hb := bank.isLt; unfold offset; omega⟩
def rawSlot (bank : Fin 3) : Fin 234 := ⟨offset bank+74,by have hb := bank.isLt; unfold offset; omega⟩

theorem stage_run {z : ℕ} (ambient : Configuration 234 z) (bank : Fin 3)
    (left right : Fin 234) (hl : left.val < offset bank) (hr : right.val < offset bank)
    (hne : left≠right) (a b pa pb : ℕ)
    (ha : ambient.tapes left=frame a.bits++List.replicate pa false)
    (hb : ambient.tapes right=frame b.bits++List.replicate pb false)
    (hh : ∀ i,ambient.heads i=0)
    (hf : ∀ i,offset bank ≤ i.val → i.val < offset bank+76 → ambient.tapes i=[]) :
    ∃ r,runFrom (cons bank left right) (PCPPRequestTaggedCons.budget a b)
      (Composition.restart ambient (cons bank left right).start)=some r ∧
      r.steps≤PCPPRequestTaggedCons.budget a b ∧ (∀ i,r.final.heads i=0) ∧
      (∃ padding,r.final.tapes (outputSlot bank)=
        frame (Nat.pair 1 (Nat.pair a b)).bits++List.replicate padding false) ∧
      r.final.tapes (rawSlot bank)=(Nat.pair 1 (Nat.pair a b)).bits ∧
      (∀ i,left≠i → right≠i →
        (i.val < offset bank ∨ offset bank+76 ≤ i.val) → r.final.tapes i=ambient.tapes i) := by
  have ht (j : Fin 76) : ambient.tapes (slots bank left right j)=
      if j=2 then frame a.bits++List.replicate pa false
      else if j=3 then frame b.bits++List.replicate pb false else [] := by
    by_cases h2 : j=2
    · subst j; exact ha
    by_cases h3 : j=3
    · subst j; simpa only [slots,ite_false,ite_true,show (3 : Fin 76)≠2 by decide] using hb
    rw [if_neg h2,if_neg h3]
    apply hf
    · simp only [slots,h2,h3,ite_false]; omega
    · simp only [slots,h2,h3,ite_false]; have hj := j.isLt; omega
  obtain ⟨r,hrun,rs,rh,rf,rr,rkeep⟩ := PCPPRequestNodeCons.cons_at
    (slots bank left right) (slots_injective bank left right hl hr hne)
    ambient a b pa pb ht (fun j => hh _)
  refine ⟨r,hrun,rs,?_,rf,rr,?_⟩
  · intro i; rw [rh]; exact hh i
  · intro i hli hri hi
    exact rkeep i (outside bank left right i hli hri hi)

theorem printer_run (a b c : ℕ) (binary : Bool) (pa pb pc : ℕ) :
    ∃ out,ClockJoin.ReadyRun printer 4 (input a b c binary pa pb pc) out ∧
      out 3=frame (0 : ℕ).bits ∧
      (∀ i,i≠3 → i≠4 → out i=input a b c binary pa pb pc i) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := HierarchyFixedWord.word_ready [false]
  have hp : ClockJoin.ReadyRun (HierarchyFixedWord.machine [false]) 4 (fun _ => [])
      ![[false],[false]] := ⟨r,hr,rt,rh,rs.le⟩
  have hf := CompetitorRationalProducts.bounded_focus printSlots printSlots_injective
    _ _ _ hp (input a b c binary pa pb pc) (by intro j; fin_cases j <;> rfl)
  refine ⟨install printSlots (input a b c binary pa pb pc) ![[false],[false]],hf,?_,?_⟩
  · exact install_slot printSlots printSlots_injective _ _ 0
  · intro i h3 h4
    exact install_other printSlots _ _ i (by
      intro j he
      fin_cases j
      · exact h3 he.symm
      · exact h4 he.symm)

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
