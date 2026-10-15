import Proof.Supplier.EquationNaturalHeader
import Proof.Amplification.RecoveryFocusDock
import Proof.PCP.PCPPQueryField

/-! A physically supplied raw unary natural is converted to the exact
native natWord and appended at the live descriptor cursor. Zero is covered
by the existing total header producer; the output prefix is never rewound. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNaturalAppend
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 16) : Fin 18 := i.castAdd 2
def appendSlots : Fin 3 → Fin 18 := ![14,16,17]
noncomputable def first := RecoveryFocus.machine headerSlots EquationNaturalHeader.machine
noncomputable def last := RecoveryFocus.machine appendSlots (PCPPQueryField.machine true)
noncomputable def machine := Composition.machine first last
def data (n : ℕ) (out : List Bool) (i : Fin 18) : List Bool :=
  if i=0 then List.replicate n true else if i=17 then out else []
def heads (out : List Bool) (i : Fin 18) : ℕ := if i=17 then out.length else 0
noncomputable def entry (n : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data n out⟩ : Configuration 18 _)
def budget (n : ℕ) := EquationNaturalHeader.budget n+2+1+(2*natBitLength n+3)

theorem append_run (n : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (budget n) (entry n out)=some r ∧ r.steps≤budget n ∧
      r.final.tapes 17=out++natWord n ∧ r.final.heads 17=(out++natWord n).length ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.heads 1=0 := by
  obtain ⟨printed,⟨base,hbase,bt,bh,bs⟩,p1,p14⟩ := EquationNaturalHeader.header_ready n
  have headerBound (i : Fin 16) : (headerSlots i).val<16 := i.isLt
  obtain ⟨a,ha,_,asteps,aheads,atapes,akeep⟩ := RecoveryFocus.dock
    headerSlots (by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 18 => x.val) h)
    EquationNaturalHeader.machine _
    (heads out) (data n out)
    (initialConfiguration EquationNaturalHeader.machine (EquationNaturalHeader.input n))
    (by intro i
        have hn : headerSlots i≠17 := fun h => by
          have hv := congrArg Fin.val h
          change i.val=17 at hv
          omega
        simp only [heads,hn,ite_false,initialConfiguration])
    (by intro i
        have hn : headerSlots i≠17 := fun h => by
          have hv := congrArg Fin.val h
          change i.val=17 at hv
          omega
        have hz : headerSlots i=0 ↔ i=0 := by
          constructor
          · intro h; apply Fin.ext; exact congrArg (fun x : Fin 18 => x.val) h
          · intro h; subst i; rfl
        simp only [data,EquationNaturalHeader.input,initialConfiguration,hn,hz,ite_false])
    base hbase
  obtain ⟨copied,hcopied,cf,cs⟩ := PCPPQueryField.nat_run true [] [] [] out n
  obtain ⟨b,hb,_,bsteps,bheads,btapes,bkeep⟩ := RecoveryFocus.dock
    appendSlots (by decide) (PCPPQueryField.machine true) _ a.final.heads a.final.tapes
    (PCPPQueryField.cfg 0 ([]++natWord n++[]) 0 [] 0 out)
    (by intro i; fin_cases i
        · exact (aheads 14).trans (bh 14)
        · exact (akeep 16 (by intro j; have := headerBound j; apply Fin.ne_of_val_ne; omega)).1
        · exact (akeep 17 (by intro j; have := headerBound j; apply Fin.ne_of_val_ne; omega)).1)
    (by intro i; fin_cases i
        · exact (atapes 14).trans (by rw [bt,p14]; simp only [List.nil_append,List.append_nil]; rfl)
        · exact (akeep 16 (by intro j; have := headerBound j; apply Fin.ne_of_val_ne; omega)).2
        · exact (akeep 17 (by intro j; have := headerBound j; apply Fin.ne_of_val_ne; omega)).2)
    copied hcopied
  let r := Composition.joinedReceipt a b
  have hr := Composition.run_join first last _ _ _ a b ha hb
  refine ⟨r,hr,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤_
    rw [asteps,bsteps,cs]
    unfold budget
    omega
  · change b.final.tapes 17=_
    exact (btapes 2).trans (by rw [cf]; rfl)
  · change b.final.heads 17=_
    exact (bheads 2).trans (by rw [cf]; rfl)
  · change b.final.tapes 1=_
    rw [(bkeep 1 (by decide)).2]
    exact (atapes 1).trans (by rw [bt]; exact p1)
  · change b.final.heads 1=_
    rw [(bkeep 1 (by decide)).1]
    exact (aheads 1).trans (bh 1)

theorem budget_bound (n : ℕ) : budget n≤256*(n+1)^2 := by
  have hw : natBitLength n≤n+1 := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1
  unfold budget EquationNaturalHeader.budget
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPNativeNaturalAppend
