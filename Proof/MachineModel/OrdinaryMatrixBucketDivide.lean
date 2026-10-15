import Proof.MachineModel.OrdinaryMatrixBucketDivideKernel

/-! Complete paid positive-divisor quotient, including final head resets.
This supplies the guarded canonical bucket divisions from actual unary data. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketDivide
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawBudget (n d : ℕ) := (n/d)*(2*d+2)+(n%d)+2
theorem groups_timed (n d count remaining : ℕ) (h : (count+remaining)*d≤n) :
    Timed raw (remaining*(2*d+2)) (cfg 1 n d (count*d) 1 count)
      (cfg 1 n d ((count+remaining)*d) 1 (count+remaining)) := by
  induction remaining generalizing count with
  | zero => simp only [Nat.zero_mul,Nat.add_zero]; exact Timed.refl _ _
  | succ remaining ih =>
    have hfirst : count*d+d≤n := by nlinarith
    have hgroup := group_timed n d (count*d) count hfirst
    have hpos : count*d+d=(count+1)*d := by ring
    rw [hpos] at hgroup
    have ht := ih (count+1) (by simpa only [Nat.add_assoc,Nat.add_comm 1 remaining] using h)
    have hend : count+1+remaining=count+(remaining+1) := by omega
    rw [hend] at ht
    have htime : (2*d+2)+remaining*(2*d+2)=(remaining+1)*(2*d+2) := by ring
    simpa only [htime] using hgroup.trans ht

theorem raw_run (n d : ℕ) (hd : 0<d) :
    ∃ actual,run raw (rawBudget n d) (input n d)=some actual ∧
      actual.final=cfg 3 n d n (n%d+1) (n/d) ∧ actual.steps=rawBudget n d := by
  have he : n/d*d+n%d=n := by
    have h := Nat.mod_add_div n d
    nlinarith
  have hstart := Timed.single (by rfl) (boot_step n d)
  have hgroups := groups_timed n d 0 (n/d) (by simpa only [Nat.zero_add] using Nat.div_mul_le_self n d)
  simp only [Nat.zero_mul,Nat.zero_add] at hgroups
  have htail := scan_prefix n d (n/d*d) 0 (n/d) (n%d) (by omega)
    (by simpa only [Nat.zero_add] using (Nat.mod_lt n hd).le)
  simp only [Nat.zero_add,he] at htail
  have hstop := Timed.single (by rfl) (stop_step n d (n%d) (n/d) (Nat.mod_lt n hd))
  have hall := ((hstart.trans hgroups).trans htail).trans hstop
  have ht : 1+(n/d)*(2*d+2)+n%d+1=rawBudget n d := by unfold rawBudget; omega
  rw [ht] at hall
  exact hall.run (by rfl)

theorem rawBudget_le (n d : ℕ) (hd : 0<d) : rawBudget n d≤4*n+2 := by
  have he := Nat.mod_add_div n d
  have he' : n/d*d+n%d=n := by nlinarith
  have hq : n/d≤n/d*d := by
    have h := Nat.mul_le_mul_left (n/d) (show 1≤d by omega)
    simpa only [Nat.mul_one] using h
  unfold rawBudget
  rw [show n/d*(2*d+2)=2*(n/d*d)+2*(n/d) by ring]
  omega

def machine := Rewind.machine raw
def resetInput (n d : ℕ) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input n d) (fun _ : Fin 1 => [])
theorem divide_run (n d : ℕ) (hd : 0<d) :
    ∃ actual,run machine (8*n+6) (resetInput n d)=some actual ∧
      actual.final.tapes 0=List.replicate n true ∧ actual.final.tapes 1=UnaryTemplate.tape d ∧
      actual.final.tapes 2=List.replicate (n/d) true ∧ (∀ i,actual.final.heads i=0) ∧ actual.steps≤8*n+6 := by
  obtain ⟨base,hb,hbf,hbs⟩ := raw_run n d hd
  obtain ⟨actual,ha,atapes,ah,as,_⟩ := Rewind.reset_run raw (rawBudget n d) (input n d) base hb
  have hbound : 2*base.steps+2≤8*n+6 := by
    rw [hbs]
    have h := rawBudget_le n d hd
    omega
  have he := run_moreFuel machine _ (8*n+6-(2*base.steps+2)) (resetInput n d) actual ha
  rw [Nat.add_sub_of_le hbound] at he
  refine ⟨actual,he,?_,?_,?_,ah,as.trans_le hbound⟩
  · exact (atapes 0).trans (congrArg (fun c => c.tapes 0) hbf)
  · exact (atapes 1).trans (congrArg (fun c => c.tapes 1) hbf)
  · exact (atapes 2).trans (congrArg (fun c => c.tapes 2) hbf)

end NearCubicWires.RepairOrdinary.MatrixBucketDivide
