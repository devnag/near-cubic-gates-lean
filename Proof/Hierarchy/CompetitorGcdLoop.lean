import Proof.Hierarchy.CompetitorGcdUpdate

/-! One fixed ordinary gcd loop, with no supplied iteration counter. Each
nonterminal pass decreases a+b; the cap on the complete guessed witness
therefore pays for even the largest malformed rational fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 7→ℕ := ![9,9,9,13,13,6,6]
noncomputable def programs : (j : Fin 7)→Machine 7 (sizes j)
  | ⟨0,_⟩=>check 0
  | ⟨1,_⟩=>check 1
  | ⟨2,_⟩=>check 2
  | ⟨3,_⟩=>update 0
  | ⟨4,_⟩=>update 1
  | ⟨5,_⟩=>select 0
  | ⟨6,_⟩=>select 1
  | ⟨n+7,h⟩=>False.elim (by omega)
def next (j : Fin 7) (_ : Fin (sizes j)) (cells : Fin 7→Bool) : Option (Fin 7) :=
  ![some (if cells 4 then 6 else 1),some (if cells 4 then 5 else 2),
    some (if cells 4 then 4 else 3),some 0,some 0,none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (w a b c : ℕ) (flag : Bool) :=
  controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) (data w a b c flag))
noncomputable def stopped (w a b c : ℕ) := RecoveryCalls.stopped sizes (fun _ : Fin 7=>0) (data w a b c true)
def unit (w : ℕ) := 32*w+40

theorem loop (w a b c : ℕ) (flag : Bool) (ha : a<2^w) (hb : b<2^w) :
    ∃ t aa bb,t≤(a+b+1)*unit w ∧
      Timed machine t (entry w a b c flag) (stopped w aa bb (Nat.gcd a b)) := by
  generalize hn : a+b=n
  induction n using Nat.strong_induction_on generalizing a b c flag with
  | h n ih =>
    by_cases haz : a=0
    · subst a
      have h0 := (check_ready w 0 b c flag 0 ha hb).call sizes programs 0 next 0 6 (by intro q;rfl)
      have h1 := (select_ready w 0 b c true 1).stop sizes programs 0 next 6 (by intro q;rfl)
      have h := h0.trans h1
      refine ⟨(4*w+6+1)+(8*w+8+1),0,b,?_,?_⟩
      · unfold unit;nlinarith
      · simpa only [machine,entry,stopped,minuend,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.gcd_zero_left] using h
    · have h0 := (check_ready w a b c flag 0 ha hb).call sizes programs 0 next 0 1 (by
        intro q
        change some (if decide (a≤0) then 6 else 1)=some 1
        simp [haz])
      have hf : decide (left a b (0 : Fin 3)≤right b 0)=false := by simp [left,right,haz]
      rw [hf] at h0
      by_cases hbz : b=0
      · subst b
        have h1 := (check_ready w a 0 c false 1 ha hb).call sizes programs 0 next 1 5 (by intro q;rfl)
        have h2 := (select_ready w a 0 c true 0).stop sizes programs 0 next 5 (by intro q;rfl)
        have h := (h0.trans h1).trans h2
        refine ⟨((4*w+6+1)+(4*w+6+1))+(8*w+8+1),a,0,?_,?_⟩
        · unfold unit;nlinarith
        · simpa only [machine,entry,stopped,minuend,Matrix.cons_val_zero,Nat.gcd_zero_right] using h
      · have h1 := (check_ready w a b c false 1 ha hb).call sizes programs 0 next 1 2 (by
          intro q
          change some (if decide (b≤0) then 5 else 2)=some 2
          simp [hbz])
        have hbf : decide (left a b (1 : Fin 3)≤right b 1)=false := by simp [left,right,hbz]
        rw [hbf] at h1
        by_cases hab : a≤b
        · have h2 := (check_ready w a b c false 2 ha hb).call sizes programs 0 next 2 4 (by
            intro q
            change some (if decide (a≤b) then 4 else 3)=some 4
            simp [hab])
          have hat : decide (left a b (2 : Fin 3)≤right b 2)=true := by simp [left,right,hab]
          rw [hat] at h2
          have hu := (update_ready w a b c true 1 ha hb hab).call sizes programs 0 next 4 0 (by intro q;rfl)
          obtain ⟨t,aa,bb,ht,hi⟩ := ih (a+(b-a)) (by omega) a (b-a) (b-a) true ha (by omega) rfl
          rw [Nat.gcd_sub_self_right hab] at hi
          have h := (((h0.trans h1).trans h2).trans hu).trans hi
          refine ⟨(((4*w+6+1)+(4*w+6+1))+(4*w+6+1))+(12*w+13+1)+t,aa,bb,?_,h⟩
          have hh := Nat.mul_le_mul_right (unit w) (show a+(b-a)+1≤a+b by omega)
          unfold unit at *
          nlinarith
        · have h2 := (check_ready w a b c false 2 ha hb).call sizes programs 0 next 2 3 (by
            intro q
            change some (if decide (a≤b) then 4 else 3)=some 3
            simp [hab])
          have haf : decide (left a b (2 : Fin 3)≤right b 2)=false := by simp [left,right,hab]
          rw [haf] at h2
          have hba : b≤a := by omega
          have hu := (update_ready w a b c false 0 ha hb hba).call sizes programs 0 next 3 0 (by intro q;rfl)
          obtain ⟨t,aa,bb,ht,hi⟩ := ih ((a-b)+b) (by omega) (a-b) b (a-b) false (by omega) hb rfl
          rw [Nat.gcd_sub_self_left hba] at hi
          have h := (((h0.trans h1).trans h2).trans hu).trans hi
          refine ⟨(((4*w+6+1)+(4*w+6+1))+(4*w+6+1))+(12*w+13+1)+t,aa,bb,?_,h⟩
          have hh := Nat.mul_le_mul_right (unit w) (show (a-b)+b+1≤a+b by omega)
          unfold unit at *
          nlinarith

end NearCubicWires.RepairOrdinary.CompetitorGcd
