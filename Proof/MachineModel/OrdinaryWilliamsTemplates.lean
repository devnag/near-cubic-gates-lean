import Proof.MachineModel.OrdinaryWilliamsTemplateHeader

/-! All eight template/header calls in one executed finite controller.
The input consists only of the six dimension words produced by the prior
external-input phase; every remaining tape starts blank. -/
namespace NearCubicWires.RepairOrdinary.WilliamsTemplates
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairRepresentation RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Original (u c v : ℕ) (a : Fin 50 → List Bool) : Prop :=
  a 0=UnaryTemplate.tape u ∧ a 1=UnaryTemplate.tape c ∧ a 2=UnaryTemplate.tape v ∧
  a 3=UnaryTemplate.tape (natBitLength u) ∧ a 5=frame (binary (natBitLength v) v) ∧
  a 6=List.replicate (natBitLength v) true ∧ a 8=UnaryTemplate.tape (natBitLength v)

theorem Original.retain {u c v k : ℕ} {a b : Fin 50 → List Bool}
    (h : Original u c v a) (ho : Old k a b) (hk : 9 ≤ k) : Original u c v b := by
  rcases h with ⟨h0,h1,h2,h3,h5,h6,h8⟩
  exact ⟨(ho 0 (by omega)).trans h0,(ho 1 (by omega)).trans h1,(ho 2 (by omega)).trans h2,
    (ho 3 (by omega)).trans h3,(ho 5 (by omega)).trans h5,(ho 6 (by omega)).trans h6,
    (ho 8 (by omega)).trans h8⟩

def Data (u c v : ℕ) (a : Fin 50 → List Bool) : Prop :=
  Original u c v a ∧ a 10=UnaryTemplate.tape (v-u) ∧
  a 12=UnaryTemplate.tape (natBitLength v-natBitLength u) ∧
  a 22=UnaryTemplate.tape (u*c) ∧ a 32=UnaryTemplate.tape ((v-u)*c) ∧
  a 42=UnaryTemplate.tape ((v-u)*natBitLength v) ∧ a 46=UnaryTemplate.tape u ∧ a 48=natWord v
def budget (u c v : ℕ) :=
  8*u*c+8*(v-u)*c+8*(v-u)*natBitLength v+14*u+20*(v-u)+2*v+12*natBitLength v+138

theorem preparation_ready (u c v : ℕ) (huv : u ≤ v) :
    ∃ a, ReadyRun machine (budget u c v) (input u c v) a ∧ Data u c v a := by
  have hw : natBitLength u ≤ natBitLength v := Nat.add_le_add_right (Nat.log_mono_right huv) 1
  obtain ⟨a1,r1,o1,h15,h16,h18,b1⟩ := width_ready (input u c v) (natBitLength v) rfl (input_blank u c v)
  have orig1 : Original u c v a1 :=
    ⟨o1 0 (by decide),o1 1 (by decide),o1 2 (by decide),o1 3 (by decide),h15,h16,h18⟩
  obtain ⟨a2,r2,o2,h210,b2⟩ := delta_ready a1 v u huv orig1.2.2.1 orig1.1 b1
  have orig2 := orig1.retain o2 (by decide)
  obtain ⟨a3,r3,o3,h312,b3⟩ := gap_ready a2 (natBitLength v) (natBitLength u) hw
    orig2.2.2.2.2.2.2 orig2.2.2.2.1 b2
  have orig3 := orig2.retain o3 (by decide)
  have h310 := (o3 10 (by decide)).trans h210
  obtain ⟨a4,r4,o4,h422,b4⟩ := used_ready a3 u c orig3.1 orig3.2.1 b3
  have orig4 := orig3.retain o4 (by decide)
  have h410 := (o4 10 (by decide)).trans h310
  obtain ⟨a5,r5,o5,h532,b5⟩ := pad_ready a4 (v-u) c h410 orig4.2.1 b4
  have orig5 := orig4.retain o5 (by decide)
  have h510 := (o5 10 (by decide)).trans h410
  obtain ⟨a6,r6,o6,h642,b6⟩ := tail_ready a5 (v-u) (natBitLength v) h510 orig5.2.2.2.2.2.2 b5
  have orig6 := orig5.retain o6 (by decide)
  have h610 := (o6 10 (by decide)).trans h510
  obtain ⟨a7,r7,o7,h746,b7⟩ := copy_ready a6 u orig6.1 b6
  have orig7 := orig6.retain o7 (by decide)
  have h710 := (o7 10 (by decide)).trans h610
  obtain ⟨a8,r8,o8,h848⟩ := header_ready a7 v orig7.2.2.2.2.1 orig7.2.2.2.2.2.1 b7
  have orig8 := orig7.retain o8 (by decide)
  have t1 := r1.call sizes programs 0 next 0 1 (by intro q; rfl)
  have t2 := r2.call sizes programs 0 next 1 2 (by intro q; rfl)
  have t3 := r3.call sizes programs 0 next 2 3 (by intro q; rfl)
  have t4 := r4.call sizes programs 0 next 3 4 (by intro q; rfl)
  have t5 := r5.call sizes programs 0 next 4 5 (by intro q; rfl)
  have t6 := r6.call sizes programs 0 next 5 6 (by intro q; rfl)
  have t7 := r7.call sizes programs 0 next 6 7 (by intro q; rfl)
  have t8 := r8.stop sizes programs 0 next 7 (by intro q; rfl)
  have ht := t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans t8))))))
  have htime : (4*natBitLength v+12+1)+((2*v+8+1)+((2*natBitLength v+8+1)+
      ((8*u*c+10*u+28+1)+((8*(v-u)*c+10*(v-u)+28+1)+
      ((8*(v-u)*natBitLength v+10*(v-u)+28+1)+((4*u+12+1)+(6*natBitLength v+6+1))))))) = budget u c v := by
    unfold budget
    ring
  rw [htime] at ht
  obtain ⟨actual,hr,hf,hs⟩ := ht.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hi : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) (input u c v)) =
      initialConfiguration machine (input u c v) := by rfl
  rw [hi] at hr
  refine ⟨a8,⟨actual,hr,?_,?_,hs⟩,orig8,(o8 10 (by decide)).trans h710,?_,?_,?_,?_,?_,h848⟩
  · rw [hf]; rfl
  · intro i; rw [hf]; rfl
  · exact (o8 12 (by decide)).trans ((o7 12 (by decide)).trans ((o6 12 (by decide)).trans
      ((o5 12 (by decide)).trans ((o4 12 (by decide)).trans h312))))
  · exact (o8 22 (by decide)).trans ((o7 22 (by decide)).trans ((o6 22 (by decide)).trans
      ((o5 22 (by decide)).trans h422)))
  · exact (o8 32 (by decide)).trans ((o7 32 (by decide)).trans ((o6 32 (by decide)).trans h532))
  · exact (o8 42 (by decide)).trans ((o7 42 (by decide)).trans h642)
  · exact (o8 46 (by decide)).trans h746

end NearCubicWires.RepairOrdinary.WilliamsTemplates
