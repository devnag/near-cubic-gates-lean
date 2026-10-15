import Proof.Amplification.RecoveryTseitinGraph

/-! Finite query-prefix state and the exact update of one executed node. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stage_congr (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs more : Fin 6→Fin 39→List Bool)
    (n : Nat) (hn : n ≤ 6) (he : ∀ j : Fin 6,j.val<n → outs j=more j) :
    stage cap ls original outs n=
      stage cap ls original more n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmod : n%6=n := Nat.mod_eq_of_lt (by omega)
    rw [stage,stage,ih (by omega) (by intro j hj; exact he j (by omega)),
      he ⟨n%6,Nat.mod_lt _ (by decide)⟩ (by dsimp; rw [hmod]; omega)]

theorem update_prefix (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool)
    (k : Fin 6) (out : Fin 39→List Bool) :
    stage cap ls original (Function.update outs k out) k.val=
      stage cap ls original outs k.val := by
  apply stage_congr _ _ _ _ _ _ k.isLt.le
  intro j hj
  have hne : j≠k := by intro h; subst j; omega
  simp [hne]

theorem update_successor (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool)
    (k : Fin 6) (out : Fin 39→List Bool) :
    stage cap ls original (Function.update outs k out) (k.val+1)=
      install (cellSlots k) (stage cap ls original outs k.val) out := by
  have he : (⟨k.val%6,Nat.mod_lt _ (by decide)⟩ : Fin 6)=k :=
    Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [stage,he,Function.update_self,update_prefix]

theorem prepared_bounded (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (hcap : capacity ls ≤ cap) :
    Bounded cap (prepared cap ls original) := by
  obtain ⟨_,h02,h03⟩ := cell_capacity ls 0
  obtain ⟨_,h12,h13⟩ := cell_capacity ls 1
  obtain ⟨_,h22,h23⟩ := cell_capacity ls 2
  change 2*(ls 0).1.toNat.bits.length+1 ≤ capacity ls at h02
  change 2*(ls 0).2.bits.length+1 ≤ capacity ls at h03
  change 2*(ls 1).1.toNat.bits.length+1 ≤ capacity ls at h12
  change 2*(ls 1).2.bits.length+1 ≤ capacity ls at h13
  change 2*(ls 2).1.toNat.bits.length+1 ≤ capacity ls at h22
  change 2*(ls 2).2.bits.length+1 ≤ capacity ls at h23
  intro i hi
  simp only [prepared,if_neg (show ¬i.val<5 by omega)]
  split_ifs <;> simp only [ZeroPadding.pad_length,frame_length,List.length_replicate]
  all_goals first | exact Nat.le_refl _ | apply max_le le_rfl
  all_goals omega

def Fields (cap : Nat) (ls : Literals) (n : Nat)
    (outs : Fin 6→Fin 39→List Bool) : Prop :=
  ∀ j : Fin 6,j.val<n → outs j 26=ZeroPadding.pad cap (frame (values ls j).bits)

theorem fields_update (cap : Nat) (ls : Literals)
    (outs : Fin 6→Fin 39→List Bool) (k : Fin 6) (out : Fin 39→List Bool)
    (hf : Fields cap ls k.val outs)
    (ho : out 26=ZeroPadding.pad cap (frame (values ls k).bits)) :
    Fields cap ls (k.val+1) (Function.update outs k out) := by
  intro j hj
  by_cases he : j=k
  · subst j
    simpa using ho
  · have hj' : j.val<k.val := by
      have hne : j.val≠k.val := by intro h; exact he (Fin.ext h)
      omega
    simpa [he] using hf j hj'

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
