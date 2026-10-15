import Proof.Amplification.RecoveryQueryGraph

/-! Finite query-prefix state and the exact update of one executed node. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stage_congr (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs more : Fin 9→Fin 39→List Bool)
    (n : Nat) (hn : n ≤ 9) (he : ∀ j : Fin 9,j.val<n → outs j=more j) :
    stage cap flat payload committed count original outs n=
      stage cap flat payload committed count original more n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmod : n%9=n := Nat.mod_eq_of_lt (by omega)
    rw [stage,stage,ih (by omega) (by intro j hj; exact he j (by omega)),
      he ⟨n%9,Nat.mod_lt _ (by decide)⟩ (by dsimp; rw [hmod]; omega)]

theorem update_prefix (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool)
    (k : Fin 9) (out : Fin 39→List Bool) :
    stage cap flat payload committed count original (Function.update outs k out) k.val=
      stage cap flat payload committed count original outs k.val := by
  apply stage_congr _ _ _ _ _ _ _ _ _ k.isLt.le
  intro j hj
  have hne : j≠k := by intro h; subst j; omega
  simp [hne]

theorem update_successor (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool)
    (k : Fin 9) (out : Fin 39→List Bool) :
    stage cap flat payload committed count original (Function.update outs k out) (k.val+1)=
      install (cellSlots k) (stage cap flat payload committed count original outs k.val) out := by
  have he : (⟨k.val%9,Nat.mod_lt _ (by decide)⟩ : Fin 9)=k :=
    Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [stage,he,Function.update_self,update_prefix]

theorem prepared_bounded (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (hcap : capacity payload committed count ≤ cap) :
    Bounded cap (prepared cap flat payload committed count original) := by
  have hbase : bytes payload committed count+1 ≤ (bytes payload committed count+1)^2 := by nlinarith
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hflat : flat.toNat.bits.length ≤ 1 := by cases flat <;> decide
  unfold capacity bytes at hcap hbase hpos
  intro i hi
  simp only [prepared,if_neg (show ¬i.val<5 by omega)]
  split_ifs <;> simp only [ZeroPadding.pad_length,frame_length,List.length_replicate]
  all_goals first | exact Nat.le_refl _ | apply max_le le_rfl
  all_goals first | change 3 ≤ cap; omega | omega

def Fields (cap : Nat) (flat : Bool) (payload committed count n : Nat)
    (outs : Fin 9→Fin 39→List Bool) : Prop :=
  ∀ j : Fin 9,j.val<n → outs j 26=ZeroPadding.pad cap (frame (values flat payload committed count j).bits)

theorem fields_update (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (outs : Fin 9→Fin 39→List Bool) (k : Fin 9) (out : Fin 39→List Bool)
    (hf : Fields cap flat payload committed count k.val outs)
    (ho : out 26=ZeroPadding.pad cap (frame (values flat payload committed count k).bits)) :
    Fields cap flat payload committed count (k.val+1) (Function.update outs k out) := by
  intro j hj
  by_cases he : j=k
  · subst j
    simpa using ho
  · have hj' : j.val<k.val := by
      have hne : j.val≠k.val := by intro h; exact he (Fin.ext h)
      omega
    simpa [he] using hf j hj'

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
