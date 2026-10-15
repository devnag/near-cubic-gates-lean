import Proof.Amplification.RecoveryTseitinNativeTautologyReset

/-! The cold tautology workspace lies entirely in the later native scratch
bank. Arity is read at its original raw port and formula output stays live. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tautSlots (i : Fin 263) : Fin 1370 :=
  if i=239 then 1333 else if i=242 then 0 else ⟨i.val+2,by have hi:=i.isLt; omega⟩
theorem taut_injective : Function.Injective tautSlots := by
  intro i j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  dsimp only [tautSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem taut_away (i : Fin 1370) (h0 : i≠0) (h33 : i≠1333) (hi : i.val<2 ∨ 265 ≤ i.val) :
    ∀ j,tautSlots j≠i := by
  intro j he
  have hv:=congrArg Fin.val he
  have hj:=j.isLt
  have hn0 : i.val≠0:=fun h=>h0 (Fin.ext h)
  have hn33 : i.val≠1333:=fun h=>h33 (Fin.ext h)
  dsimp only [tautSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
def tautOld (i : Fin 263) : Fin 1342 := ⟨(tautSlots i).val,by
  dsimp only [tautSlots]
  split_ifs <;> dsimp <;> have hi:=i.isLt <;> omega⟩
theorem taut_old_cast (i : Fin 263) : (tautOld i).castAdd 28=tautSlots i := rfl
theorem taut_old_work (i : Fin 263) : tautOld i≠1336 ∧ tautOld i≠1338 := by
  constructor <;> intro he <;> have hv:=congrArg Fin.val he
  all_goals
    dsimp only [tautOld,tautSlots] at hv
    split_ifs at hv <;> dsimp at hv <;> have hi:=i.isLt <;> omega
theorem taut_input (n count output : Nat) (word : List Bool) (i : Fin 263) :
    input n count output word (tautSlots i)=tautInput n i := by
  refine Fin.addCases (m:=262) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [tautInput,Fin.addCases_left,RecoveryTseitinTautology.Cold.driversInput]
    by_cases h239 : j=239
    · subst j; rfl
    by_cases h242 : j=242
    · subst j; rfl
    have hn239 : j.val≠239:=fun h=>h239 (Fin.ext h)
    have hn242 : j.val≠242:=fun h=>h242 (Fin.ext h)
    have hi:=j.isLt
    rw [if_neg h242]
    have hc239 : j.castAdd 1≠(239 : Fin 263) := by intro he; have hv:=congrArg Fin.val he; exact h239 (Fin.ext hv)
    have hc242 : j.castAdd 1≠(242 : Fin 263) := by intro he; have hv:=congrArg Fin.val he; exact h242 (Fin.ext hv)
    rw [tautSlots,if_neg hc239,if_neg hc242]
    unfold input
    simp only [Fin.ext_iff,Fin.val_castAdd]
    norm_num
    split_ifs <;> first | rfl | omega
  · have hj0 : j=0 := Subsingleton.elim _ _
    subst j
    rfl
theorem taut_capacity (n count : Nat) : RecoveryTseitinTautology.Cold.budget n ≤ Reuse.capacity n count := by
  have hb:=RecoveryTseitinTautology.Cold.budget_bound n
  have hp:=Nat.pow_le_pow_left (show n+1 ≤ n+count+1 by omega) 3
  unfold Reuse.capacity
  omega

def retained (i : Fin 1370) : Prop := i=0 ∨ i=1 ∨ i=1062 ∨ (1336 ≤ i.val ∧ i.val<1342)
def preparedData (n count output : Nat) (word : List Bool) (i : Fin 1370) : List Bool :=
  if i=1336 then List.replicate (Reuse.capacity n count) true else
  if i=1338 then CompareMachine.word count else input n count output word i
theorem retained_bound (i : Fin 1370) (hi : retained i) : i.val<1342 := by
  rcases hi with rfl|rfl|rfl|hi <;> first | decide | exact hi.2
theorem retained_away (i : Fin 1370) (hi : retained i) (h0 : i≠0) : ∀ j,tautSlots j≠i := by
  apply taut_away i h0
  · intro he
    rcases hi with rfl|rfl|rfl|hi <;> simp_all
  · rcases hi with rfl|rfl|rfl|hi <;> omega

theorem native_blank (n count output : Nat) (word : List Bool) (j : Fin 1332) :
    input n count output word ((Reuse.scratch j).castAdd 34)=[] := by
  have hr:=Reuse.scratch_range j
  have hi:=(Reuse.scratch j).isLt
  unfold input
  simp only [Fin.ext_iff,Fin.val_castAdd]
  norm_num
  split_ifs <;> first | rfl | omega

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
