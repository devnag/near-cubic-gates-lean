import Proof.CaseAnalysis.ScheduleRefuterInput
import Proof.CaseAnalysis.CommonPrepareLayout

/-! The common ordinary input is literally tape0.  Sparse aliases pass the
retained final address and actual refuter answer to the paid shared preparation;
the live flag and refuter query bank remain outside the preparation workspace. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPrefix
open LocalBitMultitape RepairOrdinary CloseoutSchedule CloseoutRetainedRefuter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def base (w : ℕ) (r : OrdinaryOracleProgram):=CloseoutRetainedRefuter.tapes (Guarded.tapes w) r
def tapes (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ):=1+base w r+CloseoutCommonPrepare.tapes k
instance (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) : NeZero (tapes w r k) :=
  ⟨by unfold tapes; omega⟩
def address (w : ℕ) (r : OrdinaryOracleProgram) : Fin (base w r):=
  old r (RefuterPrefix.addressPort w)
def answer (w : ℕ) (r : OrdinaryOracleProgram) : Fin (base w r):=fresh (Guarded.tapes w) r 0

def firstSlots (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) (j : Fin (base w r)) : Fin (tapes w r k):=
  if j=address w r then 0 else ⟨1+j.val,by have hj:=j.isLt;unfold tapes;omega⟩
def prepareSlots (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ)
    (j : Fin (CloseoutCommonPrepare.tapes k)) : Fin (tapes w r k):=
  if j.val=0 then 0 else if j.val=1 then firstSlots w r k (answer w r)
  else ⟨1+base w r+j.val,by have hj:=j.isLt;unfold tapes;omega⟩
def input (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) (bits : List Bool)
    (i : Fin (tapes w r k)):=if i.val=0 then frame bits else []

theorem address_ne_answer (w : ℕ) (r : OrdinaryOracleProgram) : address w r≠answer w r:=
  old_fresh r (RefuterPrefix.addressPort w) 0

theorem first_injective (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) :
    Function.Injective (firstSlots w r k):=by
  intro i j he
  have hv:=congrArg Fin.val he
  by_cases hi:i=address w r <;> by_cases hj:j=address w r
  · exact hi.trans hj.symm
  · simp [firstSlots,hi,hj] at hv
    omega
  · simp [firstSlots,hi,hj] at hv
  · simp only [firstSlots,if_neg hi,if_neg hj] at hv
    exact Fin.ext (by omega)

theorem first_address (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) :
    firstSlots w r k (address w r)=0:=by simp [firstSlots]

theorem first_answer (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) :
    (firstSlots w r k (answer w r)).val=1+(answer w r).val:=by
  simp only [firstSlots,if_neg (Ne.symm (address_ne_answer w r))]

theorem first_bound (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) (j : Fin (base w r)) :
    (firstSlots w r k j).val<1+base w r:=by
  unfold firstSlots
  split_ifs <;> have hj:=j.isLt <;> dsimp <;>omega

theorem prepare_injective (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) :
    Function.Injective (prepareSlots w r k):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have ha:=first_answer w r k
  have hb:=first_bound w r k (answer w r)
  unfold prepareSlots at hv
  split_ifs at hv <;> simp only [Fin.val_zero] at hv <;> apply Fin.ext <;> omega

theorem initial_first (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) (bits : List Bool)
    (j : Fin (base w r)) :
    input w r k bits (firstSlots w r k j)=
      CloseoutRetainedRefuter.input r (Guarded.input w bits) j:=by
  rw [RefuterPrefix.literal_input]
  by_cases hj:j=address w r
  · subst j
    rw [first_address]
    simp only [input,Fin.val_zero,if_true,address]
  · have hn:j.val≠(address w r).val:=fun h=>hj (Fin.ext h)
    simp only [firstSlots,if_neg hj,input]
    rw [if_neg (by omega : ¬(1+j.val=0))]
    exact (if_neg hn).symm

end
end NearCubicWires.RepairSource.CloseoutCommonPrefix
