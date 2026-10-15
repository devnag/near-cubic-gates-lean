import Proof.CaseAnalysis.CaseTwoXorInit

/-! A finite sequence of fixed ordinary workers. Each next copy receives a
fresh bank and the same three retained words plus the running XOR bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FixedFold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (t : ℕ) : ℕ→ℕ
  | 0=>4
  | n+1=>tapes t n+t
theorem tapes_lower (t n : ℕ) : 4≤tapes t n:=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [tapes];omega
def low (t n : ℕ) (i : Fin 4) : Fin (tapes t n):=⟨i.val,by have hi:=i.isLt;have ht:=tapes_lower t n;omega⟩
def previousSlots (t n : ℕ) (i : Fin (tapes t n)) : Fin (tapes t (n+1)):=i.castAdd t
def fresh (t n : ℕ) (i : Fin t) : Fin (tapes t (n+1)):=i.natAdd (tapes t n)
def ports {t : ℕ} (acc : Fin t) (ha : 3≤acc.val) (i : Fin 3) : Fin t:=
  ⟨i.val,by have hi:=i.isLt;have hb:=acc.isLt;omega⟩
def slots {t : ℕ} (acc : Fin t) (n : ℕ) (j : Fin t) : Fin (tapes t (n+1)):=
  ⟨if j.val<3 then j.val else if j.val=acc.val then 3 else tapes t n+j.val,
    by have hj:=j.isLt;have hb:=tapes_lower t n;dsimp only [tapes];split_ifs <;>omega⟩
theorem prefix_injective (t n : ℕ) : Function.Injective (previousSlots t n):=by
  intro i j he;exact Fin.ext (congrArg (fun x : Fin (tapes t (n+1))=>x.val) he)
theorem slots_injective {t : ℕ} (acc : Fin t) (n : ℕ) : Function.Injective (slots acc n):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have hb:=tapes_lower t n
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;>omega
theorem prefix_low (t n : ℕ) (i : Fin 4) : previousSlots t n (low t n i)=low t (n+1) i:=rfl
theorem slots_port {t : ℕ} (acc : Fin t) (ha : 3≤acc.val) (n : ℕ) (i : Fin 3) :
    slots acc n (ports acc ha i)=low t (n+1) (i.castAdd 1):=by
  apply Fin.ext
  change (if i.val<3 then i.val else if i.val=acc.val then 3 else _)=i.val
  rw [if_pos i.isLt]
theorem slots_acc {t : ℕ} (acc : Fin t) (ha : 3≤acc.val) (n : ℕ) :
    slots acc n acc=low t (n+1) 3:=by
  apply Fin.ext
  change (if acc.val<3 then acc.val else if acc.val=acc.val then 3 else _)=3
  rw [if_neg (by omega),if_pos rfl]
theorem slots_fresh {t : ℕ} (acc : Fin t) (n : ℕ) (j : Fin t) (h3 : ¬j.val<3) (ha : j.val≠acc.val) :
    slots acc n j=fresh t n j:=by
  apply Fin.ext
  change (if j.val<3 then j.val else if j.val=acc.val then 3 else _)=tapes t n+j.val
  rw [if_neg h3,if_neg ha]
theorem fresh_outside (t n : ℕ) (j : Fin t) : ∀ i,previousSlots t n i≠fresh t n j:=by
  intro i he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  change i.val=tapes t n+j.val at hv
  omega
def initial (t n : ℕ) (words : Fin 3→List Bool) (j : Fin (tapes t n)) : List Bool:=
  if h : j.val<3 then words ⟨j.val,h⟩ else []
def bodyInput {t : ℕ} (acc : Fin t) (words : Fin 3→List Bool) (parity : Bool) (j : Fin t) : List Bool:=
  if h : j.val<3 then words ⟨j.val,h⟩ else if j.val=acc.val then [parity] else []
structure Result (t n : ℕ) (words : Fin 3→List Bool) (parity : Bool) (A : Fin (tapes t n)→List Bool) : Prop where
  words : ∀ i : Fin 3,A (low t n (i.castAdd 1))=words i
  parity : A (low t n 3)=[parity]
def states (sizes : ℕ→ℕ) : ℕ→ℕ
  | 0=>2
  | n+1=>states sizes n+sizes n
noncomputable def machine {t : ℕ} (sizes : ℕ→ℕ) (workers : (n : ℕ)→Machine t (sizes n))
    (acc : Fin t) : (n : ℕ)→Machine (tapes t n) (states sizes n)
  | 0=>XorInit.machine
  | n+1=>Composition.machine
      (RecoveryFocus.machine (previousSlots t n) (machine sizes workers acc n))
      (RecoveryFocus.machine (slots acc n) (workers n))
def budget (cost : ℕ→ℕ) : ℕ→ℕ
  | 0=>1
  | n+1=>budget cost n+1+cost n
def value (bit : ℕ→Bool) : ℕ→Bool
  | 0=>false
  | n+1=>xor (value bit n) (bit n)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FixedFold
