import Proof.PCP.PCPPNativeCanonicalTreeHead

/-! Actual balanced-code descent pays for both queued children in binary
width. This applies to malformed trees too: the ordinary traversal cannot
expand exponentially, and needs no supplied node count or clock. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
open CanonicalBinary RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pair_branch_square (p : ℕ) : p^2≤Nat.pair 2 p := by
  unfold Nat.pair
  split <;> nlinarith

theorem pair_branch_product (a b : ℕ) :
    4*max 1 a*max 1 b≤Nat.pair 2 (Nat.pair a b) := by
  have hs:=pair_branch_square (Nat.pair a b)
  by_cases ha:a=0
  · subst a
    by_cases hb:b=0
    · subst b;decide
    · have hbpos:1≤b:=by omega
      rw [max_eq_right hbpos]
      simp only [max_eq_left (by omega : 0≤1)]
      by_cases hbo:b=1
      · subst b;decide
      · have hb2:2≤b:=by omega
        have hp:Nat.pair 0 b=b^2:=by simp [Nat.pair,show 0<b by omega,pow_two]
        rw [hp] at hs ⊢
        have h1:2*b≤b^2:=by nlinarith
        have h2:2≤b^2:=by nlinarith
        have hm:=Nat.mul_le_mul h1 h2
        nlinarith
  · have hapos:1≤a:=by omega
    by_cases hb:b=0
    · subst b
      rw [max_eq_right hapos]
      simp only [max_eq_left (by omega : 0≤1)]
      have hp:Nat.pair a 0=a^2+a:=by simp [Nat.pair,pow_two]
      rw [hp] at hs ⊢
      have h1:2*a≤a^2+a:=by nlinarith
      have h2:2≤a^2+a:=by nlinarith
      have hm:=Nat.mul_le_mul h1 h2
      nlinarith
    · have hbpos:1≤b:=by omega
      rw [max_eq_right hapos,max_eq_right hbpos]
      have hp:(a+1)*(b+1)≤Nat.pair a b+1:=by
        unfold Nat.pair
        split <;> nlinarith
      have hprod:(a+b)^2≤(Nat.pair a b)^2:=by gcongr;nlinarith
      nlinarith [sq_nonneg ((a:ℤ)-b)]

theorem bits_pow_upper (n : ℕ) : 2^natBitLength n≤2*max 1 n := by
  by_cases hz:n=0
  · subst n;simp [natBitLength]
  · have hp:=Nat.pow_log_le_self 2 hz
    rw [natBitLength,pow_succ,max_eq_right (by omega : 1≤n)]
    omega

theorem branch_weight (a b : ℕ) :
    natBitLength a+natBitLength b+1≤natBitLength (Nat.pair 2 (Nat.pair a b)) := by
  have hp:2^(natBitLength a+natBitLength b+1)≤2*Nat.pair 2 (Nat.pair a b):=by
    rw [pow_succ,pow_add]
    calc
      _≤(2*max 1 a)*(2*max 1 b)*2:=by gcongr;exact bits_pow_upper a;exact bits_pow_upper b
      _=8*max 1 a*max 1 b:=by ring
      _≤_:=by have h:=pair_branch_product a b;nlinarith
  have hc:Nat.pair 2 (Nat.pair a b)<2^natBitLength (Nat.pair 2 (Nat.pair a b)):=
    Nat.lt_pow_succ_log_self (by omega) _
  by_contra h
  have hle:=pow_le_pow_right₀ (by omega : 1≤(2:ℕ))
    (show natBitLength (Nat.pair 2 (Nat.pair a b))+1≤natBitLength a+natBitLength b+1 by omega)
  rw [pow_succ] at hle
  omega

def todoWeight (todo : List ℕ) := (todo.map natBitLength).sum
def descend (code : ℕ) (todo : List ℕ) :=
  if (Nat.unpair code).1=2 then
    (Nat.unpair (Nat.unpair code).2).1::(Nat.unpair (Nat.unpair code).2).2::todo
  else todo

theorem descend_decreases (code : ℕ) (todo : List ℕ) :
    todoWeight (descend code todo)+1≤todoWeight (code::todo) := by
  unfold descend
  split_ifs with htag
  · have hpair:code=Nat.pair 2 (Nat.pair (Nat.unpair (Nat.unpair code).2).1 (Nat.unpair (Nat.unpair code).2).2):=by
      rw [Nat.pair_unpair,←htag,Nat.pair_unpair]
    have hb:=branch_weight (Nat.unpair (Nat.unpair code).2).1 (Nat.unpair (Nat.unpair code).2).2
    rw [←hpair] at hb
    simp only [todoWeight,List.map_cons,List.sum_cons]
    omega
  · have hp:1≤natBitLength code:=by unfold natBitLength;omega
    simp only [todoWeight,List.map_cons,List.sum_cons]
    omega

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
