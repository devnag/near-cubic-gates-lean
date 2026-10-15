import Proof.PCP.PCPPNativeCanonicalStackReady
import Proof.Circuits.CanonicalBalancedTraversal

namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
open CanonicalBinary CanonicalBinaryProgram RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tree (code : ℕ) : BalancedTraversalTree :=
  if _h : (Nat.unpair code).1=2 then
    .branch (tree (Nat.unpair (Nat.unpair code).2).1) (tree (Nat.unpair (Nat.unpair code).2).2)
  else if (Nat.unpair code).1=1 then .leaf (Nat.unpair code).2 else .empty
termination_by code
decreasing_by
  all_goals
    have hp:(Nat.unpair code).2<code:=by
      have hs:=Nat.unpair_add_le code
      rw [_h] at hs
      omega
  · exact (Nat.unpair_left_le _).trans_lt hp
  · exact (Nat.unpair_right_le _).trans_lt hp

theorem tree_of_code (t : BalancedTraversalTree) : tree t.code=t := by
  induction t with
  | empty=>rw [tree];rfl
  | leaf a=>
    change tree (Nat.pair 1 a)=_
    rw [tree]
    simp
  | branch l r hl hr=>
    change tree (Nat.pair 2 (Nat.pair l.code r.code))=_
    rw [tree]
    simp [hl,hr]

theorem tree_nodes (code : ℕ) : (tree code).nodeCount≤natBitLength code := by
  induction code using Nat.strong_induction_on with
  | h code ih=>
    rw [tree]
    split_ifs with ht hl
    · have hp:(Nat.unpair code).2<code:=by
        have hs:=Nat.unpair_add_le code
        rw [ht] at hs
        omega
      have hleft:=ih _ ((Nat.unpair_left_le _).trans_lt hp)
      have hright:=ih _ ((Nat.unpair_right_le _).trans_lt hp)
      have hb:=branch_weight (Nat.unpair (Nat.unpair code).2).1 (Nat.unpair (Nat.unpair code).2).2
      have he:code=Nat.pair 2 (Nat.pair (Nat.unpair (Nat.unpair code).2).1 (Nat.unpair (Nat.unpair code).2).2):=by
        rw [Nat.pair_unpair,←ht,Nat.pair_unpair]
      rw [←he] at hb
      change 1+_+_≤_
      omega
    · change 1≤natBitLength code
      unfold natBitLength
      omega
    · change 1≤natBitLength code
      unfold natBitLength
      omega

theorem tree_atoms (values : List ℕ) : (tree (encodeBalancedList values)).atoms=values := by
  rw [←balancedTraversalTree_code,tree_of_code,balancedTraversalTree_atoms]

theorem tree_canonical_iff (code : ℕ) :
    encodeBalancedList (tree code).atoms=code ↔ ∃ values,encodeBalancedList values=code := by
  constructor
  · intro h;exact ⟨(tree code).atoms,h⟩
  · rintro ⟨values,rfl⟩
    rw [tree_atoms]

theorem word_weight (bits : List Bool) : natBitLength (value bits)≤bits.length+1 := by
  by_cases hz:value bits=0
  · simp [hz,natBitLength]
  · have hp:=Nat.log_lt_of_lt_pow hz (value_lt bits)
    unfold natBitLength
    omega

theorem nonempty_word_weight (bits : List Bool) (hz:value bits≠0) :
    natBitLength (value bits)≤bits.length := by
  have hp:=Nat.log_lt_of_lt_pow hz (value_lt bits)
  unfold natBitLength
  omega

theorem word_nodes (bits : List Bool) : (tree (value bits)).nodeCount≤bits.length+1 :=
  (tree_nodes _).trans (word_weight bits)

theorem nonempty_word_nodes (bits : List Bool) (hz:value bits≠0) :
    (tree (value bits)).nodeCount≤bits.length :=
  (tree_nodes _).trans (nonempty_word_weight bits hz)

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
