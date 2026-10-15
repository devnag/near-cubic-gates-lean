import Proof.PCP.PCPTraversalInvariantCombine

/-! Strong induction for the actual balanced serializer controller. Each
recursive child stops at node nine before inspecting its caller's flag. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def subtreeBudget (cap n : ℕ) := 200*(2*n-1)*(cap+1)

theorem subtree_budget_split (cap n l r : ℕ) (hs : l+r=n) (hl : 0<l) (hr : 0<r) :
    11*cap+38+subtreeBudget cap l+(10*cap+29)+subtreeBudget cap r+(24*cap+77)
      ≤ subtreeBudget cap n := by
  have hn : (2*l-1)+(2*r-1)+1=2*n-1 := by omega
  have he : subtreeBudget cap n=subtreeBudget cap l+subtreeBudget cap r+200*(cap+1) := by
    unfold subtreeBudget
    rw [←hn]
    ring
  rw [he]
  omega

theorem stream_split (fields : List (List Bool)) :
    FieldList.stream fields=FieldList.stream (leftFields fields)++FieldList.stream (rightFields fields) := by
  have he := List.take_append_drop (midpoint fields) fields
  have hm := congrArg FieldList.stream he
  simpa only [FieldList.stream,List.map_append,List.flatten_append,leftFields,rightFields] using hm.symm

theorem subtree_run (B n : ℕ) :
    ∀ (fields : List (List Bool)), fields.length=n → 0<n → mass fields≤B →
    ∀ (pre suffix countWord rightStack continuation leftStack : List Bool)
      (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool),
    Stable (PCPPairReusable.capacity B) (pre++FieldList.stream fields++suffix)
      countWord pre.length rightStack continuation leftStack heads tapes →
    CountAt (PCPPairReusable.capacity B) n tapes →
    leftStack.length+n*frameBound B≤PCPPairReusable.capacity B →
    rightStack.length+3*n≤PCPPairReusable.capacity B →
    continuation.length+2*n≤PCPPairReusable.capacity B →
    ∃ outHeads outTapes,
      Path 0 9 (subtreeBudget (PCPPairReusable.capacity B) n) heads tapes outHeads outTapes ∧
      Stable (PCPPairReusable.capacity B) (pre++FieldList.stream fields++suffix)
        countWord (pre.length+(FieldList.stream fields).length)
        rightStack continuation leftStack outHeads outTapes ∧
      outTapes 77=ZeroPadding.pad (PCPPairReusable.capacity B) (frame (code fields).bits) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro fields hlen hn hmass pre suffix countWord rightStack continuation leftStack heads tapes
      st count hleft hright hcont
    let cap := PCPPairReusable.capacity B
    have hnB : n≤B := by have h := (mass_bounds fields).1; omega
    have hcap : 3*n+3≤cap := by have h := capacity_reserves B; omega
    have hBcap : B≤cap := by have h := capacity_reserves B; omega
    have hB : 0<B := by omega
    have hframe : frameBound B+1≤cap := by
      have h := capacity_reserves B
      have hm : frameBound B≤B*frameBound B := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (frameBound B) hB
      omega
    have hpower : B+1≤(B+1)^5 := by
      calc
        B+1=(B+1)^1 := by simp
        _≤(B+1)^5 := pow_le_pow_right₀ (by omega) (by omega)
    by_cases hone : n=1
    · obtain ⟨bits,rfl⟩ := List.length_eq_one_iff.mp (hlen.trans hone)
      subst n
      have hbits : 2*bits.length+1≤B := by
        simpa only [mass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hmass
      have hpair := PCPPairReusable.capacity_covers B (1 : ℕ).bits bits
        (by change 1≤3*(B+1)^5; omega) (by omega)
      have hst : Stable cap (pre++frame bits++suffix) countWord pre.length
          rightStack continuation leftStack heads tapes := by
        simpa only [FieldList.stream,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
          using st
      obtain ⟨h,t,hpath,hstable,hresult⟩ := stable_leaf cap pre bits suffix countWord rightStack continuation leftStack
        heads tapes hst count (by omega) (by omega) hpair
      refine ⟨h,t,hpath.mono ?_,?_,?_⟩
      · simp only [subtreeBudget]
        omega
      · simpa only [FieldList.stream,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
          frame_length,Nat.add_assoc] using hstable
      · simpa only [code,values,List.map_cons,List.map_nil,CanonicalBinary.encodeBalancedList] using hresult
    · have htwo : 2≤fields.length := by omega
      obtain ⟨hlpos,hrpos,hlt,hrt,hsum,hrhalf⟩ := split_lengths fields htwo
      have hlhalf : (leftFields fields).length=(n+1)/2 := by omega
      have hlsmall : (leftFields fields).length<n := by omega
      have hrsmall : (rightFields fields).length<n := by omega
      have hsumN : (leftFields fields).length+(rightFields fields).length=n := by omega
      have hrhalfN : (rightFields fields).length=n/2 := by omega
      have hm := split_mass fields (midpoint fields)
      have hml : mass (leftFields fields)≤B := hm.1.trans hmass
      have hmr : mass (rightFields fields)≤B := hm.2.trans hmass
      have hfl := bounded_frame (leftFields fields) B hml
      have hfr := bounded_frame (rightFields fields) B hmr
      have hbl := bounded_code (leftFields fields) B hml
      have hbr := bounded_code (rightFields fields) B hmr
      obtain ⟨hleftNext,hrightNext,hcontLeft,hcontRight⟩ := split_reserves B n
        (leftFields fields).length (rightFields fields).length leftStack.length rightStack.length continuation.length
        hsumN hlpos hrpos hleft hright hcont
      obtain ⟨h₁,t₁,p₁,s₁,c₁⟩ := stable_descend cap n pre.length
        (pre++FieldList.stream fields++suffix) countWord rightStack continuation leftStack heads tapes st count
        (by omega) hcap (by omega) (by omega)
      have sl : Stable cap
          (pre++FieldList.stream (leftFields fields)++(FieldList.stream (rightFields fields)++suffix))
          countWord pre.length
          (rightStack++(frame (List.replicate (rightFields fields).length true)).reverse)
          (continuation++[false,true]) leftStack h₁ t₁ := by
        simpa only [stream_split fields,List.append_assoc,hrhalfN] using s₁
      have cl : CountAt cap (leftFields fields).length t₁ := by simpa only [hlhalf] using c₁
      obtain ⟨h₂,t₂,p₂,s₂,c₂⟩ := ih (leftFields fields).length hlsmall (leftFields fields) rfl hlpos hml
        pre (FieldList.stream (rightFields fields)++suffix) countWord
        (rightStack++(frame (List.replicate (rightFields fields).length true)).reverse)
        (continuation++[false,true]) leftStack h₁ t₁ sl cl
        (by have hm := Nat.mul_le_mul_right (frameBound B) (Nat.le_of_lt hlsmall); omega)
        (by simpa only [List.length_append,List.length_reverse,frame_length,List.length_replicate,Nat.add_assoc]
              using hrightNext)
        (by simpa only [List.length_append,List.length_cons,List.length_nil] using hcontLeft)
      have sr : Stable cap (pre++FieldList.stream fields++suffix) countWord
          (pre.length+(FieldList.stream (leftFields fields)).length)
          (rightStack++(frame (List.replicate (rightFields fields).length true)).reverse)
          (continuation++[false,true]) leftStack h₂ t₂ := by
        simpa only [stream_split fields,List.append_assoc] using s₂
      obtain ⟨h₃,t₃,p₃,s₃,c₃⟩ := stable_resume cap (rightFields fields).length
        (pre.length+(FieldList.stream (leftFields fields)).length)
        (pre++FieldList.stream fields++suffix) countWord rightStack continuation leftStack
        (code (leftFields fields)).bits h₂ t₂ sr (by omega)
        (by rw [frame_length] at hfl; omega) c₂
      have ss : Stable cap
          ((pre++FieldList.stream (leftFields fields))++FieldList.stream (rightFields fields)++suffix)
          countWord (pre++FieldList.stream (leftFields fields)).length rightStack (continuation++[true,true])
          (leftStack++(frame (code (leftFields fields)).bits).reverse) h₃ t₃ := by
        simpa only [stream_split fields,List.append_assoc,List.length_append] using s₃
      obtain ⟨h₄,t₄,p₄,s₄,c₄⟩ := ih (rightFields fields).length hrsmall (rightFields fields) rfl hrpos hmr
        (pre++FieldList.stream (leftFields fields)) suffix countWord rightStack (continuation++[true,true])
        (leftStack++(frame (code (leftFields fields)).bits).reverse) h₃ t₃ ss c₃
        (by simp only [List.length_append,List.length_reverse]; omega)
        (by omega)
        (by simpa only [List.length_append,List.length_cons,List.length_nil] using hcontRight)
      have sc : Stable cap (pre++FieldList.stream fields++suffix) countWord
          (pre.length+(FieldList.stream fields).length) rightStack (continuation++[true,true])
          (leftStack++(frame (code (leftFields fields)).bits).reverse) h₄ t₄ := by
        simpa only [stream_split fields,List.append_assoc,List.length_append,Nat.add_assoc] using s₄
      have hpair := PCPPairReusable.capacity_covers B (code (leftFields fields)).bits (code (rightFields fields)).bits hbl hbr
      have htag := PCPPairReusable.capacity_covers B (2 : ℕ).bits
        (Nat.pair (code (leftFields fields)) (code (rightFields fields))).bits
        (by change 2≤3*(B+1)^5; omega) (bounded_inner fields B hmass htwo)
      have hp : 0<Nat.pair (RadixSemantics.value (code (leftFields fields)).bits)
          (RadixSemantics.value (code (rightFields fields)).bits) := by
        rw [CanonicalPositiveOutput.nat_bits_value,CanonicalPositiveOutput.nat_bits_value]
        exact (positive_code (leftFields fields) hlpos).trans_le (Nat.left_le_pair _ _)
      obtain ⟨h₅,t₅,p₅,s₅,c₅⟩ := stable_combine cap (pre.length+(FieldList.stream fields).length)
        (pre++FieldList.stream fields++suffix) countWord rightStack continuation leftStack
        (code (leftFields fields)).bits (code (rightFields fields)).bits h₄ t₄ sc (by omega)
        (by rw [frame_length] at hfl; omega) (by rw [frame_length] at hfr; omega) hp hpair
        (by simpa only [CanonicalPositiveOutput.nat_bits_value] using htag) c₄
      refine ⟨h₅,t₅,(((p₁.trans p₂).trans p₃).trans p₄).trans p₅ |>.mono ?_,s₅,?_⟩
      · exact subtree_budget_split cap n (leftFields fields).length (rightFields fields).length hsumN hlpos hrpos
      · simpa only [CanonicalPositiveOutput.nat_bits_value,split_code fields htwo] using c₅

end NearCubicWires.RepairOrdinary.PCPTraversal
