import Proof.CaseAnalysis.CaseTwoParity

/-! The existing masked-parity argument specialized to the explicit mask
returned by the original PCPP support reader. The order change is justified
by counting selected true positions modulo two. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Parity
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem fold_xor_count {α : Type} (select : α→Bool) (elements : List α) (acc : Bool) :
    elements.foldl (fun b x=>xor b (select x)) acc=xor acc (decide (Odd (elements.countP select))):=by
  induction elements generalizing acc with
  | nil=>simp
  | cons head tail ih=>
    rw [List.foldl_cons,ih,List.countP_cons]
    by_cases hh:select head=true
    · rcases Nat.mod_two_eq_zero_or_one (tail.countP select) with hp|hp
      · cases acc <;>simp [hh,Nat.odd_add_one,Nat.odd_iff,hp]
      · cases acc <;>simp [hh,Nat.odd_add_one,Nat.odd_iff,hp]
    · simp only [Bool.not_eq_true] at hh
      simp [hh]

private theorem support_perm {n : ℕ} (support : Finset (Fin n)) :
    support.toList.Perm ((List.finRange n).filter fun i=>decide (i∈support)):=by
  have he:support=(Finset.univ.filter fun i=>i∈support):=by ext i;simp
  conv_lhs=>rw [he]
  rw [←Multiset.coe_eq_coe,Finset.coe_toList,Finset.filter_val]
  change Multiset.filter (fun i=>i∈support) (↑(List.finRange n))=_
  rw [Multiset.filter_coe]

theorem fold_support {n : ℕ} (support : Finset (Fin n)) (u : BitInput n) :
    fold (List.ofFn fun i : Fin n=>(decide (i∈support),u i)) false=parityOn support u:=by
  unfold fold parityOn
  rw [List.ofFn_eq_map,List.foldl_map]
  change (List.finRange n).foldl (fun b i=>xor b (decide (i∈support)&&u i)) false=_
  rw [fold_xor_count,fold_xor_count]
  congr 2
  rw [(support_perm support).countP_eq u,List.countP_filter]
  simp only [Bool.and_comm]

theorem systematic_run {n : ℕ} (support : Finset (Fin n)) (u : BitInput n) : ∃ out,
    ClockJoin.ReadyRun machine (2*n+6)
      ![List.replicate n true,List.ofFn (fun i : Fin n=>decide (i∈support)),List.ofFn u,[],[]] out ∧
      out 3=[parityOn support u]:=by
  obtain ⟨out,hr,ht⟩:=parity_run (List.ofFn fun i : Fin n=>(decide (i∈support),u i))
  have hi:input (List.ofFn fun i : Fin n=>(decide (i∈support),u i))=
      ![List.replicate n true,List.ofFn (fun i : Fin n=>decide (i∈support)),List.ofFn u,[],[]]:=by
    funext i;fin_cases i <;>simp [input,List.map_ofFn,Function.comp_def]
  rw [hi,List.length_ofFn] at hr
  exact ⟨out,hr,ht.trans (congrArg (fun b=>[b]) (fold_support support u))⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Parity
