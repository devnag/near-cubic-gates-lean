import Proof.CaseAnalysis.WitnessAliases

/-! Choose redundant clause-address bits by finite averaging. The selected
restriction has no larger error and leaves the actual source occurrence count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Padding
open SourceInterfaces OuterPCPRecovery ExecutableInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (x : BitInput (n+c+1)) : BitInput (n+r+1) := fun i=>
  if hp : i.val<n+c then x ⟨i.val,by omega⟩
  else if hr : i.val<n+r then padding ⟨i.val-(n+c),by omega⟩
  else x ⟨n+c,by omega⟩
def extra {n c r : ℕ} (h : c ≤ r) (x : BitInput (n+r+1)) : BitInput (r-c) :=
  fun i=>x ⟨n+c+i.val,by omega⟩

theorem project_extend {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (x : BitInput (n+c+1)) : projectPaddedOccurrenceInput h (extend h padding x)=x := by
  funext i
  unfold projectPaddedOccurrenceInput extend
  by_cases hi:i.val<n+c
  · simp only [hi,↓reduceDIte]
  · have he:i.val=n+c:=by omega
    simp only [hi,↓reduceDIte,show ¬n+r<n+c by omega,lt_self_iff_false]
    exact congrArg x (Fin.ext he.symm)

theorem extra_extend {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (x : BitInput (n+c+1)) : extra h (extend h padding x)=padding := by
  funext i
  simp only [extra,extend,show ¬n+c+i.val<n+c by omega,
    show n+c+i.val<n+r by omega,↓reduceDIte]
  apply congrArg padding
  apply Fin.ext
  change n+c+i.val-(n+c)=i.val
  omega

theorem extend_projections {n c r : ℕ} (h : c ≤ r) (x : BitInput (n+r+1)) :
    extend h (extra h x) (projectPaddedOccurrenceInput h x)=x := by
  funext i
  unfold extend
  by_cases hp:i.val<n+c
  · simp only [hp,↓reduceDIte,projectPaddedOccurrenceInput]
  · simp only [hp,↓reduceDIte]
    by_cases hr:i.val<n+r
    · simp only [hr,↓reduceDIte,extra]
      apply congrArg x
      apply Fin.ext
      change n+c+(i.val-(n+c))=i.val
      omega
    · simp only [hr,↓reduceDIte,projectPaddedOccurrenceInput,lt_self_iff_false]
      apply congrArg x
      apply Fin.ext
      change n+r=i.val
      omega

def cubeEquiv (n c r : ℕ) (h : c ≤ r) :
    BitInput (r-c) × BitInput (n+c+1) ≃ BitInput (n+r+1) where
  toFun parts:=extend h parts.1 parts.2
  invFun x:=(extra h x,projectPaddedOccurrenceInput h x)
  left_inv:=by
    intro parts
    change (extra h (extend h parts.1 parts.2),projectPaddedOccurrenceInput h (extend h parts.1 parts.2))=parts
    rw [extra_extend,project_extend]
  right_inv:=extend_projections h

theorem distance_expect {n : ℕ} (f : BoolFunction n) (g : BitInput n→ℝ) :
    l1DistanceFromBoolean f g=𝔼 x,|g x-bitAsReal (f x)| := by
  rw [Finset.expect_eq_sum_div_card]
  rfl

theorem distance_average {n c r : ℕ} (h : c ≤ r) (f : BoolFunction (n+c+1))
    (g : BitInput (n+r+1)→ℝ) :
    l1DistanceFromBoolean (fun x=>f (projectPaddedOccurrenceInput h x)) g=
      𝔼 padding : BitInput (r-c),l1DistanceFromBoolean f (fun x=>g (extend h padding x)) := by
  classical
  simp_rw [distance_expect]
  have he:=Fintype.expect_equiv (cubeEquiv n c r h)
    (fun parts=>|g (extend h parts.1 parts.2)-bitAsReal (f parts.2)|)
    (fun x=>|g x-bitAsReal (f (projectPaddedOccurrenceInput h x))|)
    (by intro parts;simp only [cubeEquiv,Equiv.coe_fn_mk,project_extend])
  rw [←he,←Finset.univ_product_univ,Finset.expect_product]

theorem exists_restriction {n c r : ℕ} (h : c ≤ r) (f : BoolFunction (n+c+1))
    (g : BitInput (n+r+1)→ℝ) : ∃ padding : BitInput (r-c),
    l1DistanceFromBoolean f (fun x=>g (extend h padding x))≤
      l1DistanceFromBoolean (fun x=>f (projectPaddedOccurrenceInput h x)) g := by
  classical
  obtain ⟨padding,_,hp⟩:=Finset.exists_le_of_expect_le (s:=Finset.univ)
    Finset.univ_nonempty (distance_average h f g).symm.le
  exact ⟨padding,hp⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.Padding
