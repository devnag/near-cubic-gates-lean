import Proof.CaseAnalysis.RowsBankPorts
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds

/-! The shared enumeration width comes from the actual canonical polynomial
support and degree. It is not an independently supplied monomial envelope. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSourceDigits
open SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem support_bound {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) (d : ℕ)
    (hd : P.totalDegree ≤ d) : P.support.card ≤ (B+1)^d := by
  classical
  let encode (m : ↥P.support) : Sym (Option (Fin B)) d :=
    ⟨(Finsupp.toMultiset m.val).map some +
        Multiset.replicate (d-(Finsupp.toMultiset m.val).card) none,by
      have hm : (Finsupp.toMultiset m.val).card ≤ d := by
        rw [Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree m.property).trans hd
      simp only [Multiset.card_add,Multiset.card_map,Multiset.card_replicate]
      omega⟩
  have hinj : Function.Injective encode := by
    intro a b he
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have hc := congrArg (fun m : Sym (Option (Fin B)) d=>m.val.count (some i)) he
    simpa [encode,Multiset.count_replicate,
      Multiset.count_map_eq_count' some _ (Option.some_injective _),Finsupp.count_toMultiset] using hc
  have hc := Fintype.card_le_of_injective encode hinj
  have hs : Fintype.card (Sym (Option (Fin B)) d)=(B+d).choose d := by
    rw [Sym.card_sym_eq_choose]
    simp
  rw [hs] at hc
  simpa using hc.trans (Nat.choose_add_le_add_one_pow B d)

noncomputable def rows {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) : List (List Bool) :=
  (polynomialMonomialOccurrences P).map fun m=>List.ofFn (fun i : Fin B=>decide (i∈m))

theorem rows_length {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) :
    (rows P).length=P.support.card := by
  simp [rows,polynomialMonomialOccurrences]

theorem row_length {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2))
    (row : List Bool) (hr : row∈rows P) : row.length=B := by
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp hr
  simp

noncomputable def bank {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2))) := ps.map rows
noncomputable def degree {B : ℕ} : List (MvPolynomial (Fin B) (ZMod 2))→ℕ
  | []=>0
  | P::ps=>max P.totalDegree (degree ps)
noncomputable def width {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2))) :=
  1+degree ps*Nat.clog 2 (B+1)

theorem degree_le {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (P : MvPolynomial (Fin B) (ZMod 2)) (hP : P∈ps) : P.totalDegree ≤ degree ps := by
  induction ps with
  | nil => simp at hP
  | cons A ps ih =>
    rcases List.mem_cons.mp hP with rfl | hP
    · exact Nat.le_max_left _ _
    · exact (ih hP).trans (Nat.le_max_right _ _)

theorem binary_support {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (P : MvPolynomial (Fin B) (ZMod 2)) (hP : P∈ps) :
    (rows P).length ≤ 2^(degree ps*Nat.clog 2 (B+1)) := by
  rw [rows_length]
  calc
    _ ≤ (B+1)^degree ps := support_bound P _ (degree_le ps P hP)
    _ ≤ (2^Nat.clog 2 (B+1))^degree ps :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = _ := by rw [←pow_mul,Nat.mul_comm]

theorem bank_width {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2))) :
    ∀ rs∈bank ps,rs.length<2^width ps := by
  intro rs hrs
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hrs
  have h:=binary_support ps P hP
  have he : 0 < 2^(degree ps*Nat.clog 2 (B+1)) := by positivity
  dsimp [width]
  rw [pow_add]
  norm_num
  omega

def load (K d B : ℕ) := K+Nat.clog 2 (K+2)+(K+1)*d*Nat.clog 2 (B+1)+1

theorem digit_load {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2))) (K : ℕ) :
    K+width ps*(K+2) ≤ 2*load K (degree ps) B := by
  unfold width load
  nlinarith [Nat.zero_le (K*degree ps*Nat.clog 2 (B+1))]

theorem digit_margin {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (K s : ℕ) (hload : 200*load K (degree ps) B ≤ s) :
    100*(K+width ps*(K+2)) ≤ s := by
  have h:=digit_load ps K
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsSourceDigits
