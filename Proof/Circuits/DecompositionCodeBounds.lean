import Proof.Circuits.DecompositionAtomBudget

/-! Canonical integer/child code widths from native input bytes, used to
choose one fixed global capacity before any nested serialization. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCodeBounds
open CanonicalBinary RepairRepresentation PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (values : List ℤ) := values.flatMap intWord
def atoms (values : List ℤ) := values.map encodeInt
def child (values : List ℤ) := encodeBalancedList (atoms values)

theorem integer_bits (z : ℤ) : (encodeInt z).bits.length ≤ 10*(natBitLength z.natAbs+1)^5 := by
  have h := PCPPair.pair_bound [decide (z<0)] (encodeNat z.natAbs).bits
  rw [DecompositionSignedPair.int_pair] at h
  have hn := (Nat.size_eq_bits_len (encodeInt z)).le.trans (Nat.size_le.mpr h)
  have hm := DecompositionAtom.magnitude_bits z.natAbs
  have hp : 1≤(natBitLength z.natAbs+1)^5 := Nat.one_le_pow 5 _ (by omega)
  simp only [PCPPair.width,List.length_cons,List.length_nil] at hn
  omega

theorem integer_width (z : ℤ) : natBitLength (encodeInt z) ≤ 11*(natBitLength z.natAbs+1)^5 := by
  have h := value_width (encodeInt z).bits
  rw [CanonicalPositiveOutput.nat_bits_value] at h
  have hb := integer_bits z
  have hp : 1≤(natBitLength z.natAbs+1)^5 := Nat.one_le_pow 5 _ (by omega)
  omega

theorem native_count (values : List ℤ) : values.length ≤ (native values).length := by
  induction values with
  | nil => rfl
  | cons z values ih =>
    simp only [native,List.flatMap_cons,List.length_append,DecompositionSource.intWord_length,
      List.length_cons] at ih ⊢
    omega

theorem native_member (values : List ℤ) (z : ℤ) (hz : z∈values) :
    natBitLength z.natAbs ≤ (native values).length := by
  induction values with
  | nil => simp at hz
  | cons a values ih =>
    simp only [List.mem_cons] at hz
    simp only [native,List.flatMap_cons,List.length_append,DecompositionSource.intWord_length]
    rcases hz with hz|hz
    · subst a
      change natBitLength z.natAbs ≤ 2*natBitLength z.natAbs+2+(values.flatMap intWord).length
      omega
    · have h := ih hz
      change natBitLength z.natAbs ≤ (values.flatMap intWord).length at h
      omega

theorem sum_bound {α : Type} (values : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x∈values,f x≤B) : (values.map f).sum ≤ values.length*B := by
  induction values with
  | nil => simp
  | cons a values ih =>
    have ha := h a (by simp)
    have ht := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem atom_mass (values : List ℤ) (N : ℕ) (hN : (native values).length≤N) :
    mass (values.map (fun z => (encodeInt z).bits)) ≤ 21*(N+1)^6 := by
  have hc := (native_count values).trans hN
  have hp : 1≤(N+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have hs := sum_bound values (fun z => 2*(encodeInt z).bits.length+1) (21*(N+1)^5) (by
    intro z hz
    have hw := (native_member values z hz).trans hN
    have hb := (integer_bits z).trans (show 10*(natBitLength z.natAbs+1)^5 ≤ 10*(N+1)^5 by gcongr)
    omega)
  have hm : values.length*(21*(N+1)^5) ≤ 21*(N+1)^6 := by
    calc
      _ ≤ (N+1)*(21*(N+1)^5) := by gcongr; omega
      _ = _ := by ring
  simpa only [mass,List.map_map,Function.comp_def] using hs.trans hm

theorem child_width (values : List ℤ) (N : ℕ) (hN : (native values).length≤N) :
    natBitLength (child values) ≤ 25*(N+1)^10 := by
  have hc := (native_count values).trans hN
  have hs := sum_bound values (fun z => natBitLength (encodeInt z)) (11*(N+1)^5) (by
    intro z hz
    have hw := (native_member values z hz).trans hN
    exact (integer_width z).trans (by gcongr))
  have hs' : ((atoms values).map natBitLength).sum ≤ 11*(N+1)^6 := by
    have hm : values.length*(11*(N+1)^5) ≤ 11*(N+1)^6 := by
      calc
        _ ≤ (N+1)*(11*(N+1)^5) := by gcongr; omega
        _ = _ := by ring
    simpa only [atoms,List.map_map,Function.comp_def] using hs.trans hm
  have hp : 1≤(N+1)^6 := Nat.one_le_pow 6 _ (by omega)
  have hb : balancedListAtomBits (atoms values) ≤ 12*(N+1)^6 := by
    unfold balancedListAtomBits
    omega
  have hcode := balancedListCodeBits_le (atoms values)
  have hcount : (atoms values).length ≤ N+1 := by simpa only [atoms,List.length_map] using hc.trans (Nat.le_succ _)
  have hproduct : 1+2*(atoms values).length^4*balancedListAtomBits (atoms values) ≤
      1+24*(N+1)^10 := by
    calc
      _ ≤ 1+2*(N+1)^4*(12*(N+1)^6) := by gcongr
      _ = _ := by ring
  have hp10 : 1≤(N+1)^10 := Nat.one_le_pow 10 _ (by omega)
  exact hcode.trans (hproduct.trans (by omega))

end NearCubicWires.RepairOrdinary.DecompositionCodeBounds
