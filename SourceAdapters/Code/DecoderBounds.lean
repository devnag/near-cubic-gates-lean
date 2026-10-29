import SourceAdapters.Code.DecoderTypes
import SourceAdapters.Code.LengthPreparation
import SourceAdapters.Code.DecoderRunAlgorithm

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": explicit bounds relating original target words, retained
allocation prefixes, source tuples and decoder-stage packets. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Code DecoderTypes PolynomialCosts

theorem word_length (F : BinaryFamily) {onset : ℕ} (j : Job F onset) :
    (jobWord F j).length = 2 * (jobLength F j).bits.length + 2 * (jobBits F j).length + 2 := by
  simp only [jobWord, List.length_append, frame_length]
  omega

theorem message_le_bits (F : BinaryFamily) (onset : ℕ) (distance : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance) (j : Job F onset) :
    jobLength F j ≤ (jobBits F j).length := by
  cases j with
  | inl p => simp [jobLength, jobBits]
  | inr p =>
    have h0 := source_length_lower F onset distance hd hmin (blockSize p.1 0)
      (blockSize_large onset p.1 p.2.property 0).1
    have h1 := source_length_lower F onset distance hd hmin (blockSize p.1 1)
      (blockSize_large onset p.1 p.2.property 1).1
    have h2 := source_length_lower F onset distance hd hmin (blockSize p.1 2)
      (blockSize_large onset p.1 p.2.property 2).1
    have hs := blockSize_sum p.1
    simp only [jobLength, jobBits, List.length_ofFn, threeBlock]
    omega

theorem decoder_word_length (F : BinaryFamily) (p : TotalSourceRequest F) :
    (decoderInput F p.1 p.2).length = p.1 + F.length p.1 + 1 := by simp [decoderInput]; omega

theorem payload_length (F : BinaryFamily) {onset : ℕ} (j : Job F onset) :
    (payload F (workOf F j)).length ≤ 4 * jobLength F j + 2 * (jobBits F j).length + 13 := by
  cases j with
  | inl p => simp [payload, workOf, jobLength, jobBits, frame_length]; omega
  | inr p =>
    have hs := blockSize_sum p.1
    simp only [payload, workOf, List.length_cons, List.length_append, DecoderRunAlgorithm.packet_length,
      decoderInput, List.length_replicate, jobLength, jobBits, List.length_ofFn, threeBlock]
    omega

theorem source_word_le (F : BinaryFamily) {onset : ℕ} (j : Job F onset)
    (hn : jobLength F j ≤ (jobBits F j).length) (p : TotalSourceRequest F)
    (hp : p ∈ DecoderRunAlgorithm.requests F (workOf F j)) :
    (decoderInput F p.1 p.2).length ≤ (jobWord F j).length := by
  cases j with
  | inl q => simp [workOf, DecoderRunAlgorithm.requests] at hp
  | inr q =>
    simp only [workOf, DecoderRunAlgorithm.requests, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [jobLength, jobBits, List.length_ofFn, threeBlock] at hn
    rw [word_length]
    simp only [jobLength, jobBits, List.length_ofFn, threeBlock]
    rcases hp with rfl | rfl | rfl
    all_goals rw [decoder_word_length]
    all_goals
      have hs := blockSize_sum q.1
      dsimp
      omega

def sizes (onset K e : ℕ) : Sz := ⟨cutoff onset + 100, 1, 1, 1, K, e⟩

def L (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : ℕ := (jobWord F j).length.size

theorem size_lower (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : (jobWord F j).length < 2 ^ L F j :=
  Nat.lt_size_self _

theorem size_upper (F : BinaryFamily) {onset : ℕ} (j : Job F onset) :
    2 ^ L F j ≤ 2 * ((jobWord F j).length + 1) := by
  rw [L, ← Nat.size_eq_bits_len]
  exact Parsing.two_pow_bits_length_le _

theorem width (F : BinaryFamily) {onset : ℕ} (K e : ℕ) (j : Job F onset) :
    20 * ((jobWord F j).length + 1) + cutoff onset + 30 < 2 ^ (sizes onset K e).W (L F j) := by
  have hs := size_lower F j
  have h1 : 1 ≤ 2 ^ L F j := Nat.one_le_pow _ _ (by omega)
  have hc := Nat.mul_le_mul_left (cutoff onset) h1
  have hw : 20 * ((jobWord F j).length + 1) + cutoff onset + 30 ≤ (sizes onset K e).W (L F j) := by
    simp only [sizes, Sz.W, one_mul]
    nlinarith
  exact hw.trans_lt Nat.lt_two_pow_self

theorem prep_capacity (F : BinaryFamily) {onset : ℕ} (K e : ℕ) (j : Job F onset)
    (hn : jobLength F j ≤ (jobBits F j).length) :
    (jobBits F j).length + 2 * jobLength F j + 6 + cutoff onset + 2 ^ (jobLength F j).bits.length <
      2 ^ (sizes onset K e).W (L F j) := by
  have hw := width F K e j
  have hp := Parsing.two_pow_bits_length_le (jobLength F j)
  rw [word_length] at hw
  omega

theorem run_capacity (F : BinaryFamily) {onset : ℕ} (K e : ℕ) (j : Job F onset)
    (hn : jobLength F j ≤ (jobBits F j).length) :
    2 * (payload F (workOf F j)).length + 2 < 2 ^ (sizes onset K e).W (L F j) := by
  have hw := width F K e j
  have hp := payload_length F j
  rw [word_length] at hw
  omega

theorem input_room (F : BinaryFamily) {onset : ℕ} (K e : ℕ) (j : Job F onset) (n : ℕ)
    (hn : n ≤ (jobWord F j).length) : n ≤ (sizes onset K e).Lk (L F j) := by
  have hs := size_lower F j
  simp only [sizes, Sz.Lk, one_mul, mul_one]
  omega

theorem call_clock (F : BinaryFamily) {onset : ℕ} (K e : ℕ) (j : Job F onset) (n : ℕ)
    (hn : n ≤ (jobWord F j).length) : K * (n + 1) ^ e ≤ (sizes onset K e).Bk (L F j) := by
  have hs := size_lower F j
  have hp := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (show n + 1 ≤ 2 ^ L F j by omega) e)
  simpa only [sizes, Sz.Bk, ← pow_mul, Nat.mul_comm e, Nat.mul_comm K] using hp

theorem prefix_poly (F : BinaryFamily) (onset : ℕ) : Bound (fun j : Job F onset => (jobWord F j).length) (L F) :=
  mono self (fun _ => Nat.size_le.mpr Nat.lt_two_pow_self)

theorem allocation_poly (F : BinaryFamily) (onset : ℕ) :
    Bound (fun j : Job F onset => (jobWord F j).length) (fun j => 2 ^ L F j) :=
  ⟨2, 1, fun j => by simpa only [pow_one] using size_upper F j⟩

end NearCubicGates.Adapters.Code.DecoderBounds
