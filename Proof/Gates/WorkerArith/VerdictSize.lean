import Proof.Gates.Worker.Terms
import Proof.Gates.Counter.OutOK
import Proof.Gates.Setup.ReadBound

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Worker NearCubicGates.Close.Gadget

theorem natWord_le (v : ℕ) : (natWord v).length ≤ 2 * v + 3 := by
  rw [Setup.natWord_len]
  have := Setup.natBitLength_le_of_lt v v Nat.lt_two_pow_self
  omega

theorem ratWord_le (r : ℚ) : (ratWord r).length ≤ 2 * r.num.natAbs + 2 * r.den + 11 := by
  have h1 := natWord_le (if r.num < 0 then 1 else 0)
  have h2 := natWord_le r.num.natAbs
  have h3 := natWord_le r.den
  have h4 : (if r.num < 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  simp only [Interfaces.ratWord, Interfaces.intWord, List.length_append]
  omega

theorem ratWord_const (a : ℚ) (ha : a = 0 ∨ a = 1 / 2 ∨ a = 1) : (ratWord a).length ≤ 20 := by
  refine (ratWord_le a).trans ?_
  rcases ha with rfl | rfl | rfl
  · norm_num
  · have h1 : ((1 : ℚ) / 2).num = 1 := by norm_num
    have h2 : ((1 : ℚ) / 2).den = 2 := by norm_num
    rw [h1, h2]; norm_num
  · norm_num

theorem outputWord_const (a b : ℚ) (ha : a = 0 ∨ a = 1 / 2 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (outputWord (a, b)).length ≤ 40 := by
  have h1 := ratWord_const a ha
  have h2 := ratWord_const b (by rcases hb with h | h <;> simp [h])
  simp only [outputWord, List.length_append]
  omega

section Size
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N)) {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (Co eo : ℕ)
  (hO : ∀ (c : Call) (w : List Bool), (outputWord (ctr.value c w)).length ≤ Co * (c.n + 1) ^ eo)

include hO in
theorem termParts_out_le (w : List Bool) (ops : List (Bool × Atom)) :
    (outputWord (G.termParts P x ctr ω w ops).2).length ≤ Co * (width s g N + 1) ^ eo + 40 := by
  have hpm : ∀ S : Finset (Fin (width s g N)), parityMean S = 0 ∨ parityMean S = 1 / 2 ∨ parityMean S = 1 := by
    intro S; unfold parityMean; split_ifs <;> simp
  have hask : ∀ c : Call, c.n = width s g N → (outputWord (ctr.value c w)).length ≤ Co * (width s g N + 1) ^ eo + 40 :=
    fun c hc => by have := hO c w; rw [hc] at this; omega
  unfold Guess.termParts
  generalize ops.map Prod.snd = l
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact (outputWord_const 0 1 (Or.inl rfl) (Or.inr rfl)).trans (by omega)
  · cases a with
    | sys u => exact (outputWord_const _ 0 (hpm _) (Or.inl rfl)).trans (by omega)
    | aux j =>
      refine hask _ ?_
      unfold Guess.singleCall; split_ifs <;> rfl
  · cases a with
    | sys u =>
      cases b with
      | sys v => exact (outputWord_const _ 0 (hpm _) (Or.inl rfl)).trans (by omega)
      | aux j => refine hask _ ?_; unfold Guess.singleCall; split_ifs <;> rfl
    | aux i =>
      cases b with
      | sys u => refine hask _ ?_; unfold Guess.singleCall; split_ifs <;> rfl
      | aux j =>
        show (outputWord (if i = j then (0, 0) else ctr.value (G.pairCall ω i j) w)).length ≤ _
        split_ifs
        · exact (outputWord_const 0 0 (Or.inl rfl) (Or.inl rfl)).trans (by omega)
        · exact hask _ rfl
  · cases a <;> cases b <;> exact le_trans (outputWord_const 0 1 (Or.inl rfl) (Or.inr rfl)) (by omega)

include hO in
/-- **The verdict request's length.** -/
theorem verdictWord_le (hD : Counter.DenOK ctr) :
    (verdictWord (G.verdictReq P x ctr hD ω)).length ≤
      2 * width s g N + 2 * gadgets s g N + 2 * Worker.nu N ^ (g.lenRoot + 1) + 2 * (pcpp s P g x G.oracle).randomBits +
        2 * clauseWidth g.clauseDegree (width s g N) + 20 * gadgets s g N + 18 +
        10 * gadgets s g N * (Co * (width s g N + 1) ^ eo + 43) := by
  have hel : ∀ y ∈ G.termList P x ctr ω, (bitWord y.1 ++ outputWord y.2).length ≤
      Co * (width s g N + 1) ^ eo + 43 := by
    intro y hy
    unfold Guess.termList WorkerArith.gmList at hy
    obtain ⟨a, -, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hy
    have h1 := termParts_out_le (P := P) x G ctr ω Co eo hO (G.witnesses a t) (G.operands P x a t)
    have h2 : (bitWord (G.termRaw P x ctr ω a t).1).length ≤ 3 := by
      unfold bitWord; split_ifs <;> decide
    simp only [List.length_append]
    unfold Guess.termRaw at h2 ⊢
    omega
  have hf := Setup.flatMap_len_le (fun y : Bool × (ℚ × ℚ) => bitWord y.1 ++ outputWord y.2)
    (Co * (width s g N + 1) ^ eo + 43) (G.termList P x ctr ω) hel
  rw [G.termList_length P x ctr ω] at hf
  have a1 := natWord_le (width s g N)
  have a2 := natWord_le (gadgets s g N)
  have a3 := natWord_le (Worker.nu N ^ (g.lenRoot + 1))
  have a4 := natWord_le (pcpp s P g x G.oracle).randomBits
  have a5 := natWord_le (clauseWidth g.clauseDegree (width s g N))
  have a6 := natWord_le (G.termList P x ctr ω).length
  have hl := G.termList_length P x ctr ω
  unfold verdictWord listWord
  simp only [List.length_append, Guess.verdictReq]
  omega

end Size

end NearCubicGates.Close.WorkerArith
