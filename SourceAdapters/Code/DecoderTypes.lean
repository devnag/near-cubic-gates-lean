import SourceAdapters.Code.DecoderRequest
import SourceAdapters.Code.CappedDock
import SourceAdapters.Code.PaddedOutput

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": intermediate decoder words and their exact relation to
the total finite-patched decoder. These are adapter encodings, not source leaves. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderTypes

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

structure Triple (F : BinaryFamily) where
  first : TotalSourceRequest F
  second : TotalSourceRequest F
  third : TotalSourceRequest F

abbrev Work (F : BinaryFamily) := List Bool ⊕ Triple F

def sourcePacket (F : BinaryFamily) (p : TotalSourceRequest F) : List Bool :=
  DecoderRequest.packet p.1 (List.ofFn p.2)

def payload (F : BinaryFamily) : Work F → List Bool
  | .inl bits => false :: frame bits
  | .inr p => true :: (sourcePacket F p.first ++ sourcePacket F p.second ++ sourcePacket F p.third)

def input (F : BinaryFamily) (L : ℕ) (w : Work F) : List Bool := List.replicate L true ++ false :: payload F w

def output (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius) : Work F → List Bool
  | .inl bits => bits
  | .inr p => List.ofFn (totalDecoder F D p.first.1 p.first.2) ++
      List.ofFn (totalDecoder F D p.second.1 p.second.2) ++ List.ofFn (totalDecoder F D p.third.1 p.third.2)

abbrev Job (F : BinaryFamily) (onset : ℕ) :=
  (Σ n : ℕ, {_y : BitInput n // n < cutoff onset}) ⊕
  (Σ n : ℕ, {_y : BitInput ((threeBlock F).length n) // cutoff onset ≤ n})

def jobLength (F : BinaryFamily) {onset : ℕ} : Job F onset → ℕ
  | .inl p => p.1
  | .inr p => p.1

def jobBits (F : BinaryFamily) {onset : ℕ} : Job F onset → List Bool
  | .inl p => List.ofFn p.2.val
  | .inr p => List.ofFn p.2.val

def jobWord (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : List Bool :=
  frame (jobLength F j).bits ++ frame (jobBits F j)

def workOf (F : BinaryFamily) {onset : ℕ} : Job F onset → Work F
  | .inl p => .inl (List.ofFn p.2.val)
  | .inr p => .inr ⟨⟨blockSize p.1 0, p.2.val ∘ firstOutputIndex F p.1⟩,
      ⟨blockSize p.1 1, p.2.val ∘ secondOutputIndex F p.1⟩,
      ⟨blockSize p.1 2, p.2.val ∘ thirdOutputIndex F p.1⟩⟩

def jobOutput (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius) : Job F onset → List Bool
  | .inl p => List.ofFn p.2.val
  | .inr p => List.ofFn (threeDecoder F D p.1 p.2.val)

theorem work_output (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (j : Job F onset) : output F D (workOf F j) = jobOutput F D j := by
  cases j with
  | inl p => rfl
  | inr p => exact (threeBlock_decoder_word F D p.1 p.2.val).symm

theorem source_resize (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (p : TotalSourceRequest F) :
    PaddedOutput.resize (cappedOutput D.program (decoderCappedRequest F D p)) p.1 =
      List.ofFn (totalDecoder F D p.1 p.2) := by
  rw [PaddedOutput.resize_ofFn, totalDecoder_capped_output]

theorem source_packet (F : BinaryFamily) (p : TotalSourceRequest F) :
    sourcePacket F p = frame (List.replicate p.1 true) ++ frame (decoderInput F p.1 p.2) := rfl

theorem received_split (F : BinaryFamily) (n : ℕ) (y : BitInput ((threeBlock F).length n)) :
    List.ofFn y = List.ofFn (y ∘ firstOutputIndex F n) ++ List.ofFn (y ∘ secondOutputIndex F n) ++
      List.ofFn (y ∘ thirdOutputIndex F n) := by
  have hy : joinWord (joinWord (y ∘ firstOutputIndex F n) (y ∘ secondOutputIndex F n)) (y ∘ thirdOutputIndex F n) = y := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp [joinWord, firstOutputIndex]
      · simp [joinWord, secondOutputIndex]
    · simp [joinWord, thirdOutputIndex]
  have hh := congrArg (fun f => List.ofFn f) hy
  change List.ofFn (joinWord (joinWord (y ∘ firstOutputIndex F n) (y ∘ secondOutputIndex F n))
    (y ∘ thirdOutputIndex F n)) = List.ofFn y at hh
  rw [ofFn_joinWord, ofFn_joinWord] at hh
  exact hh.symm

theorem ofFn_cast {a b : ℕ} (h : a = b) (x : BitInput b) :
    List.ofFn (fun i : Fin a => x (Fin.cast h i)) = List.ofFn x := by
  cases h
  rfl

theorem decoder_cast {n : ℕ} (C D : CoordinateCode n) (h : C = D) (y : BitInput C.size) :
    D.decoder (fun i => y (Fin.cast (congrArg CoordinateCode.size h).symm i)) = C.decoder y := by
  cases h
  rfl

noncomputable def jobOf (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (p : CodewordRequest (patchedFamily F D)) : Job F onset :=
  if h : cutoff onset ≤ p.1 then
    .inr ⟨p.1, ⟨fun i => p.2.val (Fin.cast (by simp [patchedFamily, familyFromAt, patchedAt, h, threeBlockAt]) i), h⟩⟩
  else .inl ⟨p.1, ⟨fun i => p.2.val (Fin.cast (by simp [patchedFamily, familyFromAt, patchedAt, h, identityAt]) i), by omega⟩⟩

theorem jobOf_word (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (p : CodewordRequest (patchedFamily F D)) : jobWord F (jobOf F D p) = codewordWord (patchedFamily F D) p := by
  unfold jobOf
  split_ifs <;> simp only [jobWord, jobLength, jobBits, codewordWord, ofFn_cast]

theorem jobOf_output (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (p : CodewordRequest (patchedFamily F D)) : jobOutput F D (jobOf F D p) = List.ofFn ((patchedFamily F D).decoder p.1 p.2.val) := by
  unfold jobOf
  split_ifs with h
  · simp only [jobOutput]
    apply congrArg List.ofFn
    exact decoder_cast (patchedAt F D p.1) (threeBlockAt F D p.1)
      (by simp only [patchedAt, if_pos h]) p.2.val
  · simp only [jobOutput]
    apply congrArg List.ofFn
    exact decoder_cast (patchedAt F D p.1) (identityAt p.1)
      (by simp only [patchedAt, if_neg h]) p.2.val

end NearCubicGates.Adapters.Code.DecoderTypes
