import Proof.Gates.WorkerArith.RestPoly
import Proof.Gates.WorkerArith.VerdictSize
import Proof.Gates.WorkerArith.LoopBudget
import Proof.Gates.WorkerArith.WeakWorkerDefs
import Proof.Gates.TermLoop.Fields
import Proof.Gates.Setup.Entry
import Proof.Gates.Setup.Words

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop
open NearCubicGates.Close.CheckedPCPP (supportsWord)
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount)

theorem length_le_flatMapW {α : Type} (f : α → List Bool) (h : ∀ a, 1 ≤ (f a).length) :
    ∀ l : List α, l.length ≤ (l.flatMap f).length
  | [] => by simp
  | a :: l => by
    have := length_le_flatMapW f h l
    have := h a
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- The code length is at most the supports record's length (every row is a nonempty word). -/
theorem codeLength_le_supportsW (P : ThreeQueryPCPP) (q : ℕ) : P.code.length q ≤ (supportsWord P.code q).length := by
  unfold supportsWord
  have := length_le_flatMapW (fun j : Fin (P.code.length q) =>
    Interfaces.listWord natWord ((canonList (P.code.support q j)).map Fin.val)) (fun j => by
      simp only [Interfaces.listWord, List.length_append]
      have : (natWord ((canonList (P.code.support q j)).map Fin.val).length).length =
          2 * natBitLength ((canonList (P.code.support q j)).map Fin.val).length + 1 := by simp
      omega) (List.finRange (P.code.length q))
  simpa using this

section Accept
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} {B1 B2 : ℕ} (ctr : Counter B1 B2)
  (hD : Counter.DenOK ctr) (ω εT : ℚ) (D : SetupData s P g) (vm : Worker.VerdictMachine P.gamma εT)

/-- **The accepting run's fit and fuel.** -/
theorem accept_fit (hCF : CircuitSizeFit) (hRF : RowSizeFit) (Fs : ℕ → ℕ) (onc Kc ec Co eo Cv ev : ℕ)
    (hbud : ∀ (c : Call) (w : List Bool), onc ≤ c.n → ctr.budget c w ≤ hotCall c.n + Kc * ((callWord c).length + 1) ^ ec)
    (hOo : ∀ (c : Call) (w : List Bool), (outputWord (ctr.value c w)).length ≤ Co * (c.n + 1) ^ eo)
    (hvm : ∀ r, vm.budget r ≤ Cv * ((Worker.verdictWord r).length + 1) ^ ev)
    {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (Bo : Outer.OuterGuess (width s g N))
    (hq : onc ≤ width s g N)
    (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) Bo)
    (hpad : N / 16 + 1 ≤ pad)
    (hphys : N / 16 + 2 + auxN s P g x Bo * (2 + 2 * (N / 16) * (width s g N + 2)) + 10 * gadgets s g N ≤ pad)
    (hsc : setupCost D x bits pad Bo ≤ Fs N) :
    ∃ cap Z Bc V, LoopFit (P := P) ctr ω x bits pad Bo cap Z Bc V ∧ capA D N pad ≤ cap ∧
      setupCap D x bits pad Bo ≤ cap ∧
      2 * (Worker.verdictWord ((theGuess s P g x bits pad).verdictReq P x ctr hD ω)).length + 2 ≤ cap ∧
      setupCost D x bits pad Bo +
        loopCost D.tc Z Bc (frontSize s P g x Bo) (gadgets s g N) (loopBud s P g x bits pad Bo ctr ω) +
        2 * vm.budget ((theGuess s P g x bits pad).verdictReq P x ctr hD ω) +
        12 * (Worker.verdictWord ((theGuess s P g x bits pad).verdictReq P x ctr hD ω)).length + 100 ≤
      Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N +
        WorkerArith.WorkerBounds.hotOf s g D.tc N := by
  set SS := SSf Fs (ratWord ω).length N with hSSdef
  have hS := (setupSize_le_setupCost D x bits pad Bo).trans hsc
  have hsz : N + pad + D.N0 + width s g N + gadgets s g N + auxN s P g x Bo + (pcpp s P g x Bo).randomBits +
      (pcpp s P g x Bo).word.length + (supportsWord P.code (width s g N)).length +
      (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x Bo)).length +
      (CheckedPCPP.mwWord s g N Bo.src).length + (PCPPNative.descriptor Bo.src).length +
      (PCPPNative.descriptor Bo.pf).length + Worker.nu N ^ (g.lenRoot + 1) ≤ Fs N := hS
  have hSS : 2 * Fs N ≤ SS := by rw [hSSdef]; unfold SSf; omega
  have hω : (ratWord ω).length ≤ SS := by rw [hSSdef]; unfold SSf; omega
  have hbase : Worker.nu N ^ (g.lenRoot + 1) ≤ SS := by omega
  have hL := codeLength_le_supportsW P (width s g N)
  have hwl : (guessWord N bits pad).length = N / 16 + pad := by simp [guessWord, prefixBits_length]
  have hsys : sysCount s P g x Bo = width s g N + P.code.length (width s g N) := rfl
  have hfit := loopFit_of (P := P) ctr ω hCF hRF x bits pad Bo hdec hpad hphys SS (by rw [hwl]; omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [hsys]; omega) hω
    (capOf (P := P) ctr ω x bits pad Bo SS + capA D N pad + setupCap D x bits pad Bo +
      (2 * (Worker.verdictWord ((theGuess s P g x bits pad).verdictReq P x ctr hD ω)).length + 2)) (by omega)
  refine ⟨_, _, _, _, hfit, by omega, by omega, by omega, ?_⟩
  -- the loop
  have hsplit := loopBud_split x bits pad Bo ctr ω _ _ _ _ onc Kc ec hbud hq hfit D.tc
  have hsys2 : sysCount s P g x Bo ≤ 2 * Fs N := by rw [hsys]; omega
  have haux : auxN s P g x Bo = (pcpp s P g x Bo).proofBits + gadgets s g N := rfl
  have hfront : frontSize s P g x Bo ≤ 3 * SS := by
    unfold frontSize
    omega
  have hpow : (Zof SS + frontSize s P g x Bo + 1) ^ 4 ≤ (Zof SS + 3 * SS + 1) ^ 4 :=
    Nat.pow_le_pow_left (by omega) 4
  have hloop : loopCost D.tc (Zof SS) (Bcof SS) (frontSize s P g x Bo) (gadgets s g N)
      (loopBud s P g x bits pad Bo ctr ω) ≤ Lpf Fs (gadgets s g) (ratWord ω).length D.tc Kc ec N +
        WorkerArith.WorkerBounds.hotOf s g D.tc N := by
    unfold loopCost Lpf
    rw [← hSSdef]
    have h1 : 1000000000000000 * (D.tc + 1) * (Zof SS + frontSize s P g x Bo + 1) ^ 4 * (Bcof SS + 1) ≤
        1000000000000000 * (D.tc + 1) * (Zof SS + 3 * SS + 1) ^ 4 * (Bcof SS + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
    have h2 := Nat.mul_le_mul_left (gadgets s g N) (Nat.add_le_add_right h1 4)
    omega

  have hG := guess_oracle s P g x bits pad Bo hdec
  have hvw := verdictWord_le (P := P) x (theGuess s P g x bits pad) ctr ω Co eo hOo hD
  rw [hG] at hvw
  have hcl : clauseWidth g.clauseDegree (width s g N) ≤ gadgets s g N := Nat.lt_two_pow_self.le
  have hvw2 : (Worker.verdictWord ((theGuess s P g x bits pad).verdictReq P x ctr hD ω)).length ≤
      VWf Fs (gadgets s g) (width s g) (ratWord ω).length Co eo N := by
    unfold VWf
    rw [← hSSdef]
    omega
  have hvb : vm.budget ((theGuess s P g x bits pad).verdictReq P x ctr hD ω) ≤
      Cv * (VWf Fs (gadgets s g) (width s g) (ratWord ω).length Co eo N + 1) ^ ev :=
    (hvm _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) ev))
  unfold Fpf
  omega

end Accept

end NearCubicGates.Close.WorkerArith.WorkerBounds
