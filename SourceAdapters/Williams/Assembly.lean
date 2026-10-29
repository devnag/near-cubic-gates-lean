import SourceAdapters.Williams.LoaderRun
import SourceAdapters.Williams.Restriction
import Proof.Gates.CheckedPCPP.WMXReady
import Proof.Foundations.OrdinaryTapeRenaming
import Bindings.Williams14_Corollary4_4

/-!
# W07: assembly of `MultitapeMultiplier` from the published leaf

Produce the actual `Machine`, tape count, state count, fresh output index, and `run = some receipt`
proof in `MultitapeMultiplier`. Consumer: `Williams14_Corollary4_4` (`Statement.lean:1141`), the field
`rectangularProduct` of `NineInputs` (`Statement.lean:1581`). Paper anchors: `imp:batch`, the source table
row (`app:sources`), the machine model (`sec:prelim`, "Machine model").

One `WMX` program: `loader` (W04) ; the rewound simulator of the leaf's machine (W03, `Rewind.machine`) ;
`formatter` (W05). It is run from the release's blank tapes (`CheckedPCPP.WMXReady.runFrom_rel`), and tape 1 is moved
into place by `TapeRenaming` (the `WMX` layout keeps its cell on tape 1).
-/

namespace NearCubicGates.Adapters.Williams.Assembly

open NearCubicGates.Published.Williams NearCubicGates.Adapters.Williams NearCubicGates.Adapters.Williams.Load
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## W03 as a `Step`: the rewound simulator -/

theorem simulator_initial (M : MultitapeTM) (inTape : Fin M.tapes) (input : List (Symbol M.extraSymbols))
    (T : Fin M.tapes → List Bool) :
    initialConfiguration (simulator M) T =
      cfg M (readStart M (M.initial inTape input).state) (blockHeads (M.initial inTape input)) T := by
  apply configuration_ext
  · rfl
  · funext i; simp [initialConfiguration, cfg, blockHeads, MultitapeTM.initial]
  · rfl

/-- The total length of a simulated run, rewound. -/
def simCost (M : MultitapeTM) (t : ℕ) : ℕ :=
  2 * ((3 * (M.extraSymbols + 4) - 1) * t + (M.extraSymbols + 4)) + 2

/-- **W03 for the assembly.** A halting source run on `input` is a `Step` of the rewound simulator from all heads
on cell 0 to all heads on cell 0, every simulated tape holding the final source tape. -/
theorem rewound_step (M : MultitapeTM) (inTape : Fin M.tapes) (input : List (Symbol M.extraSymbols)) (t : ℕ)
    (cf : M.Configuration) (hrun : M.run t (M.initial inTape input) = some cf) (hf : M.step cf = none)
    (T : Fin M.tapes → List Bool) (hT : ∀ i, Holds ((M.initial inTape input).contents i) (T i)) :
    ∃ (T' : Fin M.tapes → List Bool) (rec : Fin 1 → List Bool), (∀ i, Holds (cf.contents i) (T' i)) ∧
      Step (Rewind.machine (simulator M)) (simCost M t) (fun _ => 0) (Fin.addCases T fun _ => [])
        (fun _ => 0) (Fin.addCases T' rec) := by
  obtain ⟨T', hT', r, hr, hfin, hsteps⟩ := simulator_run t _ cf hrun hf T hT
  rw [← simulator_initial M inTape input T] at hr
  obtain ⟨r2, hr2, htapes, hheads, hsteps2, -⟩ := Rewind.reset_run (simulator M) _ T r hr
  refine ⟨T', fun _ => r2.final.tapes (Fin.natAdd M.tapes 0), hT', ?_⟩
  refine Step.of_run (r := r2) ?_ (funext hheads) ?_
  · rw [hsteps] at hr2; unfold simCost; exact hr2
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [htapes i, hfin]; simp [cfg]
    · simp only [Fin.addCases_right]
      rw [Subsingleton.elim i 0]

/-! ## The program -/

section Program
variable (M : MultitapeTM)

/-- Streams: `IA` (tape 0 input), `IB` (tape 1 input), `OUT`, `REC` (rewind record), `SIM i` (simulated tape `i`). -/
def sIA : Fin (M.tapes + 3 + 1) := ⟨0, by omega⟩
def sIB : Fin (M.tapes + 3 + 1) := ⟨1, by omega⟩
def sOUT : Fin (M.tapes + 3 + 1) := ⟨2, by omega⟩
def sREC : Fin (M.tapes + 3 + 1) := ⟨3, by omega⟩
def sSIM (i : Fin M.tapes) : Fin (M.tapes + 3 + 1) := ⟨i.val + 4, by omega⟩

/-- The simulator's tapes among the streams. -/
def tmap : Fin (M.tapes + 1) → Fin (M.tapes + 3 + 1) := Fin.addCases (fun i => sSIM M i) (fun _ => sREC M)

theorem tmap_injective : Function.Injective (tmap M) := by
  intro a b h
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    (simp [tmap, sSIM, sREC, Fin.ext_iff] at h ⊢; try omega)

/-- **The assembled program**: loader ; rewound simulator ; formatter. -/
noncomputable def program (inTape outTape : Fin M.tapes) : WMX (M.tapes + 3) 16 :=
  .seq (loader (sIA M) (sIB M) (sSIM M inTape) M.extraSymbols)
    (.seq (.mach (Rewind.machine (simulator M)) (tmap M))
      (Format.formatter (sSIM M outTape) (sOUT M) 0 1 2 3 M.extraSymbols))

/-- The initial word state: the two input streams, everything else empty. -/
def start0 (LA LB : List Bool) : WState (M.tapes + 3) 16 :=
  ⟨fun _ => 0, fun i => if i = sIA M then LA else if i = sIB M then LB else [], fun _ => 0, false⟩

end Program

/-! ## The derivation -/

theorem mem_rowMajor {α : Type} {n m : ℕ} (P : Fin n → Fin m → α) (y : α) (hy : y ∈ rowMajor P) :
    ∃ i j, P i j = y := by
  simp only [rowMajor, List.mem_flatten, List.mem_ofFn] at hy
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hy
  simp only [List.mem_ofFn] at hl
  obtain ⟨j, rfl⟩ := hl
  exact ⟨i, j, rfl⟩

theorem integerProduct_eq {n m p : ℕ} (A : Fin n → Fin m → Bool) (B : Fin m → Fin p → Bool) :
    integerProduct A B = Bindings.Williams14.product A B := rfl

/-- **The derivation.** A halting run of the leaf's machine on `inputWord A B` with the product on its output tape
gives a `WXExec` derivation of the assembled program whose `OUT` stream is `outputWord N (product A B)`. -/
theorem program_exec (M : MultitapeTM) (inTape outTape : Fin M.tapes) (k : ℕ) (hk : 1 ≤ k)
    (A : Fin (k ^ 10) → Fin k → Bool) (B : Fin k → Fin (k ^ 10) → Bool) (t : ℕ) (cf : M.Configuration)
    (hrun : M.run t (M.initial inTape (inputWord A B)) = some cf) (hf : M.step cf = none)
    (hout : cf.contents outTape = fun p => (outputWord (integerProduct A B)).getD p Symbol.blank)
    (cap : ℕ) (hcap : loaderCap k ≤ cap) (hcapW : natBitLength (k ^ 10) + 1 ≤ cap) :
    ∃ τ, WXExec cap (program M inTape outTape)
        (start0 M (RepairRepresentation.natWord (k ^ 10) ++ WilliamsLoaderForms.rowMajorBitMatrix A)
          (WilliamsLoaderForms.rowMajorBitMatrix B)) τ
        (loaderCost M.extraSymbols k + 1 + (simCost M t + 1 +
          (k ^ 10 * k ^ 10 * (Format.entryCost M.extraSymbols (natBitLength (k ^ 10)) + 2) + 1))) ∧
      τ.st (sOUT M) = Bindings.Williams14.outputWord (k ^ 10) (Bindings.Williams14.product A B) := by
  have hAB : sIA M ≠ sIB M := by simp [sIA, sIB, Fin.ext_iff]
  have hAS : ∀ i, sIA M ≠ sSIM M i := by intro i; simp [sIA, sSIM, Fin.ext_iff]
  have hBS : ∀ i, sIB M ≠ sSIM M i := by intro i; simp [sIB, sSIM, Fin.ext_iff]
  have hOS : ∀ i, sOUT M ≠ sSIM M i := by intro i; simp [sOUT, sSIM, Fin.ext_iff]
  have hSS : ∀ i j, sSIM M i = sSIM M j → i = j := by intro i j h; simp [sSIM, Fin.ext_iff] at h; exact Fin.ext h
  obtain ⟨τ1, e1, l1, l2, l3, l4, l5, l6, l7⟩ := loader_spec (cap := cap) (sIA M) (sIB M) (sSIM M inTape) hAB
    (hAS _) (hBS _) M.extraSymbols k hk A B (start0 M (RepairRepresentation.natWord (k ^ 10) ++
      WilliamsLoaderForms.rowMajorBitMatrix A) (WilliamsLoaderForms.rowMajorBitMatrix B)) (by simp [start0]) rfl
    (by simp [start0, Ne.symm hAB]) rfl (by simp [start0, Ne.symm (hAS _), Ne.symm (hBS _)]) rfl (fun _ => rfl) hcap
  -- the simulated tapes after loading
  let T : Fin M.tapes → List Bool := fun i => τ1.st (sSIM M i)
  have hTo : ∀ i, i ≠ inTape → τ1.st (sSIM M i) = [] ∧ τ1.sh (sSIM M i) = 0 := by
    intro i hi
    have := l7 (sSIM M i) (Ne.symm (hAS i)) (Ne.symm (hBS i)) (fun h => hi (hSS _ _ h))
    rw [this.1, this.2]; simp [start0, Ne.symm (hAS i), Ne.symm (hBS i)]
  have hT : ∀ i, Holds ((M.initial inTape (inputWord A B)).contents i) (T i) := by
    intro i
    by_cases hi : i = inTape
    · subst hi
      have : (M.initial i (inputWord A B)).contents i = fun p => (inputWord A B).getD p Symbol.blank := by
        funext p; simp [MultitapeTM.initial]
      rw [this]; show Holds _ (τ1.st (sSIM M i)); rw [l1]; exact holds_flatMap _
    · intro p j _
      show readTapeBit (τ1.st (sSIM M i)) _ = _
      rw [(hTo i hi).1]; simp [MultitapeTM.initial, hi, readTapeBit]
  obtain ⟨T', rec, hT', hstep⟩ := rewound_step M inTape (inputWord A B) t cf hrun hf T hT
  have hRo : τ1.st (sREC M) = [] ∧ τ1.sh (sREC M) = 0 := by
    have := l7 (sREC M) (by simp [sREC, sIA, Fin.ext_iff]) (by simp [sREC, sIB, Fin.ext_iff])
      (by simp [sREC, sSIM, Fin.ext_iff])
    have h1 : sREC M ≠ sIA M := by simp [sREC, sIA, Fin.ext_iff]
    have h2 : sREC M ≠ sIB M := by simp [sREC, sIB, Fin.ext_iff]
    rw [this.1, this.2]; simp [start0, if_neg h1, if_neg h2]
  have hin_h : (fun j => τ1.sh (tmap M j)) = fun _ => 0 := by
    funext j
    induction j using Fin.addCases with
    | left i =>
      simp only [tmap, Fin.addCases_left]
      by_cases hi : i = inTape
      · subst hi; exact l2
      · exact (hTo i hi).2
    | right i => simp only [tmap, Fin.addCases_right]; exact hRo.2
  have hin_t : (fun j => τ1.st (tmap M j)) = Fin.addCases T (fun _ => []) := by
    funext j
    induction j using Fin.addCases with
    | left i => simp only [tmap, Fin.addCases_left]; rfl
    | right i => simp only [tmap, Fin.addCases_right]; exact hRo.1
  have hstep' : Step (Rewind.machine (simulator M)) (simCost M t) (fun j => τ1.sh (tmap M j))
      (fun j => τ1.st (tmap M j)) (fun _ => 0) (Fin.addCases T' rec) := by
    rw [hin_h, hin_t]; exact hstep
  have e2 := WXExec.mach (cap := cap) τ1 (tmap_injective M) hstep'
  have hcast : tmap M (Fin.castAdd 1 outTape) = sSIM M outTape := by simp [tmap]
  have hOUTo : ∀ j, tmap M j ≠ sOUT M := by
    intro j
    induction j using Fin.addCases with
    | left i => simp [tmap, sSIM, sOUT, Fin.ext_iff]
    | right i => simp [tmap, sREC, sOUT, Fin.ext_iff]
  have hOf := l7 (sOUT M) (by simp [sOUT, sIA, Fin.ext_iff]) (by simp [sOUT, sIB, Fin.ext_iff]) (hOS inTape)
  have hO1 : sOUT M ≠ sIA M := by simp [sOUT, sIA, Fin.ext_iff]
  have hO2 : sOUT M ≠ sIB M := by simp [sOUT, sIB, Fin.ext_iff]
  have hFm : Format.Fm (sSIM M outTape) (sOUT M) 0 1 2 3 (T' outTape) (natBitLength (k ^ 10))
      (updS (tmap M) τ1 (fun _ => 0) (Fin.addCases T' rec)) ((M.extraSymbols + 4) * 0) [] 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, l4, l5, l3, l6⟩
    · rw [← hcast, updS_st_slot (tmap M) τ1 _ _ (tmap_injective M)]; simp
    · rw [← hcast, updS_sh_slot (tmap M) τ1 _ _ (tmap_injective M)]; simp
    · rw [updS_st_other (tmap M) τ1 _ _ _ hOUTo, hOf.1]; simp [start0, hO1, hO2]
    · rw [updS_sh_other (tmap M) τ1 _ _ _ hOUTo, hOf.2]; rfl
  have hB : Format.BlocksFrom (T' outTape) 0
      ((rowMajor (integerProduct A B)).flatMap numberWord : List (Symbol M.extraSymbols)) := by
    intro q j hj
    have := hT' outTape q j hj
    rw [hout] at this
    rw [Nat.zero_add]
    exact this
  have hys : ∀ y ∈ rowMajor (integerProduct A B), y < 2 ^ natBitLength (k ^ 10) := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := mem_rowMajor _ y hy
    exact Bindings.Williams14.product_lt A B i j
  obtain ⟨τ3, e3, p', hτ3⟩ := Format.formatter_spec (cap := cap) (hOS outTape).symm (by decide) hcapW _ 0 [] _ hys
    hB hFm
  refine ⟨τ3, WXExec.seq e1 (WXExec.seq e2 (WXExec.mono e3 (by rw [rowMajor_length]))), ?_⟩
  rw [hτ3.2.2.1, List.nil_append]
  rfl

/-! ## From the derivation to a run on the release's tapes -/

open NearCubicGates.Close.CheckedPCPP (ConfRel runFrom_rel coldBank coldBank_s coldBank_c coldBank_r)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (RdEq rdEq_blank)

/-- A derivation from all-zero heads and registers is a run of the compiled machine from the blank work tapes;
every stream tape ends as the derivation's stream. -/
theorem run_cold {ns nr cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hcell : σ.cell = false) :
    ∃ r, run P.compile n (coldBank σ) = some r ∧ ∀ i, r.final.tapes (sTape i) = τ.st i := by
  obtain ⟨r, hr, -, ht, -⟩ := WXExec.run cap h hsh hval
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile (coldBank σ)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases NearCubicWires.WireExponent3_5.PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, coldBank_s]; exact NearCubicWires.WireExponent3_5.PrimT.ReadEq.RdEq.refl _
      · rw [NearCubicWires.WireExponent3_5.PrimAsm.DockW.wenc_A_c, coldBank_c, hcell]
        exact rdEq_blank _ (by simp)
      · rw [wenc_A_r, coldBank_r, hval q, NearCubicWires.WireExponent3_5.FinalPass.Tm.regTape_zero]
        exact rdEq_blank _ (by simp)
    · rintro j ⟨i, rfl⟩
      simp only [initialConfiguration]
      rw [wenc_A_s, coldBank_s]
  obtain ⟨r', hr', hrel', -⟩ := runFrom_rel P.compile E n hrel r hr
  exact ⟨r', hr', fun i => by rw [← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, wenc_A_s]⟩

/-- The tape count of the assembled machine. -/
abbrev tapeCountOf (M : MultitapeTM) : ℕ := M.tapes + 3 + 2 + 16

/-- Swap tapes 1 and 2: the second input on tape 1, the `WMX` cell on tape 2. -/
def swapT (M : MultitapeTM) : Fin (tapeCountOf M) ≃ Fin (tapeCountOf M) :=
  Equiv.swap ⟨1, by unfold tapeCountOf; omega⟩ ⟨2, by unfold tapeCountOf; omega⟩

theorem cold_rename (M : MultitapeTM) (LA LB : List Bool) (j : Fin (tapeCountOf M)) :
    coldBank (start0 M LA LB) ((swapT M).symm j) =
      if j.val = 0 then LA else if j.val = 1 then LB else [] := by
  rcases j with ⟨j, hj⟩
  simp only [swapT, Equiv.symm_swap, Equiv.swap_apply_def, Fin.ext_iff, Fin.val_mk]
  by_cases h1 : j = 1
  · subst h1; simp [coldBank, NearCubicWires.WireExponent3_5.FinalPass.Tm.role, start0, sIA, sIB]
  · by_cases h2 : j = 2
    · subst h2; simp [coldBank, NearCubicWires.WireExponent3_5.FinalPass.Tm.role]
    · simp only [h1, h2, if_false]
      by_cases h0 : j = 0
      · subst h0
        simp only [coldBank, NearCubicWires.WireExponent3_5.FinalPass.Tm.role, Fin.val_mk, dif_pos, if_true]
        rfl
      · simp only [h0, h1, h2, if_false, dif_neg, not_false_eq_true, coldBank,
          NearCubicWires.WireExponent3_5.FinalPass.Tm.role, Fin.val_mk]
        split_ifs with h3
        · simp only [start0]
          rw [if_neg (by simp only [sIA, ne_eq, Fin.ext_iff, Fin.val_mk]; omega),
            if_neg (by simp only [sIB, ne_eq, Fin.ext_iff, Fin.val_mk]; omega)]
        · rfl

end NearCubicGates.Adapters.Williams.Assembly
