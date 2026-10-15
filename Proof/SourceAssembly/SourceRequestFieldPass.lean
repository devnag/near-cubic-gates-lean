import Proof.SourceAssembly.SLoadPoolReady
import Proof.Hierarchy.CompetitorRawScalarPaddedAppend
import Proof.Assembly.AppendOutputLength
import Proof.PCP.ProjectionNormalizationForwardRules
import Proof.SourceAssembly.SourceReuse

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.FieldPass
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.ProjectionNormalization
noncomputable section

/-! ## 1. The unframe-append primitive -/

theorem raw_local (bits out : List Bool) (cap : Nat) (hc : 2 * bits.length + 1 ≤ cap) :
    Step CompetitorRawScalarEmit.machine (4 * bits.length + 3)
      ![0, out.length, 0] ![ZeroPadding.pad cap (frame bits), out, List.replicate cap false]
      ![0, (out ++ bits).length, 0] ![ZeroPadding.pad cap (frame bits), out ++ bits, List.replicate cap false] := by
  obtain ⟨r, hr, hf, _⟩ := CompetitorRawScalarEmit.padded_append_run bits out cap hc
  have hr' : runFrom CompetitorRawScalarEmit.machine (4 * bits.length + 3)
      ⟨CompetitorRawScalarEmit.machine.start, ![0, out.length, 0],
        ![ZeroPadding.pad cap (frame bits), out, List.replicate cap false]⟩ = some r := hr
  exact Step.of_run hr' (by rw [hf]; rfl) (by rw [hf]; rfl)

theorem raw_forward : CursorRestore.NoLeft CompetitorRawScalarEmit.machine 1 := by
  intro q bits a ha
  fin_cases q <;> cases hb : bits 0 <;> cases hc : bits 2 <;>
    simp [CompetitorRawScalarEmit.machine, hb, hc] at ha
  all_goals (subst ha; decide)

/-! ## 2. The chain of `n` appends on a local universe `Fin (n+2)` -/

variable (n : Nat)

def srcT (i : Fin n) : Fin (n + 2) := ⟨i.val, by omega⟩
def outT : Fin (n + 2) := ⟨n, by omega⟩
def logT : Fin (n + 2) := ⟨n + 1, by omega⟩

def stageSlots (i : Fin n) : Fin 3 → Fin (n + 2) := ![srcT n i, outT n, logT n]

theorem stageSlots_injective (i : Fin n) : Function.Injective (stageSlots n i) := by
  have hi := i.isLt
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [stageSlots, srcT, outT, logT] at hv ⊢ <;> omega

def stage (i : Fin n) : Machine (n + 2) 4 :=
  RecoveryFocus.machine (stageSlots n i) CompetitorRawScalarEmit.machine

/-- The first `k` stages, left-nested after a halting start. -/
def chain : (k : Nat) → k ≤ n → Σ s, Machine (n + 2) s
  | 0, _ => ⟨1, SourceAssemblyReuse.haltMachine (n + 2)⟩
  | k + 1, h => ⟨_, Composition.machine (chain k (by omega)).2 (stage n ⟨k, h⟩)⟩

def tapes (w : Fin n → List Bool) (c : Nat) (acc : List Bool) : Fin (n + 2) → List Bool := fun j =>
  if h : j.val < n then ZeroPadding.pad c (frame (w ⟨j.val, h⟩))
  else if j.val = n then acc else List.replicate c false

def heads (acc : List Bool) : Fin (n + 2) → Nat := fun j => if j.val = n then acc.length else 0

/-- The concatenation of the first `k` segments. -/
def acc (w : Fin n → List Bool) (k : Nat) : List Bool := ((List.ofFn w).take k).flatten

def chainCost (w : Fin n → List Bool) (k : Nat) : Nat :=
  (((List.ofFn w).take k).map (fun x => 4 * x.length + 4)).sum

theorem acc_succ (w : Fin n → List Bool) (k : Nat) (h : k < n) :
    acc n w (k + 1) = acc n w k ++ w ⟨k, h⟩ := by
  have hk : k < (List.ofFn w).length := by rw [List.length_ofFn]; exact h
  simp only [acc, List.take_add_one, List.getElem?_eq_getElem hk, List.getElem_ofFn,
    Option.toList_some, List.flatten_append, List.flatten_singleton]

theorem cost_succ (w : Fin n → List Bool) (k : Nat) (h : k < n) :
    chainCost n w (k + 1) = chainCost n w k + 1 + (4 * (w ⟨k, h⟩).length + 3) := by
  have hk : k < (List.ofFn w).length := by rw [List.length_ofFn]; exact h
  simp only [chainCost, List.take_add_one, List.getElem?_eq_getElem hk, List.getElem_ofFn,
    Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  omega

theorem acc_full (w : Fin n → List Bool) : acc n w n = (List.ofFn w).flatten := by
  simp only [acc]
  rw [List.take_of_length_le (by rw [List.length_ofFn])]

theorem dockH_eq {t u : Nat} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (amb : Fin u → Nat) (loc : Fin t → Nat) (target : Fin u → Nat)
    (h1 : ∀ j, target (slots j) = loc j) (h2 : ∀ x, (∀ j, slots j ≠ x) → target x = amb x) :
    dockH slots amb loc = target := by
  classical
  funext x
  by_cases hx : ∃ j, slots j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [dockH_slot slots hi, h1]
  · have hn : ∀ j, slots j ≠ x := fun j hj => hx ⟨j, hj⟩
    rw [dockH_other slots amb loc x hn, h2 x hn]

theorem stage_step (w : Fin n → List Bool) (c : Nat) (hc : ∀ i, 2 * (w i).length + 1 ≤ c)
    (i : Fin n) (a : List Bool) :
    Step (stage n i) (4 * (w i).length + 3) (heads n a) (tapes n w c a)
      (heads n (a ++ w i)) (tapes n w c (a ++ w i)) := by
  have hi := i.isLt
  have h := (raw_local (w i) a c (hc i)).dock (stageSlots n i) (stageSlots_injective n i)
    (heads n a) (tapes n w c a)
    (by
      intro j
      fin_cases j <;> simp [stageSlots, heads, srcT, outT, logT]
      omega)
    (by
      intro j
      fin_cases j
      · simp [stageSlots, tapes, srcT, hi]
      · simp [stageSlots, tapes, outT]
      · simp [stageSlots, tapes, logT])
  refine h.congr ?_ ?_
  · apply dockH_eq _ (stageSlots_injective n i)
    · intro j
      fin_cases j <;> simp [stageSlots, heads, srcT, outT, logT]
      omega
    · intro x hx
      have h1 : x.val ≠ n := fun e => hx 1 (Fin.ext (by simp [stageSlots, outT, e]))
      simp [heads, h1]
  · symm
    apply SLoad.Lead.install_eq _ (stageSlots_injective n i)
    · intro j
      fin_cases j
      · simp [stageSlots, tapes, srcT, hi]
      · simp [stageSlots, tapes, outT]
      · simp [stageSlots, tapes, logT]
    · intro x hx
      have h1 : x.val ≠ n := fun e => hx 1 (Fin.ext (by simp [stageSlots, outT, e]))
      simp [tapes, h1]

theorem chain_step (w : Fin n → List Bool) (c : Nat) (hc : ∀ i, 2 * (w i).length + 1 ≤ c) :
    ∀ k (hk : k ≤ n), Step (chain n k hk).2 (chainCost n w k) (heads n []) (tapes n w c [])
      (heads n (acc n w k)) (tapes n w c (acc n w k))
  | 0, _ => by
    have e : acc n w 0 = [] := rfl
    rw [e]
    exact SourceAssemblyReuse.halt_step _ _
  | k + 1, hk => by
    have ih := chain_step w c hc k (by omega)
    have hs := stage_step n w c hc ⟨k, hk⟩ (acc n w k)
    rw [← acc_succ n w k hk] at hs
    rw [cost_succ n w k hk]
    exact ih.seq hs

theorem chain_forward : ∀ k (hk : k ≤ n), CursorRestore.NoLeft (chain n k hk).2 (outT n)
  | 0, _ => by
    intro q bits a ha
    simp [chain, SourceAssemblyReuse.haltMachine] at ha
  | k + 1, hk => by
    apply CursorRestore.composition_forward
    · exact chain_forward k (by omega)
    · exact CursorRestore.focus_forward (stageSlots n ⟨k, hk⟩) (stageSlots_injective n ⟨k, hk⟩)
        CompetitorRawScalarEmit.machine 1 raw_forward

/-! ## 3. The pass: measure, then frame -/

/-- Pass universe `Fin (n+2+1+1+2)`: the chain's `n+2` tapes, the length counter and its rewind
log (`AppendOutputLength`), the framed destination and the framer's log. -/
def srcP (i : Fin n) : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (srcT n i)))
def outP : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (outT n)))
def logP : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (logT n)))
def cntP : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 (((0 : Fin 1).natAdd (n + 2)).castAdd 1)
def dstP : Fin (n + 2 + 1 + 1 + 2) := (0 : Fin 2).natAdd (n + 2 + 1 + 1)
def flogP : Fin (n + 2 + 1 + 1 + 2) := (1 : Fin 2).natAdd (n + 2 + 1 + 1)

theorem srcP_val (i : Fin n) : (srcP n i).val = i.val := rfl
theorem outP_val : (outP n).val = n := rfl
theorem logP_val : (logP n).val = n + 1 := rfl
theorem cntP_val : (cntP n).val = n + 2 := rfl
theorem dstP_val : (dstP n).val = n + 4 := rfl
theorem flogP_val : (flogP n).val = n + 5 := rfl

def lengthMachine := AppendOutputLength.machine (chain n n le_rfl).2 (outT n)

def machine :=
  Composition.machine (TapeEmbedding.machine 2 (lengthMachine n))
    (SLoad.MaskFrame.machine (outP n) (cntP n) (dstP n) (flogP n))

/-- The two framer tapes appended to a length-run bank. -/
def extT (T : Fin (n + 2 + 1 + 1) → List Bool) (cap capL : Nat) : Fin (n + 2 + 1 + 1 + 2) → List Bool :=
  Fin.addCases (motive := fun _ => List Bool) T ![List.replicate cap false, List.replicate capL false]

theorem extT_left (T : Fin (n + 2 + 1 + 1) → List Bool) (cap capL : Nat) (i : Fin (n + 2 + 1 + 1)) :
    extT n T cap capL (Fin.castAdd 2 i) = T i := by
  simp only [extT, Fin.addCases_left]

theorem extT_dst (T : Fin (n + 2 + 1 + 1) → List Bool) (cap capL : Nat) :
    extT n T cap capL (dstP n) = List.replicate cap false := by
  simp only [extT, dstP, Fin.addCases_right]; rfl

theorem extT_flog (T : Fin (n + 2 + 1 + 1) → List Bool) (cap capL : Nat) :
    extT n T cap capL (flogP n) = List.replicate capL false := by
  simp only [extT, flogP, Fin.addCases_right]; rfl

def input (w : Fin n → List Bool) (c cap capL : Nat) : Fin (n + 2 + 1 + 1 + 2) → List Bool :=
  extT n (AppendOutputLength.input (AppendOutputLength.input (tapes n w c []))) cap capL

def cost (w : Fin n → List Bool) : Nat :=
  2 * chainCost n w n + 2 + 1 + (4 * (List.ofFn w).flatten.length + 4)

theorem heads_nil : heads n [] = fun _ => 0 := by
  funext j
  simp [heads]

/-- **The field pass.** From `n` segments in normal form `pad c (frame X_i)`, all heads `0`, the
pass leaves the bare concatenation on `outP`, its unary length on `cntP` and
`pad cap (frame (X₀ ++ … ++ X_{n-1}))` on `dstP`, keeps the sources and logs, and returns every
head to `0`. -/
theorem pass_step (w : Fin n → List Bool) (c cap capL : Nat) (hc : ∀ i, 2 * (w i).length + 1 ≤ c)
    (hL : 2 * (List.ofFn w).flatten.length + 1 ≤ capL) :
    ∃ A' : Fin (n + 2 + 1 + 1 + 2) → List Bool,
      Step (machine n) (cost n w) (fun _ => 0) (input n w c cap capL) (fun _ => 0) A' ∧
      A' (outP n) = (List.ofFn w).flatten ∧
      A' (cntP n) = List.replicate (List.ofFn w).flatten.length true ∧
      A' (dstP n) = ZeroPadding.pad cap (frame (List.ofFn w).flatten) ∧
      (∀ i, A' (srcP n i) = ZeroPadding.pad c (frame (w i))) ∧
      A' (logP n) = List.replicate c false ∧
      A' (flogP n) = List.replicate capL false := by
  classical
  obtain ⟨src, hrun, hh, ht, hs⟩ := chain_step n w c hc n le_rfl
  have hr : run (chain n n le_rfl).2 (chainCost n w n) (tapes n w c []) = some src := by
    rw [heads_nil] at hrun
    exact hrun
  obtain ⟨r, hr2, hkeep, hcnt, hheads, hsteps⟩ :=
    AppendOutputLength.length_run (chain n n le_rfl).2 (outT n) (chain_forward n n le_rfl) _ _ src hr
  have hF : acc n w n = (List.ofFn w).flatten := acc_full n w
  have hout : src.final.tapes (outT n) = (List.ofFn w).flatten := by
    rw [ht, ← hF]; simp [tapes, outT]
  have hhd : src.final.heads (outT n) = (List.ofFn w).flatten.length := by
    rw [hh, ← hF]; simp [heads, outT]
  have step1 : Step (lengthMachine n) (2 * chainCost n w n + 2) (fun _ => 0)
      (AppendOutputLength.input (AppendOutputLength.input (tapes n w c []))) (fun _ => 0)
      r.final.tapes :=
    (Step.of_run hr2 (funext hheads) rfl).enlarge (by omega)
  have step2 : Step (TapeEmbedding.machine 2 (lengthMachine n)) (2 * chainCost n w n + 2)
      (fun _ => 0) (input n w c cap capL) (fun _ => 0) (extT n r.final.tapes cap capL) := by
    have h := step1.embed (fun _ : Fin 2 => 0) ![List.replicate cap false, List.replicate capL false]
    have hz : (Fin.addCases (motive := fun _ => Nat) (fun _ : Fin (n + 2 + 1 + 1) => 0)
        (fun _ : Fin 2 => 0) : Fin (n + 2 + 1 + 1 + 2) → Nat) = fun _ => 0 := by
      funext j
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;>
        simp only [Fin.addCases_left, Fin.addCases_right]
    rw [hz] at h
    exact h
  have hBout : extT n r.final.tapes cap capL (outP n) = (List.ofFn w).flatten := by
    rw [outP, extT_left, hkeep, hout]
  have hBcnt : extT n r.final.tapes cap capL (cntP n)
      = List.replicate (List.ofFn w).flatten.length true := by
    rw [cntP, extT_left, hcnt, hhd]
  have ne : ∀ x y : Fin (n + 2 + 1 + 1 + 2), x.val ≠ y.val → x ≠ y :=
    fun x y h e => h (congrArg Fin.val e)
  have step3 := SLoad.MaskFrame.mask_frame_step (outP n) (cntP n) (dstP n) (flogP n)
    (ne _ _ (by rw [outP_val, cntP_val]; omega)) (ne _ _ (by rw [outP_val, dstP_val]; omega))
    (ne _ _ (by rw [outP_val, flogP_val]; omega)) (ne _ _ (by rw [cntP_val, dstP_val]; omega))
    (ne _ _ (by rw [cntP_val, flogP_val]; omega)) (ne _ _ (by rw [dstP_val, flogP_val]; omega))
    0 0 cap capL (List.ofFn w).flatten hL (fun _ => 0) (extT n r.final.tapes cap capL) rfl rfl rfl rfl
    (by rw [hBout, ZeroPadding.pad_zero]) (by rw [hBcnt, ZeroPadding.pad_zero])
    (extT_dst n _ cap capL) (extT_flog n _ cap capL)
  refine ⟨Function.update (extT n r.final.tapes cap capL) (dstP n)
      (ZeroPadding.pad cap (frame (List.ofFn w).flatten)),
    step2.seq step3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (ne _ _ (by rw [outP_val, dstP_val]; omega)), hBout]
  · rw [Function.update_of_ne (ne _ _ (by rw [cntP_val, dstP_val]; omega)), hBcnt]
  · rw [Function.update_self]
  · intro i
    have hi := i.isLt
    rw [Function.update_of_ne (ne _ _ (by rw [srcP_val, dstP_val]; omega)), srcP,
      extT_left, hkeep, ht]
    simp [tapes, srcT, hi]
  · rw [Function.update_of_ne (ne _ _ (by rw [logP_val, dstP_val]; omega)), logP, extT_left,
      hkeep, ht]
    simp [tapes, logT]
  · rw [Function.update_of_ne (ne _ _ (by rw [flogP_val, dstP_val]; omega)), extT_flog]

end
end NearCubicWires.SourceRequest.FieldPass
