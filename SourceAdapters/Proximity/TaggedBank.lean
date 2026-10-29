import SourceAdapters.Proximity.DecoderMachine

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual tagged source-program invocation. The payload
is copied and rewound before the selected program starts on a fresh bank. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TaggedCalls

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.CheckedPCPP

abbrev State (N : ℕ) := WState (N + 2) 1

def slots (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) (i : Fin p.tapeCount) : Fin (N + 3) :=
  if i.val = 0 then ⟨1, by omega⟩ else if i = p.outputTape then ⟨2, by omega⟩ else ⟨i.val + 3, by have hi := i.isLt; omega⟩

theorem slots_injective (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) : Function.Injective (slots p N hN) := by
  intro i j h
  have hv := congrArg Fin.val h
  dsimp [slots] at hv
  split_ifs at hv
  all_goals first | exact Fin.ext (by omega) | simp_all
  all_goals exact Fin.ext hv

theorem slots_zero (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) (i : Fin p.tapeCount) :
    slots p N hN i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change (slots p N hN i).val = 0 at hv
  by_cases hz : i.val = 0
  · have hs : (slots p N hN i).val = 1 := by simp [slots, hz]
    rw [hs] at hv
    omega
  · by_cases ho : i = p.outputTape
    · have hs : (slots p N hN i).val = 2 := by rw [slots, if_neg hz, if_pos ho]
      rw [hs] at hv
      omega
    · have hs : (slots p N hN i).val = i.val + 3 := by rw [slots, if_neg hz, if_neg ho]
      rw [hs] at hv
      omega

@[simp] theorem slots_output (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) : slots p N hN p.outputTape = 2 := by
  apply Fin.ext
  simp only [slots, if_neg p.outputFresh]
  exact (Nat.mod_eq_of_lt (by omega : 2 < N + 3)).symm

def initial (N : ℕ) (tag : Bool) (word : List Bool) : State N := idealStart (N + 2) 1 (tag :: word) (fun _ => 0)
def atTag (N : ℕ) (tag : Bool) (word : List Bool) := (initial N tag word).seth 0 1
def atPayload (N : ℕ) (tag : Bool) (word : List Bool) := (initial N tag word).seth 0 2

def loaded (N : ℕ) (tag : Bool) (word : List Bool) :=
  ((initial N tag word).sets 1 (frame word)).seth 0 (2 + 2 * word.length)

theorem load_payload (N : ℕ) (tag : Bool) (word : List Bool) :
    WExec (2 * word.length + 2) (Glue.copyFrameW 0 1 0) (atPayload N tag word) (loaded N tag word)
      (32 * word.length + 16) := by
  have he := Glue.copyFrameW_spec (2 * word.length + 2) (0 : Fin (N + 3)) 1 (by intro he; have hv := congrArg Fin.val he; simp at hv) (0 : Fin 1)
    word [true, tag] [] (atPayload N tag word)
    (by change frame (tag :: word) = [true, tag] ++ frame word ++ []; simp [frame])
    rfl (by simp [atPayload, initial, idealStart]) (by simp [atPayload, initial, idealStart])
    rfl le_rfl
  refine he.cast _ ?_ (by omega)
  apply WState.eq <;> simp [atPayload, loaded]

theorem loaded_heads (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) (tag : Bool) (word : List Bool)
    (i : Fin p.tapeCount) : (loaded N tag word).sh (slots p N hN i) = 0 := by
  simp [loaded, initial, idealStart, slots_zero p N hN i]

theorem loaded_tapes (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) (tag : Bool) (word : List Bool)
    (i : Fin p.tapeCount) : (loaded N tag word).st (slots p N hN i) = p.inputTapes word i := by
  have h21 : (2 : Fin (N + 3)) ≠ 1 := by
    intro he
    have hv := congrArg Fin.val he
    change 2 % (N + 3) = 1 at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have h20 : (2 : Fin (N + 3)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change 2 % (N + 3) = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hs : slots p N hN p.outputTape = 2 := slots_output p N hN
  by_cases hi : i.val = 0
  · simp [slots, hi, loaded, Program.inputTapes]
  · by_cases ho : i = p.outputTape
    · subst i
      rw [hs]
      simp [loaded, initial, idealStart, Program.inputTapes, p.outputFresh, h21, h20]
    · have h1 : (⟨i.val + 3, by have hh := i.isLt; omega⟩ : Fin (N + 3)) ≠ 1 := by
        intro he; have hv := congrArg Fin.val he; simp only [Fin.val_one] at hv; omega
      simp [slots, hi, ho, loaded, initial, idealStart, Program.inputTapes, h1]

noncomputable def branch (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) : WMX (N + 2) 1 :=
  .seq (.wm (.fwd 0)) (.seq (.wm (Glue.copyFrameW 0 1 0)) (.mach p.machine (slots p N hN)))

theorem branch_run (p : Program) (N : ℕ) (hN : p.tapeCount ≤ N) (tag : Bool) (word out : List Bool)
    (budget : ℕ) (receipt : ExecutionReceipt p.tapeCount p.stateCount)
    (hr : run p.machine budget (p.inputTapes word) = some receipt)
    (hout : receipt.final.tapes p.outputTape = out) :
    ∃ τ : State N, WXExec (2 * word.length + 2) (branch p N hN) (atTag N tag word) τ
      (32 * word.length + budget + 19) ∧ τ.st 2 = out := by
  have hinput : (fun i => (loaded N tag word).st (slots p N hN i)) = p.inputTapes word :=
    funext (loaded_tapes p N hN tag word)
  have hr' : run p.machine budget (fun i => (loaded N tag word).st (slots p N hN i)) = some receipt := by
    rw [hinput]; exact hr
  obtain ⟨τ, he, hd⟩ := WXExec.mach_run (2 * word.length + 2) (slots_injective p N hN)
    (loaded N tag word) (loaded_heads p N hN tag word) hr'
  have hf : WExec (2 * word.length + 2) (.fwd 0) (atTag N tag word) (atPayload N tag word) 1 := by
    simpa [atTag, atPayload, wseth_seth] using WExec.fwd (cap := 2 * word.length + 2) (0 : Fin (N + 3)) (atTag N tag word)
  refine ⟨τ, (WXExec.seq (WXExec.wm hf) (WXExec.seq (WXExec.wm (load_payload N tag word)) he)).cast
      _ rfl (by omega), ?_⟩
  simpa using (hd.st p.outputTape).trans hout

end NearCubicGates.Adapters.Proximity.TaggedCalls
