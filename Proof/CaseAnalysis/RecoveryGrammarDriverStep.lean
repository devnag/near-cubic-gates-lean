import Proof.CaseAnalysis.RecoveryGrammarPath

/-! The node/output bodies physically advance the retained bound driver
once. The padding loop subsequently consumes that exact remaining suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriver
open LocalBitMultitape Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads {t : ℕ} (H : Fin t→ℕ) (pos : ℕ) : Fin (t+1)→ℕ:=
  Fin.addCases (m:=t) (n:=1) (motive:=fun _=>ℕ) H (fun _=>pos)
def data {t : ℕ} (A : Fin t→List Bool) (bits : List Bool) : Fin (t+1)→List Bool:=
  Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) A (fun _=>bits)
def lastSlot : Fin 1→Fin 113:=fun _=>112
noncomputable def move:=RecoveryFocus.machine lastSlot RecoveryBoundedNativeUnaryFlag.advance

theorem move_run (H : Fin 112→ℕ) (A : Fin 112→List Bool) (pos : ℕ) (bits : List Bool) :
    ∃ r,runFrom move 1 ⟨move.start,heads H pos,data A bits⟩=some r ∧ r.steps=1 ∧
      r.final.heads=heads H (pos+1) ∧ r.final.tapes=data A bits := by
  obtain ⟨a,ar,af,as⟩:=RecoveryBoundedNativeUnaryFlag.advance_run pos bits
  obtain ⟨r,rr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock lastSlot (by decide)
    RecoveryBoundedNativeUnaryFlag.advance _ (heads H pos) (data A bits)
    ⟨0,fun _=>pos,fun _=>bits⟩ (by intro j;fin_cases j;rfl) (by intro j;fin_cases j;rfl) a ar
  refine ⟨r,rr,rs.trans as,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=112) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simpa only [heads,Fin.addCases_left] using
        (keep (j.castAdd 1) (by intro k he;have hv:=congrArg Fin.val he;change 112=j.val at hv;omega)).1
    · fin_cases j
      change r.final.heads (lastSlot 0)=pos+1
      simpa only [af] using rh 0
  · funext i
    refine Fin.addCases (m:=112) (n:=1) (fun j=>?_) (fun j=>?_) i
    · exact (keep (j.castAdd 1) (by intro k he;have hv:=congrArg Fin.val he;change 112=j.val at hv;omega)).2
    · fin_cases j
      change r.final.tapes (lastSlot 0)=bits
      simpa only [af] using rt 0

noncomputable def bump {s : ℕ} (body : Machine 112 s):=Composition.machine (TapeEmbedding.machine 1 body) move

theorem bump_run {s : ℕ} (body : Machine 112 s) (fuel : ℕ) (c : Configuration 112 s)
    (pos : ℕ) (bits : List Bool) (a : ExecutionReceipt 112 s) (ar : runFrom body fuel c=some a) (hc : c.control=body.start) :
    ∃ r,runFrom (bump body) (fuel+2) ⟨(bump body).start,heads c.heads pos,data c.tapes bits⟩=some r ∧
      r.steps=a.steps+2 ∧ r.final.heads=heads a.final.heads (pos+1) ∧ r.final.tapes=data a.final.tapes bits := by
  let embedded:=TapeEmbedding.receipt (fun _ : Fin 1=>pos) (fun _ : Fin 1=>bits) a
  have er:=TapeEmbedding.run_embed body (fun _ : Fin 1=>pos) (fun _ : Fin 1=>bits) _ _ a ar
  obtain ⟨b,br,bs,bh,bt⟩:=move_run a.final.heads a.final.tapes pos bits
  have br' : runFrom move 1 (restart embedded.final move.start)=some b:=br
  have joined:=Composition.run_join (TapeEmbedding.machine 1 body) move _ _ _ embedded b er br'
  have initial : Composition.leftConfig 2 (TapeEmbedding.config (fun _ : Fin 1=>pos) (fun _ : Fin 1=>bits) c)=
      (⟨(bump body).start,heads c.heads pos,data c.tapes bits⟩ : Configuration 113 _) := by
    apply configuration_ext
    · simp only [Composition.leftConfig,TapeEmbedding.config,bump,Composition.machine,TapeEmbedding.machine,hc]
    · rfl
    · rfl
  rw [initial] at joined
  have cost : fuel+1+1=fuel+2:=by omega
  rw [cost] at joined
  refine ⟨joinedReceipt embedded b,joined,?_,bh,bt⟩
  change a.steps+1+b.steps=a.steps+2
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriver
