import Proof.PCP.PCPOuterCopy

namespace NearCubicWires.RepairOrdinary.PCPOuter
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (a b c d : List Bool) := [a,b,c,d]
def size (a b c d : List Bool) := a.length+b.length+c.length+d.length
def stream (a b c d : List Bool) := ((frame a++frame b)++frame c)++frame d
def sources (a b c d sa sb sc sd : List Bool) : Fin 132 → List Bool :=
  fun i => if i=0 then frame a++sa else if i=1 then frame b++sb
    else if i=2 then frame c++sc else if i=3 then frame d++sd else []
def fieldHeads (a b c d : List Bool) : Fin 132 → ℕ :=
  fun i => if i=0 then 2*a.length+1 else if i=1 then 2*b.length+1
    else if i=2 then 2*c.length+1 else if i=3 then 2*d.length+1
    else if i=4 then (stream a b c d).length else 0
def fieldTapes (a b c d sa sb sc sd : List Bool) :=
  Function.update (sources a b c d sa sb sc sd) 4 (stream a b c d)
noncomputable def copies := Composition.machine
  (Composition.machine (Composition.machine (copy (0 : Fin 132) 4) (copy 1 4)) (copy 2 4)) (copy 3 4)

theorem stream_length (a b c d : List Bool) :
    (stream a b c d).length=2*size a b c d+4 := by
  simp only [stream,List.length_append,frame_length,size]
  omega

theorem stream_fields (a b c d : List Bool) :
    stream a b c d=FieldList.stream (fields a b c d) := by
  simp [stream,fields,FieldList.stream,List.append_assoc]

theorem copies_run (a b c d sa sb sc sd : List Bool) :
    Exact copies (2*size a b c d+7) (fun _ => 0) (sources a b c d sa sb sc sd)
      (fieldHeads a b c d) (fieldTapes a b c d sa sb sc sd) := by
  let input := sources a b c d sa sb sc sd
  let h₁ := copiedHeads (0 : Fin 132) 4 a [] (fun _ => 0)
  let h₂ := copiedHeads (1 : Fin 132) 4 b (frame a) h₁
  let h₃ := copiedHeads (2 : Fin 132) 4 c (frame a++frame b) h₂
  let h₄ := copiedHeads (3 : Fin 132) 4 d ((frame a++frame b)++frame c) h₃
  have r₁ := copy_run (0 : Fin 132) 4 (by decide) a sa [] (fun _ => 0) input
    rfl rfl (by rfl) (by rfl)
  simp only [List.nil_append] at r₁
  have r₂ := copy_run (1 : Fin 132) 4 (by decide) b sb (frame a) h₁
    (Function.update input 4 (frame a))
    (by simp [h₁,copiedHeads]) (by simp [h₁,copiedHeads])
    (by simp [input,sources]) (by simp)
  have r₃ := copy_run (2 : Fin 132) 4 (by decide) c sc (frame a++frame b) h₂
    (Function.update input 4 (frame a++frame b))
    (by simp [h₂,h₁,copiedHeads]) (by simp [h₂,copiedHeads])
    (by simp [input,sources]) (by simp)
  have r₄ := copy_run (3 : Fin 132) 4 (by decide) d sd ((frame a++frame b)++frame c) h₃
    (Function.update input 4 ((frame a++frame b)++frame c))
    (by simp [h₃,h₂,h₁,copiedHeads]) (by simp [h₃,copiedHeads])
    (by simp [input,sources]) (by simp)
  simp only [Function.update_idem] at r₂ r₃ r₄
  have joined := exact_join (exact_join (exact_join r₁ r₂) r₃) r₄
  have hc : (((2*a.length+1)+1+(2*b.length+1))+1+(2*c.length+1))+1+(2*d.length+1)=
      2*size a b c d+7 := by unfold size; omega
  rw [hc] at joined
  have hh : h₄=fieldHeads a b c d := by
    funext i
    by_cases h0 : i=0
    · subst i; simp [h₄,h₃,h₂,h₁,copiedHeads,fieldHeads]
    by_cases h1 : i=1
    · subst i; simp [h₄,h₃,h₂,h₁,copiedHeads,fieldHeads]
    by_cases h2 : i=2
    · subst i; simp [h₄,h₃,h₂,h₁,copiedHeads,fieldHeads]
    by_cases h3 : i=3
    · subst i; simp [h₄,h₃,h₂,h₁,copiedHeads,fieldHeads]
    by_cases h4 : i=4
    · subst i; simp [h₄,copiedHeads,fieldHeads,stream]
    simp [h₄,h₃,h₂,h₁,copiedHeads,fieldHeads,h0,h1,h2,h3,h4]
  change Exact copies _ _ _ h₄ _ at joined
  rw [hh] at joined
  exact joined

end NearCubicWires.RepairOrdinary.PCPOuter
