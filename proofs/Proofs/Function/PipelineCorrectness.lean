/-
  Ephemaral — Pipeline Correctness Proofs
  Machine-checked proofs that the pipeline orchestration preserves key safety properties.

  The compiler correctness (Compile → SMT-LIB) is proved in Correctness.lean.
  This file proves properties of the pipeline AROUND the compiler:
  routing, augmentation, validation — the unproved glue that caused real bugs
  in experiments (dinero.js, medusa, payload).
-/
import Proofs.Function.Pipeline

-- Definitions

/-- Two string lists have no overlap: no element belongs to both. -/
def NoOverlap (l₁ l₂ : List String) : Prop :=
  ∀ x, x ∈ l₁ → x ∉ l₂

-- Augmentation preserves disjointness

/-- The filter condition `!params.contains c` guarantees every element
    of the result is absent from `params`. -/
theorem filter_not_in_params (invConsts inputFields params : List String) :
    ∀ x, x ∈ (invConsts.filter fun c => !inputFields.contains c && !params.contains c) →
    x ∉ params := by
  intro x hx
  simp [List.mem_filter] at hx
  obtain ⟨_, _, h_not_params⟩ := hx
  simpa using h_not_params

/-- If NoOverlap(inputFields, params) before augmentation, then
    NoOverlap(augmentFields inputFields params invConsts, params) after.
    The filter excludes params. -/
theorem augmentFields_preserves_noOverlap
    (inputFields params invConsts : List String)
    (h : NoOverlap inputFields params) :
    NoOverlap (augmentFields inputFields params invConsts) params := by
  unfold augmentFields NoOverlap
  intro x hx
  simp [List.mem_append] at hx
  rcases hx with h_orig | ⟨_, _, h_not_params⟩
  · exact h x h_orig
  · simpa using h_not_params

-- Validation guarantees no name shadowing

/-- findOverlap returns [] iff NoOverlap holds.
    Connects the runtime check in verifyFunction to the proof-level property. -/
theorem findOverlap_empty_iff_noOverlap (inputFields params : List String) :
    findOverlap inputFields params = [] ↔ NoOverlap inputFields params := by
  unfold findOverlap NoOverlap
  constructor
  · intro h_empty x hx h_in
    have h_mem : x ∈ inputFields.filter params.contains := by
      simp [List.mem_filter]; exact ⟨hx, h_in⟩
    simp [h_empty] at h_mem
  · intro h_no
    induction inputFields with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter]
      have hx_not : x ∉ params := h_no x (by simp)
      split
      · rename_i h_contains
        exact absurd (List.contains_iff_mem.mp h_contains) hx_not
      · exact ih (fun y hy => h_no y (by simp [hy]))

/-- findOverlap = [] at entry implies NoOverlap after augmentation.
    Composes findOverlap_empty_iff_noOverlap with augmentFields_preserves_noOverlap. -/
theorem pipeline_noShadowing
    (inputFields params invConsts : List String)
    (h_valid : findOverlap inputFields params = []) :
    NoOverlap (augmentFields inputFields params invConsts) params := by
  exact augmentFields_preserves_noOverlap inputFields params invConsts
    ((findOverlap_empty_iff_noOverlap inputFields params).mp h_valid)

-- Routing completeness

/-- If extractBlockRoot returns a root that matches a paramType, then routeOneBlock
    puts the block in paramBlocks. Guarantees typed-param invariants aren't dropped during routing. -/
theorem routeOneBlock_paramComplete
    (inputType : String) (paramTypes : List String)
    (inp par skip : List String) (block : String) (root : String)
    (h_root : extractBlockRoot block = some root)
    (h_param : paramTypes.any (· == root.toLower) = true) :
    block ∈ (routeOneBlock inputType paramTypes (inp, par, skip) block).2.1 := by
  simp only [routeOneBlock, h_root]
  split
  · simp
  · rename_i h_not_both
    split
    · rename_i h_isInput
      simp only [Bool.and_eq_true] at h_not_both
      exact absurd ⟨h_isInput, h_param⟩ h_not_both
    · simp

-- Parameter precondition resolution

/-- If a fragment has a const matching a param name, resolveParamPreconditions keeps it.
    With routeOneBlock_paramComplete, this shows .aral blocks reach the final verification context. -/
theorem resolveParamPreconditions_scalar_survives
    (funRepr : FunctionRepr) (frags : List CompiledInvariant)
    (frag : CompiledInvariant) (h_mem : frag ∈ frags)
    (h_scalar : frag.consts.any (funRepr.params.contains ·) = true) :
    frag ∈ resolveParamPreconditions funRepr frags := by
  unfold resolveParamPreconditions
  simp only [List.mem_filterMap]
  refine ⟨frag, h_mem, ?_⟩
  simp only [h_scalar, ↓reduceIte]
