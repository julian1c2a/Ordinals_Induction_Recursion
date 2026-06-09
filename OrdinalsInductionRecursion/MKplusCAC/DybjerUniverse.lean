import OrdinalsInductionRecursion.MKplusCAC.MKplusCACAxioms
import OrdinalsInductionRecursion.MKplusCAC.Tarski
import OrdinalsInductionRecursion.UnivSets.EmbedDybjer

universe u

namespace MKplusCAC

open UnivSets

/--
  La clase que representa todo el universo de conjuntos de DybjerSet.
  Un elemento `x` pertenece a `DybjerUniverse` si existe un `d : DybjerSet.DSet`
  cuya inmersión `embedDSet d` es exactamente `x`.
-/
def DybjerUniverse : Class :=
  fun (x : USet.{u+1}) => ∃ d : DybjerSet.DSet, x = embedDSet d

-- Queremos demostrar que DybjerUniverse es un conjunto, no una clase propia.
-- Esto requiere el uso de universos de Lean: el árbol que contiene a todos los
-- elementos de DybjerSet.Tree.{u} vivirá en UnivSets.Tree.{u+1}.

/-- El árbol de Aczel que recolecta a todo el universo de DybjerSet. -/
def dybjerUniverseTree : UnivSets.Tree.{u+1} :=
  UnivSets.Tree.sup (α := ULift.{u+1, 1} DybjerSet.Tree) fun t => embedDybjerTree t.down

/-- El conjunto de Aczel correspondiente al universo de Dybjer. -/
def dybjerUniverseUSet : USet.{u+1} :=
  Quotient.mk UnivSets.Tree.Setoid dybjerUniverseTree

/--
  El universo de Dybjer no es una clase propia, ¡es un conjunto en el modelo MK⁺!
  (Nota: este conjunto vive en el universo de conjuntos de nivel u+1).
-/
theorem isSet_dybjerUniverse : IsSet DybjerUniverse.{u} := by
  -- El conjunto que atestigua que DybjerUniverse es un conjunto es `dybjerUniverseUSet`.
  apply (isSet_iff_exists_uset _).mpr
  refine ⟨dybjerUniverseUSet, ?_⟩
  -- Tenemos que probar que DybjerUniverse y (toClass dybjerUniverseUSet)
  -- tienen exactamente los mismos elementos.
  apply MK_Ext
  intro x hx
  constructor
  · rintro ⟨d, h_eq, ⟨d', hd_eq⟩⟩
    refine ⟨d, h_eq, ?_⟩
    rw [hd_eq]
    -- We need to prove: embedDSet d' ∈ dybjerUniverseUSet
    -- dybjerUniverseUSet is Quotient.mk Setoid dybjerUniverseTree
    -- d' is a DSet. We can use Quotient.ind on d'
    induction d' using Quotient.ind
    rename_i t
    -- Now embedDSet (Quotient.mk t) = Quotient.mk (embedDybjerTree t)
    -- We need to prove UnivSets.Tree.Mem (embedDybjerTree t) dybjerUniverseTree
    change UnivSets.Tree.Mem (UnivSets.embedDybjerTree t) (UnivSets.Tree.sup fun (a : ULift DybjerSet.Tree) => UnivSets.embedDybjerTree a.down)
    exact UnivSets.Tree.mem_sup_equiv_new (ULift.up t) (UnivSets.Tree.Equiv_refl _)
  · rintro ⟨d, h_eq, h_mem⟩
    refine ⟨d, h_eq, ?_⟩
    induction d using Quotient.ind
    rename_i x_tree
    -- h_mem : UnivSets.Tree.Mem x_tree dybjerUniverseTree
    -- We can use cases on h_mem
    cases h_mem
    rename_i a h1 h2
    -- so x_tree is equiv to embedDybjerTree a.down
    -- and a.down is a DybjerSet.Tree
    have h_equiv : UnivSets.Tree.Equiv x_tree (UnivSets.embedDybjerTree a.down) := ⟨h1, h2⟩
    -- Thus, d = embedDSet (Quotient.mk a.down)
    refine ⟨Quotient.mk DybjerSet.Tree.Setoid a.down, ?_⟩
    change Quotient.mk UnivSets.Tree.Setoid x_tree = Quotient.mk UnivSets.Tree.Setoid (UnivSets.embedDybjerTree a.down)
    exact Quotient.sound h_equiv

theorem exists_of_mem_embedDSet {y : USet.{u+1}} {d : DybjerSet.DSet} (h : y ∈ embedDSet d) : ∃ x : DybjerSet.DSet, y = embedDSet x := by
  induction d using Quotient.ind
  rename_i t
  induction y using Quotient.ind
  rename_i y_tree
  cases t
  case zero =>
    change UnivSets.Tree.Mem y_tree UnivSets.emptyTree at h
    exfalso
    cases h
    rename_i a h1 h2
    cases a
  case succ x =>
    change UnivSets.Tree.Mem y_tree (UnivSets.Tree.sup fun _ : ULift Unit => UnivSets.embedDybjerTree x) at h
    cases h
    rename_i a h1 h2
    refine ⟨Quotient.mk DybjerSet.Tree.Setoid x, ?_⟩
    change Quotient.mk UnivSets.Tree.Setoid y_tree = Quotient.mk UnivSets.Tree.Setoid (UnivSets.embedDybjerTree x)
    exact Quotient.sound ⟨h1, h2⟩
  case sup A c f =>
    change UnivSets.Tree.Mem y_tree (UnivSets.Tree.sup fun a : ULift A => UnivSets.embedDybjerTree (f a.down)) at h
    cases h
    rename_i a h1 h2
    refine ⟨Quotient.mk DybjerSet.Tree.Setoid (f a.down), ?_⟩
    change Quotient.mk UnivSets.Tree.Setoid y_tree = Quotient.mk UnivSets.Tree.Setoid (UnivSets.embedDybjerTree (f a.down))
    exact Quotient.sound ⟨h1, h2⟩

theorem isTransitive_dybjerUniverse : IsTransitive DybjerUniverse.{u} := by
  intro x hx y hy
  obtain ⟨d_x, hx_eq, hd_x⟩ := hx
  obtain ⟨d_y, hy_eq, hy_mem⟩ := hy
  rw [hx_eq] at hy_mem
  obtain ⟨d, hd_eq⟩ := hd_x
  rw [hd_eq] at hy_mem
  change d_y ∈ embedDSet d at hy_mem
  obtain ⟨d', hd'_eq⟩ := exists_of_mem_embedDSet hy_mem
  refine ⟨d_y, hy_eq, ?_⟩
  exact ⟨d', hd'_eq⟩



theorem isGrothendieck_pair_dybjerUniverse : ∀ x y : Class, Mem x DybjerUniverse.{u} → Mem y DybjerUniverse.{u} → ∃ p : Class, IsSet p ∧ Mem p DybjerUniverse.{u} ∧ ∀ u : Class, Mem u p ↔ (u = x ∨ u = y) := by
  intro x y hx hy
  obtain ⟨d_x, hx_eq, hd_x⟩ := hx
  obtain ⟨d_y, hy_eq, hd_y⟩ := hy
  obtain ⟨dx, hdx_eq⟩ := hd_x
  obtain ⟨dy, hdy_eq⟩ := hd_y
  rw [hdx_eq] at hx_eq
  rw [hdy_eq] at hy_eq
  -- x = toClass (embedDSet dx), y = toClass (embedDSet dy)
  refine ⟨toClass (embedDSet (DybjerSet.pair dx dy)), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (isSet_iff_exists_uset _).mpr ⟨embedDSet (DybjerSet.pair dx dy), rfl⟩
  · refine ⟨embedDSet (DybjerSet.pair dx dy), rfl, ?_⟩
    exact ⟨DybjerSet.pair dx dy, rfl⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨u_set, hu_eq, hu_mem⟩ := hu
      obtain ⟨du, hdu_eq⟩ := exists_of_mem_embedDSet hu_mem
      rw [hdu_eq] at hu_mem
      have h_mem_dset := embedDSet_mem_rev hu_mem
      rw [DybjerSet.mem_pair_iff] at h_mem_dset
      cases h_mem_dset
      case inl h_eq =>
        left; rw [hu_eq, hdu_eq, h_eq, ←hx_eq]
      case inr h_eq =>
        right; rw [hu_eq, hdu_eq, h_eq, ←hy_eq]
    · intro hu
      cases hu
      case inl h_eq =>
        rw [h_eq, hx_eq]
        -- embedDSet dx ∈ embedDSet (pair dx dy)
        refine ⟨embedDSet dx, rfl, ?_⟩
        apply embedDSet_mem
        rw [DybjerSet.mem_pair_iff]
        left; rfl
      case inr h_eq =>
        rw [h_eq, hy_eq]
        refine ⟨embedDSet dy, rfl, ?_⟩
        apply embedDSet_mem
        rw [DybjerSet.mem_pair_iff]
        right; rfl


theorem isGrothendieck_union_dybjerUniverse : ∀ x : Class, Mem x DybjerUniverse.{u} → ∃ s : Class, IsSet s ∧ Mem s DybjerUniverse.{u} ∧ ∀ u : Class, Mem u s ↔ ∃ v : Class, Mem u v ∧ Mem v x := by
  intro x hx
  obtain ⟨d_x, hx_eq, hd_x⟩ := hx
  obtain ⟨dx, hdx_eq⟩ := hd_x
  rw [hdx_eq] at hx_eq
  refine ⟨toClass (embedDSet (DybjerSet.sUnion dx)), ?_⟩
  refine ⟨(isSet_iff_exists_uset _).mpr ⟨embedDSet (DybjerSet.sUnion dx), rfl⟩, ?_⟩
  refine ⟨⟨embedDSet (DybjerSet.sUnion dx), rfl, ⟨DybjerSet.sUnion dx, rfl⟩⟩, ?_⟩
  intro u
  constructor
  · intro hu
    obtain ⟨u_set, hu_eq, hu_mem⟩ := hu
    obtain ⟨du, hdu_eq⟩ := exists_of_mem_embedDSet hu_mem
    rw [hdu_eq] at hu_mem
    have h_mem_dset := embedDSet_mem_rev hu_mem
    rw [DybjerSet.mem_sUnion_iff] at h_mem_dset
    obtain ⟨dv, hdu_dv, hdv_dx⟩ := h_mem_dset
    refine ⟨toClass (embedDSet dv), ?_⟩
    constructor
    · rw [hu_eq, hdu_eq]
      exact ⟨embedDSet du, rfl, embedDSet_mem hdu_dv⟩
    · rw [hx_eq]
      exact ⟨embedDSet dv, rfl, embedDSet_mem hdv_dx⟩
  · intro hu
    obtain ⟨v, huv, hvx⟩ := hu
    rw [hx_eq] at hvx
    obtain ⟨v_set, hv_eq, hv_mem⟩ := hvx
    obtain ⟨dv, hdv_eq⟩ := exists_of_mem_embedDSet hv_mem
    rw [hdv_eq] at hv_mem
    have hdv_dx := embedDSet_mem_rev hv_mem
    rw [hv_eq, hdv_eq] at huv
    obtain ⟨u_set, hu_eq, hu_mem⟩ := huv
    obtain ⟨du, hdu_eq⟩ := exists_of_mem_embedDSet hu_mem
    rw [hdu_eq] at hu_mem
    have hdu_dv := embedDSet_mem_rev hu_mem
    rw [hu_eq, hdu_eq]
    refine ⟨embedDSet du, rfl, ?_⟩
    apply embedDSet_mem
    rw [DybjerSet.mem_sUnion_iff]
    exact ⟨dv, hdu_dv, hdv_dx⟩


theorem isGrothendieck_powerset_dybjerUniverse : ∀ x : Class, Mem x DybjerUniverse.{u} → ∃ p : Class, IsSet p ∧ Mem p DybjerUniverse.{u} ∧ ∀ u, Mem u p ↔ IsSet u ∧ ∀ v, Mem v u → Mem v x := by
  intro x hx
  obtain ⟨d_x, hx_eq, hd_x⟩ := hx
  obtain ⟨dx, hdx_eq⟩ := hd_x
  rw [hdx_eq] at hx_eq
  refine ⟨toClass (embedDSet (DybjerSet.powerset dx)), ?_⟩
  refine ⟨(isSet_iff_exists_uset _).mpr ⟨embedDSet (DybjerSet.powerset dx), rfl⟩, ?_⟩
  refine ⟨⟨embedDSet (DybjerSet.powerset dx), rfl, ⟨DybjerSet.powerset dx, rfl⟩⟩, ?_⟩
  intro u
  constructor
  · intro hu
    obtain ⟨u_set, hu_eq, hu_mem⟩ := hu
    obtain ⟨du, hdu_eq⟩ := exists_of_mem_embedDSet hu_mem
    rw [hdu_eq] at hu_mem
    have h_mem_dset := embedDSet_mem_rev hu_mem
    rw [DybjerSet.mem_powerset_iff] at h_mem_dset
    rw [DybjerSet.subset_iff_forall_mem] at h_mem_dset
    refine ⟨(isSet_iff_exists_uset _).mpr ⟨u_set, hu_eq⟩, ?_⟩
    intro v hv
    rw [hu_eq] at hv
    obtain ⟨v_set, hv_eq, hv_mem⟩ := hv
    rw [hdu_eq] at hv_mem
    obtain ⟨dv, hdv_eq⟩ := exists_of_mem_embedDSet hv_mem
    rw [hdv_eq] at hv_mem
    have hdv_du := embedDSet_mem_rev hv_mem
    have hdv_dx := h_mem_dset dv hdv_du
    rw [hdv_eq] at hv_eq
    rw [hx_eq]
    exact ⟨embedDSet dv, hv_eq, embedDSet_mem hdv_dx⟩
  · intro hu
    obtain ⟨hu_set, h_sub⟩ := hu
    obtain ⟨u_set, hu_eq⟩ := (isSet_iff_exists_uset _).mp hu_set
    -- u ⊆ x. x = toClass (embedDSet dx). So u_set ⊆ embedDSet dx.
    -- We can lift dx to a Tree t_x.
    induction dx using Quotient.ind
    rename_i t_x
    let embedTree (t : DybjerSet.Tree) := embedDSet (Quotient.mk DybjerSet.Tree.Setoid t : DybjerSet.DSet)
    
    have dec_mem : ∀ i, Decidable (embedTree (DybjerSet.indexFun t_x i) ∈ u_set) := fun i => Classical.propDecidable _
    let g : DybjerSet.indexType t_x → Bool := fun i =>
      if embedTree (DybjerSet.indexFun t_x i) ∈ u_set then true else false
      
    let t_u := DybjerSet.filterTree t_x g
    
    -- First show that u_set = embedTree t_u
    have hu_eq_embed : u_set = embedTree t_u := by
      apply USet.ext
      · apply uset_subset_iff.mpr
        intro v hv
        have hv_u : Mem (toClass v) u := by rw [hu_eq]; exact ⟨v, rfl, hv⟩
        have hvx : Mem (toClass v) x := h_sub (toClass v) hv_u
        rw [hx_eq] at hvx
        obtain ⟨v_dset', hv_eq_dset', hv_mem_dset'⟩ := hvx
        -- hv_eq_dset' : toClass v = toClass v_dset'
        -- hv_mem_dset' : v_dset' ∈ embedDSet dx
        have hv_eq_v_dset' : v = v_dset' := toClass_inj.mp hv_eq_dset'
        rw [hv_eq_v_dset'] at hv
        rw [hv_eq_v_dset']
        have hv_mem : v_dset' ∈ embedTree t_x := hv_mem_dset'
        obtain ⟨v_dset, hv_eq_dset⟩ := exists_of_mem_embedDSet hv_mem
        have hv_mem2 : embedDSet v_dset ∈ embedTree t_x := by
          rw [← hv_eq_dset]
          exact hv_mem
        have hv_mem_dset : v_dset ∈ (Quotient.mk DybjerSet.Tree.Setoid t_x : DybjerSet.DSet) := embedDSet_mem_rev hv_mem2
        obtain ⟨v_t, hv_t_eq⟩ := Quotient.exists_rep v_dset
        have hv_mem_dset2 : (Quotient.mk DybjerSet.Tree.Setoid v_t : DybjerSet.DSet) ∈ (Quotient.mk DybjerSet.Tree.Setoid t_x : DybjerSet.DSet) := by
          rw [hv_t_eq]
          exact hv_mem_dset
        obtain ⟨i, hi_eq⟩ := DybjerSet.mem_iff_exists_index.mp hv_mem_dset2
        have h_embed_eq : embedTree v_t = embedTree (DybjerSet.indexFun t_x i) := by
          dsimp [embedTree]
          rw [Quotient.sound hi_eq]
        have hgi : g i = true := by
          change (if embedTree (DybjerSet.indexFun t_x i) ∈ u_set then true else false) = true
          split
          · rfl
          · rename_i h_not_mem
            have h_mem_u : embedTree (DybjerSet.indexFun t_x i) ∈ u_set := by
              rw [← h_embed_eq]
              have h_v_t_eq : embedTree v_t = v_dset' := by
                change embedDSet (Quotient.mk _ v_t) = v_dset'
                rw [hv_t_eq]
                exact hv_eq_dset.symm
              rw [h_v_t_eq]
              exact hv
            contradiction
        have h_vt_u : DybjerSet.Tree.Mem v_t t_u := DybjerSet.mem_filterTree_iff.mpr ⟨i, hgi, hi_eq⟩
        have hd_eq : v_dset' = embedTree v_t := by
          change v_dset' = embedDSet (Quotient.mk _ v_t)
          rw [hv_t_eq]
          exact hv_eq_dset
        rw [hd_eq]
        exact embedDSet_mem h_vt_u
      · apply uset_subset_iff.mpr
        intro w hw
        -- hw : w ∈ embedTree t_u
        obtain ⟨w_dset, hw_eq_dset⟩ := exists_of_mem_embedDSet hw
        have hw_mem2 : embedDSet w_dset ∈ embedTree t_u := by
          rw [← hw_eq_dset]
          exact hw
        have hw_mem_dset : w_dset ∈ (Quotient.mk DybjerSet.Tree.Setoid t_u : DybjerSet.DSet) := embedDSet_mem_rev hw_mem2
        obtain ⟨w_t, hw_t_eq⟩ := Quotient.exists_rep w_dset
        have hw_mem_dset2 : (Quotient.mk DybjerSet.Tree.Setoid w_t : DybjerSet.DSet) ∈ (Quotient.mk DybjerSet.Tree.Setoid t_u : DybjerSet.DSet) := by
          rw [hw_t_eq]
          exact hw_mem_dset
        -- hw_mem_dset2 : Quotient.mk _ w_t ∈ t_u
        obtain ⟨i, hgi, hi_eq⟩ := DybjerSet.mem_filterTree_iff.mp hw_mem_dset2
        have h_embed_eq : embedTree w_t = embedTree (DybjerSet.indexFun t_x i) := by
          dsimp [embedTree]
          rw [Quotient.sound hi_eq]
        change (if embedTree (DybjerSet.indexFun t_x i) ∈ u_set then true else false) = true at hgi
        split at hgi
        · rename_i h_mem
          have hd_eq : w = embedTree w_t := by
            change w = embedDSet (Quotient.mk _ w_t)
            rw [hw_t_eq]
            exact hw_eq_dset
          rw [hd_eq, h_embed_eq]
          exact h_mem
        · contradiction
    
    have ht_u_powerset : DybjerSet.Tree.Mem t_u (DybjerSet.powersetTree t_x) := by
      apply DybjerSet.mem_powersetTree_iff.mpr
      apply DybjerSet.Subset_iff_forall_Mem.mpr
      intro z hz
      obtain ⟨i, hgi, hi_eq⟩ := DybjerSet.mem_filterTree_iff.mp hz
      have h_mem_tx : DybjerSet.Tree.Mem (DybjerSet.indexFun t_x i) t_x := DybjerSet.mem_iff_exists_index.mpr ⟨i, DybjerSet.Tree.Equiv_refl _⟩
      exact DybjerSet.Tree.Equiv_Mem_trans hi_eq h_mem_tx

    rw [hu_eq, hu_eq_embed]
    exact ⟨embedTree t_u, rfl, embedDSet_mem ht_u_powerset⟩


theorem isGrothendieck_replacement_dybjerUniverse : ∀ x : Class, Mem x DybjerUniverse.{u} → ∀ f : Class → Class, (∀ y, Mem y x → Mem (f y) DybjerUniverse.{u}) → ∃ r : Class, IsSet r ∧ Mem r DybjerUniverse.{u} ∧ (∀ z, Mem z r ↔ ∃ y, Mem y x ∧ z = f y) := by
  intro x hx f hf
  obtain ⟨d_x, hx_eq, hd_x⟩ := hx
  obtain ⟨dx, hdx_eq⟩ := hd_x
  rw [hdx_eq] at hx_eq
  obtain ⟨t_x, ht_x_eq⟩ := Quotient.exists_rep dx
  let embedTree (t : DybjerSet.Tree) := embedDSet (Quotient.mk DybjerSet.Tree.Setoid t : DybjerSet.DSet)
  have h_x_eq_tree : x = toClass (embedTree t_x) := by
    rw [hx_eq, ← ht_x_eq]
  have hf' : ∀ i : DybjerSet.indexType t_x, ∃ t : DybjerSet.Tree, f (toClass (embedTree (DybjerSet.indexFun t_x i))) = toClass (embedTree t) := by
    intro i
    have hy_mem : MKplusCAC.Mem (toClass (embedTree (DybjerSet.indexFun t_x i))) x := by
      rw [h_x_eq_tree]
      exact ⟨embedTree (DybjerSet.indexFun t_x i), rfl, embedDSet_mem (DybjerSet.mem_iff_exists_index.mpr ⟨i, DybjerSet.Tree.Equiv_refl _⟩)⟩
    have hfy_univ := hf _ hy_mem
    obtain ⟨d_fy, hfy_eq, hdf_y⟩ := hfy_univ
    obtain ⟨df_y, hdf_eq⟩ := hdf_y
    rw [hdf_eq] at hfy_eq
    obtain ⟨t_fy, ht_fy_eq⟩ := Quotient.exists_rep df_y
    refine ⟨t_fy, ?_⟩
    rw [hfy_eq, ← ht_fy_eq]
  let B : DybjerSet.indexType t_x → DybjerSet.Tree := fun i => Classical.choose (hf' i)
  have hB : ∀ i : DybjerSet.indexType t_x, f (toClass (embedTree (DybjerSet.indexFun t_x i))) = toClass (embedTree (B i)) := fun i => Classical.choose_spec (hf' i)
  let t_r := DybjerSet.Tree.sup (DybjerSet.indexCode t_x) B
  have ht_r_embed : embedTree t_r = embedDSet (Quotient.mk _ t_r) := rfl
  refine ⟨toClass (embedTree t_r), ?_⟩
  refine ⟨(isSet_iff_exists_uset _).mpr ⟨embedTree t_r, rfl⟩, ?_⟩
  refine ⟨⟨embedTree t_r, rfl, ⟨Quotient.mk _ t_r, rfl⟩⟩, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨z_set, hz_eq, hz_mem⟩ := hz
    obtain ⟨z_dset, hz_dset_eq⟩ := exists_of_mem_embedDSet hz_mem
    have hz_mem2 : embedDSet z_dset ∈ embedTree t_r := by
      rw [← hz_dset_eq]
      exact hz_mem
    have hz_mem_dset : z_dset ∈ (Quotient.mk DybjerSet.Tree.Setoid t_r : DybjerSet.DSet) := embedDSet_mem_rev hz_mem2
    obtain ⟨z_t, hz_t_eq⟩ := Quotient.exists_rep z_dset
    have hz_mem_dset2 : (Quotient.mk DybjerSet.Tree.Setoid z_t : DybjerSet.DSet) ∈ (Quotient.mk DybjerSet.Tree.Setoid t_r : DybjerSet.DSet) := by
      rw [hz_t_eq]
      exact hz_mem_dset
    obtain ⟨i, hi_eq⟩ := DybjerSet.mem_iff_exists_index.mp hz_mem_dset2
    let i_x : DybjerSet.indexType t_x := i
    have h_embed_eq : embedTree z_t = embedTree (B i_x) := by
      dsimp [embedTree]
      rw [Quotient.sound hi_eq]
      rfl
    refine ⟨toClass (embedTree (DybjerSet.indexFun t_x i_x)), ?_, ?_⟩
    { rw [h_x_eq_tree]
      exact ⟨embedTree (DybjerSet.indexFun t_x i_x), rfl, embedDSet_mem (DybjerSet.mem_iff_exists_index.mpr ⟨i_x, DybjerSet.Tree.Equiv_refl _⟩)⟩ }
    { rw [hB i_x]
      rw [hz_eq]
      change toClass z_set = toClass (embedTree (B i_x))
      have hz_set_eq_zt : z_set = embedTree z_t := by
        change z_set = embedDSet (Quotient.mk _ z_t)
        rw [hz_t_eq]
        exact hz_dset_eq
      rw [hz_set_eq_zt, h_embed_eq] }
  · intro h
    obtain ⟨y, hy_mem, hz_eq⟩ := h
    rw [h_x_eq_tree] at hy_mem
    obtain ⟨y_set, hy_eq, hy_set_mem⟩ := hy_mem
    obtain ⟨y_dset, hy_dset_eq⟩ := exists_of_mem_embedDSet hy_set_mem
    have hy_mem2 : embedDSet y_dset ∈ embedTree t_x := by
      rw [← hy_dset_eq]
      exact hy_set_mem
    have hy_mem_dset : y_dset ∈ (Quotient.mk DybjerSet.Tree.Setoid t_x : DybjerSet.DSet) := embedDSet_mem_rev hy_mem2
    obtain ⟨y_t, hy_t_eq⟩ := Quotient.exists_rep y_dset
    have hy_mem_dset2 : (Quotient.mk DybjerSet.Tree.Setoid y_t : DybjerSet.DSet) ∈ (Quotient.mk DybjerSet.Tree.Setoid t_x : DybjerSet.DSet) := by
      rw [hy_t_eq]
      exact hy_mem_dset
    obtain ⟨i, hi_eq⟩ := DybjerSet.mem_iff_exists_index.mp hy_mem_dset2
    have hy_val : y = toClass (embedTree (DybjerSet.indexFun t_x i)) := by
      rw [hy_eq]
      have hy_set_eq_yt : y_set = embedTree y_t := by
        change y_set = embedDSet (Quotient.mk _ y_t)
        rw [hy_t_eq]
        exact hy_dset_eq
      rw [hy_set_eq_yt]
      dsimp [embedTree]
      rw [Quotient.sound hi_eq]
    rw [hy_val] at hz_eq
    rw [hB i] at hz_eq
    rw [hz_eq]
    let i_r : DybjerSet.indexType t_r := i
    have h_mem_tr : (Quotient.mk DybjerSet.Tree.Setoid (B i) : DybjerSet.DSet) ∈ (Quotient.mk DybjerSet.Tree.Setoid t_r : DybjerSet.DSet) := by
      exact DybjerSet.mem_iff_exists_index.mpr ⟨i_r, DybjerSet.Tree.Equiv_refl _⟩
    exact ⟨embedTree (B i), rfl, embedDSet_mem h_mem_tr⟩

theorem isGrothendieck_infinity_dybjerUniverse : ∃ w : Class, Mem w DybjerUniverse.{u} ∧
    (∃ e : Class, IsSet e ∧ (∀ u : Class, ¬Mem u e) ∧ Mem e w) ∧
    (∀ y : Class, Mem y w → ∃ s : Class, IsSet s ∧ Mem s w ∧ ∀ u : Class, Mem u s ↔ Mem u y ∨ u = y) := by
  let w_dset := DybjerSet.omegaSet
  let w := toClass (embedDSet w_dset)
  refine ⟨w, ?_, ?_, ?_⟩
  · exact ⟨embedDSet w_dset, rfl, ⟨w_dset, rfl⟩⟩
  · let empty_dset := DybjerSet.empty
    let e := toClass (embedDSet empty_dset)
    refine ⟨e, ?_, ?_, ?_⟩
    · exact (isSet_iff_exists_uset _).mpr ⟨embedDSet empty_dset, rfl⟩
    · intro u hu
      obtain ⟨u_set, hu_eq, hu_mem⟩ := hu
      obtain ⟨u_dset, hu_dset_eq⟩ := exists_of_mem_embedDSet hu_mem
      have hu_mem_dset : u_dset ∈ empty_dset := by
        have h1 : embedDSet u_dset ∈ embedDSet empty_dset := by
          rw [← hu_dset_eq]
          exact hu_mem
        exact embedDSet_mem_rev h1
      exact DybjerSet.not_mem_empty u_dset hu_mem_dset
    · have he_mem : empty_dset ∈ w_dset := by
        have h1 : DybjerSet.Tree.Mem DybjerSet.Tree.zero DybjerSet.omegaTree := by
          apply DybjerSet.mem_iff_exists_index.mpr
          exact ⟨(0 : Nat), DybjerSet.Tree.Equiv_refl _⟩
        exact h1
      exact ⟨embedDSet empty_dset, rfl, embedDSet_mem he_mem⟩
  · intro y hy
    obtain ⟨y_set, hy_eq, hy_mem⟩ := hy
    obtain ⟨y_dset, hy_dset_eq⟩ := exists_of_mem_embedDSet hy_mem
    have hy_mem_w : y_dset ∈ w_dset := by
      have h1 : embedDSet y_dset ∈ embedDSet w_dset := by
        rw [← hy_dset_eq]
        exact hy_mem
      exact embedDSet_mem_rev h1
    obtain ⟨y_t, hy_t_eq⟩ := Quotient.exists_rep y_dset
    have hy_mem_w_tree : DybjerSet.Tree.Mem y_t DybjerSet.omegaTree := by
      have h1 : (Quotient.mk DybjerSet.Tree.Setoid y_t : DybjerSet.DSet) ∈ (Quotient.mk DybjerSet.Tree.Setoid DybjerSet.omegaTree : DybjerSet.DSet) := by
        rw [hy_t_eq]
        exact hy_mem_w
      exact h1
    obtain ⟨n', hn_eq⟩ := DybjerSet.mem_iff_exists_index.mp hy_mem_w_tree
    let n : Nat := n'
    change DybjerSet.Tree.Equiv y_t (DybjerSet.natTree n) at hn_eq
    let s_t := DybjerSet.natTree (n + 1)
    let s_dset : DybjerSet.DSet := Quotient.mk DybjerSet.Tree.Setoid s_t
    let s := toClass (embedDSet s_dset)
    refine ⟨s, ?_, ?_, ?_⟩
    · exact (isSet_iff_exists_uset _).mpr ⟨embedDSet s_dset, rfl⟩
    · have hs_mem : s_dset ∈ w_dset := by
        have h1 : DybjerSet.Tree.Mem s_t DybjerSet.omegaTree := by
          apply DybjerSet.mem_iff_exists_index.mpr
          exact ⟨(n + 1 : Nat), DybjerSet.Tree.Equiv_refl _⟩
        exact h1
      exact ⟨embedDSet s_dset, rfl, embedDSet_mem hs_mem⟩
    · intro u
      constructor
      · intro hu
        obtain ⟨u_set, hu_eq, hu_mem⟩ := hu
        obtain ⟨u_dset, hu_dset_eq⟩ := exists_of_mem_embedDSet hu_mem
        have hu_mem_s : u_dset ∈ s_dset := by
          have h1 : embedDSet u_dset ∈ embedDSet s_dset := by
            rw [← hu_dset_eq]
            exact hu_mem
          exact embedDSet_mem_rev h1
        have hs_eq_insert : s_dset = DybjerSet.insert (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n)) (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n)) := rfl
        rw [hs_eq_insert] at hu_mem_s
        have hy_n_eq : (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n) : DybjerSet.DSet) = y_dset := by
          have h_y_t : (Quotient.mk DybjerSet.Tree.Setoid y_t : DybjerSet.DSet) = Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n) := Quotient.sound hn_eq
          rw [← hy_t_eq]
          exact h_y_t.symm
        rw [hy_n_eq] at hu_mem_s
        have h_or := DybjerSet.mem_insert_iff.mp hu_mem_s
        cases h_or with
        | inl h_eq =>
          right
          rw [hu_eq, hy_eq]
          rw [hu_dset_eq, hy_dset_eq]
          rw [h_eq]
        | inr h_mem_n =>
          left
          rw [hu_eq, hy_eq]
          rw [hu_dset_eq, hy_dset_eq]
          exact ⟨embedDSet u_dset, rfl, embedDSet_mem h_mem_n⟩
      · intro h_or
        cases h_or with
        | inl hu_y =>
          rw [hy_eq] at hu_y
          obtain ⟨u_set, hu_eq, hu_mem⟩ := hu_y
          rw [hy_dset_eq] at hu_mem
          obtain ⟨u_dset, hu_dset_eq⟩ := exists_of_mem_embedDSet hu_mem
          have hu_mem_y : u_dset ∈ y_dset := by
            have h1 : embedDSet u_dset ∈ embedDSet y_dset := by
              rw [← hu_dset_eq]
              exact hu_mem
            exact embedDSet_mem_rev h1
          have hs_eq_insert : s_dset = DybjerSet.insert y_dset y_dset := by
            have h_insert_n : s_dset = DybjerSet.insert (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n)) (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n)) := rfl
            rw [h_insert_n]
            have hy_n_eq : (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n) : DybjerSet.DSet) = y_dset := by
              have h_y_t : (Quotient.mk DybjerSet.Tree.Setoid y_t : DybjerSet.DSet) = Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n) := Quotient.sound hn_eq
              rw [← hy_t_eq]
              exact h_y_t.symm
            rw [hy_n_eq]
          have hu_mem_s : u_dset ∈ s_dset := by
            rw [hs_eq_insert]
            exact DybjerSet.mem_insert_iff.mpr (Or.inr hu_mem_y)
          have h2 : u = toClass (embedDSet u_dset) := by
            rw [hu_eq, hu_dset_eq]
          rw [h2]
          exact ⟨embedDSet u_dset, rfl, embedDSet_mem hu_mem_s⟩
        | inr hu_eq_y =>
          rw [hu_eq_y]
          have hs_eq_insert : s_dset = DybjerSet.insert y_dset y_dset := by
            have h_insert_n : s_dset = DybjerSet.insert (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n)) (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n)) := rfl
            rw [h_insert_n]
            have hy_n_eq : (Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n) : DybjerSet.DSet) = y_dset := by
              have h_y_t : (Quotient.mk DybjerSet.Tree.Setoid y_t : DybjerSet.DSet) = Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.natTree n) := Quotient.sound hn_eq
              rw [← hy_t_eq]
              exact h_y_t.symm
            rw [hy_n_eq]
          have hy_mem_s : y_dset ∈ s_dset := by
            rw [hs_eq_insert]
            exact DybjerSet.mem_insert_iff.mpr (Or.inl rfl)
          have h2 : y = toClass (embedDSet y_dset) := by
            rw [hy_eq, hy_dset_eq]
          rw [h2]
          exact ⟨embedDSet y_dset, rfl, embedDSet_mem hy_mem_s⟩


/-- Teorema Maestro: El Universo de Dybjer forma un Universo de Grothendieck válido en MK⁺.
    Esto significa que es un conjunto transitivo cerrado bajo pares, uniones, partes e infinito. -/
theorem isGrothendieckUniverse_dybjerUniverse : IsGrothendieckUniverse DybjerUniverse.{u} := by
  refine ⟨isSet_dybjerUniverse, isTransitive_dybjerUniverse, ?_, ?_, ?_, ?_⟩
  · exact isGrothendieck_pair_dybjerUniverse
  · exact isGrothendieck_union_dybjerUniverse
  · exact isGrothendieck_powerset_dybjerUniverse
  · exact isGrothendieck_infinity_dybjerUniverse

end MKplusCAC
