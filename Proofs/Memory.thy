theory Memory
imports
  "../AutoCorres/Impl"
  "../lib/ExtraLemmas"
begin

context sable_isa
begin
abbreviation "HEAP_SIZE \<equiv> 1024" (* in mem_nodes *)
type_synonym HEAP_SIZE_t = 1024
abbreviation "heap \<equiv> Ptr (symbol_table ''heap'') :: (mem_node_C[HEAP_SIZE_t]) ptr"
abbreviation "heap_ptr \<equiv> Ptr (symbol_table ''heap'') :: mem_node_C ptr"
end

locale sable_m = sable_isa +
assumes heap_guard: "c_guard heap"
begin

lemma heap_ptr_guard: "c_guard heap_ptr"
proof -
  have "c_guard (((ptr_coerce heap) :: mem_node_C ptr) +\<^sub>p 0)"
    apply (rule c_guard_array)
    using heap_guard apply auto
    done
  thus ?thesis by simp
qed

lemma heap_guard_set_array_addrs: "\<forall>p \<in> set (array_addrs heap_ptr HEAP_SIZE). c_guard p"
proof (auto simp add: set_array_addrs)
  fix k :: nat
  assume "k < 1024"
  have "c_guard ((ptr_coerce heap :: mem_node_C ptr) +\<^sub>p int k)"
    apply (rule c_guard_array)
    using heap_guard and `k < 1024` apply auto
    done
  thus "c_guard (heap_ptr +\<^sub>p int k)" by auto
qed

definition
  liftC :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
where
  "liftC st P \<equiv> \<lambda>s. \<forall>g. s = st g \<longrightarrow> P g"

lemma hoare_liftC_wp[wp]:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r s. \<forall>t. st s = t \<longrightarrow> Q r t\<rbrace> \<Longrightarrow> \<lbrace>liftC st P\<rbrace> exec_concrete st m \<lbrace>Q\<rbrace>"
unfolding liftC_def
apply wp
unfolding valid_def
apply auto
done

lemma hoare_liftC[intro]:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r s. \<forall>t. st s = t \<longrightarrow> liftC st (Q r) t\<rbrace> \<Longrightarrow>
   \<lbrace>liftC st P\<rbrace> exec_concrete st m \<lbrace>\<lambda>r s. liftC st (Q r) s\<rbrace>"
by wp

definition
  heap_invs :: "globals \<Rightarrow> bool"
where
  "heap_invs s \<equiv> node_' s \<in> set (array_addrs heap_ptr HEAP_SIZE) \<and>
    (let node_size = mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) in
    node_size < HEAP_SIZE \<and> node_' s +\<^sub>p uint (node_size) = heap_ptr +\<^sub>p (HEAP_SIZE - 1) \<and>
    (\<forall>p \<in> {ptr_val (node_' s +\<^sub>p 1)..+unat node_size * size_of TYPE(mem_node_C)}.
      snd (hrs_htd (t_hrs_' s) p) = Map.empty))"

definition
  init_heap_P :: "globals \<Rightarrow> bool"
where
  "init_heap_P s \<equiv> node_' s = NULL \<and>
    (\<forall>p \<in> {ptr_val heap_ptr..+HEAP_SIZE * size_of TYPE(mem_node_C)}.
     snd (hrs_htd (t_hrs_' s) p) = Map.empty)"

lemma init_heap'_invs:
  "\<lbrace>\<lambda>s. (init_heap_P s)\<rbrace> init_heap' \<lbrace>\<lambda>_ s. (heap_invs s)\<rbrace>!"
unfolding init_heap'_def heap_invs_def fail'_def
  FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def init_heap_P_def
apply wp
using heap_guard apply (auto simp add: ptr_add_def ptr_sub_def h_val_id intvl_self)
defer
using heap_ptr_guard apply simp
proof -
  fix s :: globals and q :: "32 word"
  assume empty: "\<forall>p \<in> {symbol_table ''heap''..+8192}. snd (hrs_htd (t_hrs_' s) p) = Map.empty"
     and q: "q \<in> {symbol_table ''heap'' + 8..+8184}"
  from q have "q \<in> {symbol_table ''heap''..+8192}"
    by (rule_tac y=8 in intvl_plus_sub_offset, auto)
  with empty show "snd (hrs_htd (t_hrs_' s) q) = Map.empty" by blast
qed

lemma size_of_le_n[dest]: "size_of TYPE('a :: wf_type) \<le> unat (n :: ('b :: len) word) \<Longrightarrow> 0 < n"
proof -
  fix n :: "'b word"
  assume "size_of TYPE('a) \<le> unat n"
  moreover have "0 < size_of TYPE('a)" using sz_nzero by auto
  ultimately have "0 < unat n" by linarith 
  thus "0 < n" using word_of_nat_less by force
qed

(*declare [[show_types]]
declare [[show_consts]]
declare [[show_sorts]]*)

lemma alloc'_invs: "align_of TYPE('a :: mem_type) dvd align_of TYPE(mem_node_C)
  \<Longrightarrow> size_of TYPE('a) \<le> unat n
  \<Longrightarrow> \<lbrace>\<lambda>s. heap_invs s\<rbrace> alloc' n
      \<lbrace>\<lambda>r s. heap_invs s \<and> (let ptr = (ptr_coerce r) :: 'a ptr in
        ptr_val r \<noteq> 0 \<longrightarrow> heap_ptr_valid (ptr_retyp ptr (hrs_htd (t_hrs_' s))) ptr)\<rbrace>!"
unfolding alloc'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def Let_def
apply (simp add: h_val_field_from_bytes)
apply wp
apply (simp add: h_val_id not_le word_gt_a_gt_0)
apply (insert size_of_le_n [where n=n and 'a='a])
apply simp
apply (rule conjI)
apply (clarsimp simp add: heap_guard_set_array_addrs)
proof clarify
  fix s :: globals
  let ?size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) :: 32 word"
  let ?blocks = "(n >> 3) + 1 :: 32 word"
  assume node: "node_' s \<in> set (array_addrs heap_ptr HEAP_SIZE)"
     and node_size: "node_' s +\<^sub>p uint ?size = heap_ptr +\<^sub>p 1023"
     and size: "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) < HEAP_SIZE"
     and align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)"
     and n: "size_of TYPE('a) \<le> unat n"
     and blocks_size: "(n >> 3) + 1 < ?size"
     and empty: "\<forall>p\<in>{ptr_val (node_' s +\<^sub>p 1)..+unat ?size * 8}. snd (hrs_htd (t_hrs_' s) p) = Map.empty"
  from blocks_size have blocksp1_size: "?blocks + 1 \<le> ?size" by unat_arith
  from blocks_size and size have blocks_bound: "?blocks < HEAP_SIZE - 1" by unat_arith
  from node obtain i where i: "node_' s = heap_ptr +\<^sub>p (int i)" and "i < HEAP_SIZE"
    using array_addrs_ptr_ex by blast
  with node_size have heap_i: "heap_ptr +\<^sub>p (int i + uint ?size) = heap_ptr +\<^sub>p 1023"
    unfolding ptr_add_def by simp
  moreover have "(heap_ptr +\<^sub>p (int i + uint ?size) = heap_ptr +\<^sub>p 1023)
                  = (int i + uint ?size = 1023)"
    apply (rule ptr_arith_index) using size and `i < HEAP_SIZE`
    apply auto
    apply uint_arith
    done
  ultimately have i_size: "int i + uint ?size = 1023" by auto
  from `i < 1024` have "int i < 1024" by auto
  moreover from size have "uint ?size < 1024" by uint_arith
  ultimately have i_blocks: "int i + uint (?blocks + 1) < HEAP_SIZE" using i_size and blocksp1_size
    by (simp, uint_arith)
  hence "heap_ptr +\<^sub>p (int i + uint (?blocks + 1)) \<in> set (array_addrs heap_ptr HEAP_SIZE)" by auto
  with i have new_node_in_heap: "node_' s +\<^sub>p uint (?blocks + 1) \<in> set (array_addrs heap_ptr HEAP_SIZE)"
    unfolding ptr_add_def by (simp add: semiring_normalization_rules(25))
  from i_blocks have "i + unat (?blocks + 1) < HEAP_SIZE"
    by (simp add: uint_nat)
  moreover
  { from blocks_bound have "unat (n >> 3) + unat (2 :: 32 word) < 2 ^ len_of TYPE(32)"
      by (simp add: shiftr3_is_div_8, unat_arith)
    hence "unat ((n >> 3) + 2) = unat (n >> 3) + unat (2 :: 32 word)"
      using unat_add_lem by blast }
  ultimately have i_blocks_u: "i + unat (n >> 3) + unat (2 :: 32 word) < HEAP_SIZE"
    by (simp, unat_arith)
  with n and `i < HEAP_SIZE` have n_bound: "n < HEAP_SIZE * 8"
    by (simp add: shiftr3_is_div_8, unat_arith)
  show "node_' s +\<^sub>p uint (2 + (n >> 3)) \<in> set (array_addrs heap_ptr HEAP_SIZE) \<and>
        ?size - (2 + (n >> 3)) < HEAP_SIZE \<and>
        node_' s +\<^sub>p uint (2 + (n >> 3)) +\<^sub>p uint (?size - (2 + (n >> 3))) = heap_ptr +\<^sub>p 1023 \<and>
        (\<forall>p \<in> {ptr_val (node_' s +\<^sub>p uint (2 + (n >> 3)) +\<^sub>p 1)..+unat (?size - (2 + (n >> 3))) * 8}.
             snd (hrs_htd (t_hrs_' s) p) = Map.empty) \<and>
        (ptr_val (node_' s +\<^sub>p 1) \<noteq> 0 \<longrightarrow>
          heap_ptr_valid (ptr_retyp (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr) (hrs_htd (t_hrs_' s)))
           (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)) \<and>
        c_guard (node_' s +\<^sub>p uint (2 + (n >> 3))) \<and> c_guard (node_' s)"
  proof safe
    show "c_guard (node_' s)" using heap_guard_set_array_addrs and node ..
  next
    show "node_' s +\<^sub>p uint (2 + (n >> 3) :: 32 word) \<in> set (array_addrs heap_ptr HEAP_SIZE)"
      using new_node_in_heap by simp
  next
    show "node_' s +\<^sub>p uint (2 + (n >> 3)) +\<^sub>p uint (?size - (2 + (n >> 3))) = heap_ptr +\<^sub>p 1023"
      using node_size unfolding ptr_add_def by unat_arith
  next
    show "?size - (2 + (n >> 3)) < 0x400" using blocksp1_size and size
      by (auto, unat_arith)
  next
    let ?ptrc = "ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr"
    assume "ptr_val (node_' s +\<^sub>p 1) \<noteq> 0"
    from node and heap_guard_set_array_addrs have "c_guard (node_' s)" by auto
    show "heap_ptr_valid (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) ?ptrc"
    unfolding heap_ptr_valid_def c_guard_def
    proof safe
      show "valid_simple_footprint (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) (ptr_val ?ptrc)
            (typ_uinfo_t TYPE('a))"
      apply (rule TypHeapSimple.valid_simple_footprint_ptr_retyp) defer
      apply (simp, metis Suc_le_eq mem_type_simps(3) size_of_def)
      apply (simp add: size_of_tag)
      proof clarify
        fix k :: nat
        assume "k < size_td (typ_uinfo_t TYPE('a))"
        with n have "k < unat n" by (simp add: size_of_def)
        with blocks_size have "k < unat ?size * 8" by (simp add: shiftr3_is_div_8, unat_arith)
        with empty show "snd (hrs_htd (t_hrs_' s) (ptr_val ?ptrc + of_nat k)) = Map.empty"
          using intvlI by (simp, blast)
      qed
    next
      from `c_guard (node_' s)` have "ptr_aligned (node_' s +\<^sub>p 1)"
        unfolding c_guard_def by (simp add: CTypes.ptr_aligned_plus)
      moreover have "ptr_val (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr) = ptr_val (node_' s +\<^sub>p 1)"
        by auto
      ultimately show "ptr_aligned (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)"
        unfolding ptr_aligned_def using align dvd_trans by auto
    next
      from heap_guard have "0 \<notin> {ptr_val heap_ptr..+(HEAP_SIZE * size_of TYPE(mem_node_C))}"
        (is "_ \<notin> ?heap") unfolding c_guard_def c_null_guard_def by auto
      moreover have "{ptr_val (node_' s +\<^sub>p 1)..+size_of TYPE('a)} \<subseteq> ?heap" (is "?val \<subseteq> _")
      proof
        fix x
        assume "x \<in> {ptr_val (node_' s +\<^sub>p 1)..+size_of TYPE('a)}" (is "_ \<in> {?start..+?sz}")
        then obtain k where "x = ?start + of_nat k" and "k < ?sz"
          by (blast dest: intvlD)
        with i have x: "x = ptr_val (heap_ptr +\<^sub>p int i +\<^sub>p 1) + of_nat k" by auto
        from `k < ?sz` and n have "k < unat n" by auto
        hence k: "k + 1 < unat ?blocks * 8" by (simp add: shiftr3_is_div_8, unat_arith)
        from i_blocks_u have "8 * i + unat n < 8176" by (simp add: shiftr3_is_div_8, unat_arith)
        show "x \<in> {ptr_val heap_ptr..+1024 * size_of TYPE(mem_node_C)}"
        apply (rule intvl_inter_le [where k=0 and ka="(i + 1) * size_of TYPE(mem_node_C) + k"])
        apply auto
        apply (subst x)
        apply (simp add: ptr_add_def)
        using i_blocks_u and k apply (simp add: shiftr3_is_div_8)
        apply unat_arith
        done
      qed
      with heap_guard show "c_null_guard (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)"
        unfolding c_guard_def c_null_guard_def by auto
    qed
  next
    show "c_guard (node_' s +\<^sub>p uint (2 + (n >> 3)))"
      using new_node_in_heap and heap_guard_set_array_addrs by auto
  next
    fix p :: "32 word"
    assume p: "p \<in> {ptr_val (node_' s +\<^sub>p uint (2 + (n >> 3)) +\<^sub>p 1)..+unat (?size - (2 + (n >> 3))) * 8}"
    moreover
    { have "unat (?size - (2 + (n >> 3))) = unat ?size - unat (2 + (n >> 3))"
        using size and blocks_size by unat_arith
      hence "unat (?size - (2 + (n >> 3))) * 8 = unat ?size * 8 - unat (2 + (n >> 3)) * 8" by simp }
    moreover
    { have "unat (2 + (n >> 3)) * unat (8 :: 32 word) < 2 ^ len_of TYPE(32)"
        using n_bound by (simp add: shiftr3_is_div_8, unat_arith)
      hence "unat ((2 + (n >> 3)) * 8) = unat (2 + (n >> 3)) * unat (8 :: 32 word)"
        by (subst(asm) unat_mult_lem)
      hence "unat (2 + (n >> 3)) * 8 = unat ((2 + (n >> 3)) * 8)" by auto }
    ultimately have "p \<in> {ptr_val (node_' s +\<^sub>p 1) + ((2 + (n >> 3)) * 8)..+
                            unat ?size * 8 - unat ((2 + (n >> 3)) * 8)}"
      unfolding ptr_add_def by simp
    hence "p \<in> {ptr_val (node_' s +\<^sub>p 1)..+unat ?size * 8}"
      by (drule_tac y="(2 + (n >> 3)) * 8" in intvl_plus_sub_offset)
    with empty show "snd (hrs_htd (t_hrs_' s) p) = Map.empty" by blast
  qed
qed

lemma alloc_w32_safe: "\<lbrace>\<lambda>s. (liftC heap_invs) s\<rbrace> exec_concrete lift_global_heap (alloc' 4)
      \<lbrace>\<lambda>r s. (liftC heap_invs) s \<and> (ptr_val r \<noteq> 0 \<longrightarrow> is_valid_w32 s ((ptr_coerce r) :: (32 word) ptr))\<rbrace>!"
unfolding liftC_def apply wp
unfolding validNF_def valid_def
apply auto
proof -
  fix s a b
  assume "\<forall>g. lift_global_heap s = lift_global_heap g \<longrightarrow> heap_invs g"
     and "\<forall>g. lift_global_heap b = lift_global_heap g \<longrightarrow> heap_invs g"
  hence "heap_invs s" and "heap_invs b" by auto
oops*)


end

end