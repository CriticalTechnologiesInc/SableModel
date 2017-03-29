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
  heap_invs :: "globals \<Rightarrow> bool"
where
  "heap_invs s \<equiv> node_' s \<in> set (array_addrs heap_ptr HEAP_SIZE) \<and>
    mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) < HEAP_SIZE \<and>
    node_' s +\<^sub>p uint (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s))) = heap_ptr +\<^sub>p (HEAP_SIZE - 1)"

lemma init_heap'_invs: "\<lbrace>\<lambda>s. node_' s = NULL\<rbrace> init_heap' \<lbrace>\<lambda>_ s. (heap_invs s)\<rbrace>!"
unfolding init_heap'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply wp
using heap_guard apply (auto simp add: ptr_sub_def h_val_id intvl_self)
using heap_ptr_guard apply simp
done

lemma alloc'_invs: "align_of TYPE('a :: c_type) dvd align_of TYPE(mem_node_C) \<Longrightarrow> n > 0
  \<Longrightarrow> \<lbrace>\<lambda>s. heap_invs s\<rbrace> alloc' n
      \<lbrace>\<lambda>r s. heap_invs s \<and> (ptr_val r \<noteq> 0 \<longrightarrow> c_guard ((ptr_coerce r) :: 'a ptr))\<rbrace>!"
unfolding alloc'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply (simp add: h_val_field_from_bytes)
apply wp
apply (simp add: h_val_id not_le)
proof clarify
  fix s :: globals
  let ?size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) :: 32 word"
  let ?blocks = "(n >> 3) + 1 :: 32 word"
  assume node: "node_' s \<in> set (array_addrs heap_ptr HEAP_SIZE)"
     and node_size: "node_' s +\<^sub>p uint ?size = heap_ptr +\<^sub>p 1023"
     and size: "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) < HEAP_SIZE"
     and align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)" and "0 < n"
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
  show "(?size \<le> (n >> 3) + 1 \<longrightarrow> c_guard (node_' s)) \<and>
        ((n >> 3) + 1 < ?size \<longrightarrow> node_' s +\<^sub>p uint (2 + (n >> 3)) \<in> set (array_addrs heap_ptr HEAP_SIZE) \<and>
        ?size - (2 + (n >> 3)) < HEAP_SIZE \<and>
        node_' s +\<^sub>p uint (2 + (n >> 3)) +\<^sub>p uint (?size - (2 + (n >> 3))) = heap_ptr +\<^sub>p 1023 \<and>
        (ptr_val (node_' s +\<^sub>p 1) \<noteq> 0 \<longrightarrow> c_guard (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)) \<and>
        c_guard (node_' s +\<^sub>p uint (2 + (n >> 3))) \<and> c_guard (node_' s))"
  proof safe
    show "c_guard (node_' s)" using heap_guard_set_array_addrs and node ..
  next
    assume "?blocks < ?size"
    hence "?blocks + 1 \<le> ?size" by unat_arith
    hence "uint (?blocks + 1) \<le> uint ?size" by uint_arith
    moreover from `i < 1024` have "int i < 1024" by auto
    moreover from size have "uint ?size < 1024" by uint_arith
    ultimately have "int i + uint (?blocks + 1) < HEAP_SIZE" using i_size by auto
    hence "heap_ptr +\<^sub>p (int i + uint (?blocks + 1)) \<in> set (array_addrs heap_ptr HEAP_SIZE)" by auto
    with i show "node_' s +\<^sub>p uint (2 + (n >> 3) :: 32 word) \<in> set (array_addrs heap_ptr HEAP_SIZE)"
      unfolding ptr_add_def by (simp add: semiring_normalization_rules(25))
  next
    show "node_' s +\<^sub>p uint (2 + (n >> 3)) +\<^sub>p uint (?size - (2 + (n >> 3))) = heap_ptr +\<^sub>p 1023"
      using node_size unfolding ptr_add_def by unat_arith
  next
    assume "ptr_val (node_' s +\<^sub>p 1) \<noteq> 0"
    moreover from node and heap_guard_set_array_addrs have "c_guard (node_' s)" by auto
    ultimately show "c_guard (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)" using align
      unfolding c_guard_def c_null_guard_def ptr_aligned_def ptr_add_def apply auto
      apply unat_arith sorry
  next
    assume "?blocks < ?size"
    hence "?blocks + 1 \<le> ?size" by unat_arith
    thus "?size - (2 + (n >> 3)) < 0x400" using size
      apply auto
      apply unat_arith
      done
  next
    assume "(n >> 3) + 1 < ?size"
    hence "(n >> 3) + 2 \<le> ?size" by unat_arith
    with `((n >> 3) + 1 < size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s))) \<Longrightarrow>
      node_' s +\<^sub>p uint (2 + (n >> 3)) \<in> set (array_addrs heap_ptr 1024)`
    with heap_guard and size show "c_guard (node_' s +\<^sub>p uint (2 + (n >> 3)))" sorry
  next
    from node and heap_guard_set_array_addrs show "c_guard (node_' s)" by auto
qed

(*apply (auto simp add: h_val_field_from_bytes shiftr2_is_div_4 h_val_id)
apply (simp add: ptr_add_def ptr_sub_def)
proof -
  fix s :: globals
  let ?node = "ptr_val (node_' s)" and ?heap = "symbol_table ''heap''"
  let ?node_size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s))"
  let ?blocks = "(scast (ucast n div 4 :: 32 signed word) + 1) :: 16 word"
  assume a1: "uint (scast (ucast (?node - ?heap) div 4)) + uint ?node_size = 2047"
     and a2: "\<not> uint ?node_size \<le> uint ?blocks"
  from a2 have "uint ?blocks < uint ?node_size" by auto
  have "uint (?blocks) * 4 + 4 = uint (?blocks + 1) * 4" apply unat_arith
  have "uint ((scast ((ucast (?node + (of_int (uint (?blocks)) * 4 + 4) - ?heap) :: 32 signed word) div 4)) :: 16 word)
    = uint ((scast ((ucast (?node - ?heap) :: 32 signed word) div 4)) :: 16 word) + uint (?blocks) + 1"
    
  have "uint ((scast ((ucast (?node + (of_int (uint (?blocks)) * 4 + 4) - ?heap) :: 32 signed word) div 4)) :: 16 word) +
         uint (?node_size - (?blocks + 1)) = 2047" sorry
  thus "uint ((scast ((ucast (?node + (of_int (uint (?blocks)) * 4 + 4) - ?heap) :: 32 signed word) div 4)) :: 16 word) +
         uint (?node_size - (2 + (scast ((ucast n div 4) :: 32 signed word)) :: 16 word)) = 2047" by simp*)


lemma alloc'_hoare: "n > 0 \<Longrightarrow> \<lbrace>heap_invs\<rbrace> alloc' n
  \<lbrace>\<lambda>r s. (heap_invs s) \<and> (ptr_val r \<noteq> 0 \<longrightarrow> c_guard r)\<rbrace>"
unfolding alloc'_def
apply simp
apply (rule hoare_seq_ext [where B="\<lambda>_ s. alloc'_invs s"])
prefer 2
apply wp_once_trace
apply (rule hoare_seq_ext [where B="\<lambda>_ s. alloc'_invs s"])
apply wp_once_trace
apply auto
apply (rule hoare_seq_ext)
apply wp_once_trace

end

end